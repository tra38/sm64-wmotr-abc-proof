/* Native source-mechanics probe, NOT the selected Clight program or a
 * controller witness. The selected movement/AI/collision functions below are
 * extracted unchanged. This driver supplies normal western-Goomba fields,
 * a declared Mario pose in the bucket, static terrain and no other actors.
 * Sound has no output here. Object scheduling, dynamic owners, attacks,
 * live elevator collision and other actors' RNG calls are not simulated.
 * The stock-search mode can make Mario's height follow the extracted elevator
 * loop's trace, conditional on carriage. Optional distance activation uses
 * the end-of-update test, with pre-movement distance.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "sm64.h"
#include "engine/math_util.h"
#include "engine/surface_collision.h"
#include "engine/surface_load.h"
#include "game/debug.h"
#include "game/object_list_processor.h"
#include "trig_tables.inc.c"

#define o gCurrentObject
struct Object *gCurrentObject, *gMarioObject;
struct MarioState *gMarioState;
struct SurfaceNode *sSurfaceNodePool;
struct Surface *sSurfacePool;
s16 sSurfacePoolSize;
s32 gSurfaceNodesAllocated, gSurfacesAllocated;
SpatialPartitionCell gStaticSurfacePartition[NUM_CELLS][NUM_CELLS];
SpatialPartitionCell gDynamicSurfacePartition[NUM_CELLS][NUM_CELLS];
s16 gCheckingSurfaceCollisionsForCamera;
s16 gFindFloorIncludeSurfaceIntangible;
TerrainData *gEnvironmentRegions;
u16 gRandomSeed16;
struct NumTimesCalled gNumCalls;
s32 gNumFindFloorMisses;

/* These are presentation calls only in the selected walk/jump bodies. */
void cur_obj_play_sound_2(s32 sound) { (void)sound; }
void cur_obj_play_sound_at_anim_range(s8 a, s8 b, u32 sound) {
    (void)a; (void)b; (void)sound;
}
#define random_u16 stock_random_u16
#include "source_rng.inc"
#undef random_u16
static int grant_rng;
static u16 grant_values[3];
static unsigned grant_count, grant_at;
static u16 grant_default,grant_kind[2],grant_sign[2],grant_duration[100];
u16 random_u16(void) {
    if(!grant_rng) return stock_random_u16();
    return grant_at<grant_count ? grant_values[grant_at++] : grant_default;
}
static void verify_granted_outcomes(void) {
    unsigned char visited[65536]={0};
    unsigned count=0;
    int found_default=0,kind[2]={0},sign[2]={0},duration[100]={0};
    gRandomSeed16=0;
    while(!visited[gRandomSeed16]) {
        visited[gRandomSeed16]=1;count++;
        u16 r=stock_random_u16();
        unsigned k=(r&3)!=0,s=r>=0x7FFF,n=(100u*r)/65536u;
        if(!kind[k]) {grant_kind[k]=r;kind[k]=1;}
        if(!sign[s]) {grant_sign[s]=r;sign[s]=1;}
        if(!duration[n]) {grant_duration[n]=r;duration[n]=1;}
        if(!found_default && (50u*r)/65536u==0) {grant_default=r;found_default=1;}
    }
    assert(found_default && kind[0] && kind[1] && sign[0] && sign[1]);
    for(unsigned n=0;n<100;n++) assert(duration[n]);
    printf("GRANTED_OUTCOMES,visitedRngStates=%u,walkDurations=100,turnSigns=2,jumpSigns=2\n",count);
}
#include "source_functions.inc"
#include "source_mesh.inc"
#include "source_roster.inc"

static struct Surface surfaces[2300];
static struct SurfaceNode nodes[7000];
static struct Object goomba, mario;
static struct MarioState mario_state;
static int distance_activation;
static float start_x=-3638, start_y=0, start_z=1928;
static float mario_x=-410, mario_y=128, mario_z=-154;
static int follow_elevator, stock_mode;
static unsigned scene_frame, search_horizon=100000;
static float elevator_y[901];
static float last_wall_dx,last_wall_dz;

static void load_mesh(void) {
    TerrainData *p=source_mesh+2, *v=p;
    RoomData *rooms=NULL;
    p+=3*source_mesh[1];
    sSurfacePool=surfaces; sSurfaceNodePool=nodes; sSurfacePoolSize=2300;
    while (*p < 64 || *p >= 101) {
        int type=*p++;
        load_static_surfaces(&p,v,type,&rooms);
    }
    assert(*p==65 && gSurfacesAllocated==1558 && gSurfaceNodesAllocated<7000);
}

static void start(unsigned seed) {
    memset(&goomba,0,sizeof(goomba)); memset(&mario,0,sizeof(mario));
    gCurrentObject=&goomba; gMarioObject=&mario; gMarioState=&mario_state;
    mario.oPosX=mario_x; mario.oPosY=mario_y; mario.oPosZ=mario_z;
    goomba.oPosX=goomba.oHomeX=start_x;
    goomba.oPosY=goomba.oHomeY=start_y;
    goomba.oPosZ=goomba.oHomeZ=start_z;
    goomba.activeFlags=ACTIVE_FLAG_ACTIVE;
    goomba.oRoom=-1;
    goomba.oGoombaScale=1.5f; goomba.oGravity=-4;
    goomba.oBounciness=-0.5f; goomba.oDragStrength=10;
    goomba.oWallHitboxRadius=40;
    goomba.hitboxRadius=108; goomba.hitboxHeight=75;
    goomba.parentObj=&goomba;
    gRandomSeed16=seed;
    memset(&gNumCalls,0,sizeof(gNumCalls)); gNumFindFloorMisses=0;
}

static float prepare(void) {
    if(follow_elevator) mario.oPosY=elevator_y[scene_frame<901 ? scene_frame : 900];
    float dx=o->oPosX-mario.oPosX, dy=o->oPosY-mario.oPosY;
    float dz=o->oPosZ-mario.oPosZ;
    float distance=sqrtf(dx*dx+dy*dy+dz*dz);
    o->oDistanceToMario=distance;
    o->oAngleToMario=atan2s(-dz,-dx);
    obj_update_blinking(&o->oGoombaBlinkTimer,30,50,5);
    float before_x=o->oPosX,before_z=o->oPosZ;
    cur_obj_update_floor_and_walls();
    last_wall_dx=o->oPosX-before_x;last_wall_dz=o->oPosZ-before_z;
    return distance;
}
static void act_move(float distance) {
    switch(o->oAction) {
      case GOOMBA_ACT_WALK: goomba_act_walk(); break;
      case GOOMBA_ACT_JUMP: goomba_act_jump(); break;
      default: abort();
    }
    cur_obj_move_standard(-78);
    if(distance_activation) {
        if(distance>4000) o->activeFlags|=ACTIVE_FLAG_FAR_AWAY;
        else o->activeFlags&=~ACTIVE_FLAG_FAR_AWAY;
    }
}
static void update(void) { float distance=prepare(); act_move(distance); }

/* Local wall fixtures are explicitly granted poses, not reached states. */
static void check_wall(void) {
    unsigned cases=0,floor_cases=0;
    for(int y=0;y<=132;y++) for(int x=-3152;x<=-3113;x++) {
        struct Surface *floor=NULL;
        assert(find_floor(x,y,1928,&floor)==0 && floor!=NULL);
        floor_cases++;
    }
    for(int y=0;y<=62;y++) for(int x=-3151;x<=-3113;x++) {
        start(0); o->oPosX=x; o->oPosY=y; o->oPosZ=1928;
        o->oMoveAngleYaw=0x4000;
        assert(cur_obj_resolve_wall_collisions());
        assert(o->oPosX==-3152 && o->oPosY==y && o->oPosZ==1928);
        cases++;
    }
    start(0); o->oPosX=-3130; o->oPosY=63; o->oPosZ=1928;
    o->oMoveAngleYaw=0x4000;
    assert(!cur_obj_resolve_wall_collisions() && o->oPosX==-3130);
    printf("WALL_FIXTURES,lowCases=%u,flatFloorCases=%u,pushedX=-3152,aboveWallY=63\n",cases,floor_cases);
}

/* Finite closure of the isolated, fully updating, flat-floor vertical case.
 * Grant MORE jump choices than RNG: any WALK update may jump immediately,
 * even when the real walk timer would forbid it. WALK may move at speed 2.
 * There are no other actors or changing supports. The pause variant grants
 * arbitrary partial/full updates and still cannot cross the straight wall.
 * We use the extracted jump and vertical movement routines, not a height
 * formula. This is still a native diagnostic, not a Clight refinement proof.
 */
struct VerticalState { u32 y, vy, flags, action, forward, clearance; };
static struct VerticalState vertical[32768];
static unsigned vertical_parent[32768], vertical_choice[32768];
static unsigned clearance;
static u32 bits(float x) { u32 b; memcpy(&b,&x,4); return b; }
static float unbits(u32 b) { float x; memcpy(&x,&b,4); return x; }
static struct VerticalState vertical_state(void) {
    struct VerticalState v={bits(o->oPosY),bits(o->oVelY),o->oMoveFlags,
        o->oAction,bits(o->oForwardVel),clearance};
    return v;
}
static int vertical_closure(int pauses) {
    unsigned count=1, edges=0, maxMovingAt=0,maxClearance=0;
    float maxY=0, maxMovingY=0;
    start(0); o->oFloorHeight=-0.0f; vertical[0]=vertical_state();
    for(unsigned i=0;i<count;i++) {
        for(unsigned partial=0;partial<=(unsigned)pauses;partial++)
        for(unsigned round_y=0;round_y<=1;round_y++)
        for(unsigned jump=0;jump<=(vertical[i].action==GOOMBA_ACT_WALK);jump++) {
            start(0); o->oFloorHeight=-0.0f;
            o->oPosY=unbits(vertical[i].y); o->oVelY=unbits(vertical[i].vy);
            clearance=vertical[i].clearance;
            o->oMoveFlags=vertical[i].flags; o->oAction=vertical[i].action;
            o->oForwardVel=unbits(vertical[i].forward);
            /* Every low full wall pass restores the 40-unit clearance. A
             * partial update cannot move horizontally. Allow either integer
             * wall correction or no correction of Y at every low pass. */
            if(!partial && o->oPosY<63) {
                clearance=0;
                if(round_y) o->oPosY=(s16)o->oPosY;
            } else if(round_y) continue;
            if(o->oPosY>o->oFloorHeight) o->oMoveFlags|=OBJ_MOVE_IN_AIR;
            if(o->oAction==GOOMBA_ACT_WALK) {
                if(jump) goomba_begin_jump(); else o->oForwardVel=2;
            } else goomba_act_jump();
            /* X/Z movement runs at this point, before the vertical update. */
            if(!partial && o->oForwardVel>0 && o->oPosY>maxMovingY) {
                maxMovingY=o->oPosY; maxMovingAt=i;
            }
            if(!partial) {
                if(o->oForwardVel>0) clearance+=2;
                cur_obj_move_y(-4,-0.5f,0);
            }
            if(clearance>maxClearance) maxClearance=clearance;
            if(o->oPosY>maxY) maxY=o->oPosY;
            struct VerticalState v=vertical_state();
            unsigned j=0;
            for(;j<count;j++) if(!memcmp(&v,&vertical[j],sizeof(v))) break;
            if(j==count) {
                assert(count<32768);
                vertical[count]=v; vertical_parent[count]=i;
                vertical_choice[count]=jump+2*partial+4*round_y; count++;
            }
            edges++;
        }
    }
    printf("FLAT_VERTICAL_CLOSURE,pauses=%d,states=%u,edges=%u,maxY=%.9g,maxMovingQueryY=%.9g,maxClearanceAdvance=%u\n",
        pauses,count,edges,maxY,maxMovingY,maxClearance);
    assert(count==(pauses ? 845u : 215u));
    assert(edges==(pauses ? 2696u : 487u));
    assert(maxY==(pauses ? 132.0f : 77.0f));
    assert(maxMovingY==(pauses ? 66.0f : 11.0f));
    assert(maxClearance==(pauses ? 8u : 2u) && maxClearance<40);
    printf("MAX_MOVING_CHAIN_REVERSED");
    for(unsigned i=maxMovingAt;i;i=vertical_parent[i])
        printf(",[%u:%g:%g:%u:%u]",i,unbits(vertical[i].y),unbits(vertical[i].vy),
            vertical[i].action,vertical_choice[i]);
    printf("\n");
    return 0;
}

#include "elevator_analysis.inc.c"
#include "search.inc.c"

int main(int argc, char **argv) {
    if(argc>1 && !strcmp(argv[1],"--scene")) return report_scene(argc>2 ? argv[2] : NULL);
    if(argc>1 && !strcmp(argv[1],"--stock-choices")) {stock_mode=1;verify_granted_outcomes();return choice_search(argc,argv);}
    if(argc>1 && !strcmp(argv[1],"--choices")) {verify_granted_outcomes();return choice_search(argc,argv);}
    if(argc>1 && !strcmp(argv[1],"--replay-west")) {verify_granted_outcomes();return replay_west(argc>2?argv[2]:NULL);}
    if(argc>1 && !strcmp(argv[1],"--vertical")) return vertical_closure(0);
    if(argc>1 && !strcmp(argv[1],"--vertical-pauses")) return vertical_closure(1);
    unsigned seeds=argc>1 ? strtoul(argv[1],NULL,10) : 1;
    unsigned frames=argc>2 ? strtoul(argv[2],NULL,10) : 2000;
    distance_activation=argc>3 ? atoi(argv[3]) : 1;
    unsigned first=argc>4 ? strtoul(argv[4],NULL,10) : 0;
    FILE *trace=argc>5 ? fopen(argv[5],"w") : NULL;
    if(argc>5) assert(trace && seeds==1);
    float bestX=-10000, maxY=-10000, maxHome=0;
    unsigned bestSeed=0, bestFrame=0, rim=0, pit=0;
    assert(seeds && first+seeds<=65536 && frames && frames<=100000);
    load_mesh();
    check_wall();
    if(trace) fprintf(trace,"frame,rng_before,rng_after,x,y,z,vy,forward,yaw,target,action,flags,floor,walk_timer,turning,active\n");
    for(unsigned seed=first;seed<first+seeds;seed++) {
        start(seed);
        for(unsigned frame=0;frame<frames;frame++) {
            unsigned rng=gRandomSeed16;
            update();
            if(trace) fprintf(trace,"%u,%u,%u,%.9g,%.9g,%.9g,%.9g,%.9g,%d,%d,%d,%u,%.9g,%d,%d,%d\n",
                frame,rng,gRandomSeed16,o->oPosX,o->oPosY,o->oPosZ,o->oVelY,
                o->oForwardVel,(s16)o->oMoveAngleYaw,(s16)o->oGoombaTargetYaw,
                o->oAction,o->oMoveFlags,o->oFloorHeight,o->oGoombaWalkTimer,
                o->oGoombaTurningAwayFromWall,o->activeFlags);
            float dx=o->oPosX-o->oHomeX, dz=o->oPosZ-o->oHomeZ;
            float home=sqrtf(dx*dx+o->oPosY*o->oPosY+dz*dz);
            if(o->oPosX>bestX) {bestX=o->oPosX;bestSeed=seed;bestFrame=frame;}
            if(o->oPosY>maxY) maxY=o->oPosY;
            if(home>maxHome) maxHome=home;
            if(o->oFloorHeight>=72 && o->oPosX>=-3112 && o->oPosX<=-3071) rim++;
            if(o->oPosX>-3071 && o->oFloorHeight<0) pit++;
            assert(o->oGoombaRelativeSpeed<=2.0f && o->oForwardVel<=2.001f);
            assert(isfinite(o->oPosX) && isfinite(o->oPosY) && isfinite(o->oPosZ));
        }
    }
    if(trace) fclose(trace);
    printf("WEST_RNG,seeds=%u,frames=%u,distanceActivation=%d,bestX=%.9g,bestSeed=%u,bestFrame=%u,"
           "maxY=%.9g,maxHome=%.9g,rimSamples=%u,pitSamples=%u\n",
           seeds,frames,distance_activation,bestX,bestSeed,bestFrame,maxY,maxHome,rim,pit);
    return 0;
}
