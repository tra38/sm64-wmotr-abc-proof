/* A supplied-Mario-pose diagnostic, not a controller replay. Actual Tweester
 * chase and terrain functions are extracted unchanged. Dynamic objects,
 * particles, sound, Mario movement/capture and object scheduling are omitted. */
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
struct MarioState gMarioStates[1];
struct SurfaceNode *sSurfaceNodePool;
struct Surface *sSurfacePool;
s16 sSurfacePoolSize;
s32 gSurfaceNodesAllocated, gSurfacesAllocated;
SpatialPartitionCell gStaticSurfacePartition[NUM_CELLS][NUM_CELLS];
SpatialPartitionCell gDynamicSurfacePartition[NUM_CELLS][NUM_CELLS];
s16 gCheckingSurfaceCollisionsForCamera, gFindFloorIncludeSurfaceIntangible;
TerrainData *gEnvironmentRegions;
struct NumTimesCalled gNumCalls;
s32 gNumFindFloorMisses;
const BehaviorScript bhvTweesterSandParticle[] = {0};
void cur_obj_play_sound_1(s32 sound) {(void)sound;}
void print_debug_top_down_objectinfo(const char *str, s32 number) {(void)str;(void)number;}
struct Object *spawn_object(struct Object *parent, s32 model, const BehaviorScript *behavior) {
    (void)parent;(void)model;(void)behavior;return NULL;
}
#include "source_functions.inc"
#include "source_mesh.inc"
static struct Surface surfaces[4000];
static struct SurfaceNode nodes[20000];
static struct Object tornado, mario;
static const float homes[3][3]={{-3600,-200,2940},{1017,-200,3832},{3066,-200,400}};
static const int radii[3]={1800,2500,2500};

static void load_mesh(void) {
    TerrainData *p=source_mesh+2,*v=p; RoomData *rooms=NULL;
    p+=3*source_mesh[1];
    sSurfacePool=surfaces;sSurfaceNodePool=nodes;sSurfacePoolSize=4000;
    while(*p<64 || *p>=101) {int type=*p++;load_static_surfaces(&p,v,type,&rooms);}
    assert(*p==65 && gSurfacesAllocated<4000 && gSurfaceNodesAllocated<20000);
    printf("MESH,surfaces=%d,nodes=%d\n",gSurfacesAllocated,gSurfaceNodesAllocated);
}
static float floor_at(float x,float y,float z) {struct Surface *f;return find_floor(x,y,z,&f);}
static void start(int actor) {
    memset(&tornado,0,sizeof(tornado));memset(&mario,0,sizeof(mario));
    gCurrentObject=&tornado;gMarioObject=&mario;gMarioState=gMarioStates;
    gMarioStates[0].action=ACT_IDLE;
    o->oPosX=o->oHomeX=homes[actor][0];o->oPosZ=o->oHomeZ=homes[actor][2];
    o->oPosY=o->oHomeY=floor_at(o->oPosX,homes[actor][1]+200,o->oPosZ);
    o->activeFlags=ACTIVE_FLAG_ACTIVE;o->oRoom=-1;o->oGravity=-4;
    o->oBuoyancy=2;o->oWallHitboxRadius=30;o->oBhvParams2ndByte=radii[actor]/100;
    o->oAction=TWEESTER_ACT_CHASE;o->oSubAction=TWEESTER_SUB_ACT_CHASE;
    o->oFloorHeight=o->oPosY;
    o->oTweesterScaleTimer=-512;tweester_scale_and_move(1.0f);
    mario.hitboxRadius=37;mario.hitboxHeight=160;
}
static float distance_to_warp(void) {
    float dx=o->oPosX+2048,dz=o->oPosZ+1024;
    return sqrtf(dx*dx+dz*dz);
}
static void supply_mario(int actor,int angle,float radius) {
    mario.oPosX=homes[actor][0]+radius*sins(angle);
    mario.oPosZ=homes[actor][2]+radius*coss(angle);
    mario.oPosY=floor_at(mario.oPosX,20000,mario.oPosZ);
    float dx=mario.oPosX-o->oPosX,dy=mario.oPosY-o->oPosY,dz=mario.oPosZ-o->oPosZ;
    o->oDistanceToMario=sqrtf(dx*dx+dy*dy+dz*dz);
    o->oAngleToMario=atan2s(dz,dx);
}
int main(int argc,char **argv) {
    load_mesh();
    if(argc>1 && !strcmp(argv[1],"contact")) {
        start(0);
        o->oPosX=-2979.89648f;o->oPosY=880.013916f;o->oPosZ=-1022.63019f;
        o->oTweesterScaleTimer=0;tweester_scale_and_move(1.0f);
        o->hitboxRadius=o->header.gfx.scale[0]*1500;o->hitboxHeight=o->header.gfx.scale[1]*4000;
        mario.oPosX=-2200;mario.oPosY=768;mario.oPosZ=-1024;
        int tornado_contact=detect_object_hitbox_overlap(&mario,o);
        struct Object warp={0};warp.oPosX=-2048;warp.oPosY=768;warp.oPosZ=-1024;
        warp.hitboxRadius=150;warp.hitboxHeight=50;
        int warp_contact=detect_object_hitbox_overlap(&mario,&warp);
        printf("CONTACT,supplied=1,tornado=%d,warp=%d,radius=%.9g,height=%.9g,marioTop=%.9g,tornadoBase=%.9g\n",tornado_contact,warp_contact,o->hitboxRadius,o->hitboxHeight,mario.oPosY+mario.hitboxHeight,o->oPosY);
        assert(tornado_contact && warp_contact);return 0;
    }
    if(argc>1 && !strcmp(argv[1],"terrain")) {
        for(int actor=0;actor<3;actor++) {
            start(actor);float best=1e9;int waypoint=argc>2?atoi(argv[2]):0;
            for(int frame=0;frame<1200;frame++) {
                float tx=waypoint?-4200:-2048,tz=-1024;
                if(waypoint && hypotf(tx-o->oPosX,tz-o->oPosZ)<40)waypoint=0;
                o->oMoveAngleYaw=atan2s(tz-o->oPosZ,tx-o->oPosX);o->oForwardVel=20;
                cur_obj_update_floor_and_walls();
                if(o->oMoveFlags&OBJ_MOVE_HIT_WALL)o->oMoveAngleYaw=o->oWallAngle;
                cur_obj_move_standard(60);
                float d=distance_to_warp();if(d<best)best=d;
                if(frame%100==0)printf("TERRAIN,%d,%d,%.9g,%.9g,%.9g,%.9g,%u\n",actor,frame,o->oPosX,o->oPosY,o->oPosZ,d,o->oMoveFlags);
            }
            printf("TERRAIN_BEST,%d,%.9g\n",actor,best);
        }
        return 0;
    }
    if(argc>1 && !strcmp(argv[1],"floor")) {
        for(int x=-4000;x<=0;x+=128) printf("FLOOR,%d,%.9g\n",x,floor_at(x,20000,-1024));
        return 0;
    }
    if(argc!=1 && argc!=5) {
        fprintf(stderr,"Use no args, floor, contact, terrain [1], or actor angle inside outside.\n");return 2;
    }
    int trace=argc>1, ta=trace?atoi(argv[1]):-1;
    int tang=trace?atoi(argv[2]):0,ton=trace?atoi(argv[3]):0,toff=trace?atoi(argv[4]):0;
    for(int actor=0;actor<3;actor++) {
        if(getenv("ACTOR") && actor!=atoi(getenv("ACTOR")))continue;
        float best=1e9,bx=0,by=0,bz=0;int ba=0,bon=0,boff=0,bframe=0;
        int trials=0,hides=0,contacts=0,bcontact=-1;
        int angle_step=getenv("ANGLE_STEP")?atoi(getenv("ANGLE_STEP")):512;
        assert(angle_step>0);
        for(int angle=0;angle<65536;angle+=angle_step) for(int on=1;on<=8;on++) for(int off=1;off<=8;off++) {
            if(trace && (actor!=ta || angle!=tang || on!=ton || off!=toff))continue;
            start(actor);o->oMoveAngleYaw=angle;trials++;int first_contact=-1;
            int horizon=getenv("HORIZON")?atoi(getenv("HORIZON")):900;
            for(int frame=0;frame<horizon;frame++) {
                /* First leave the 200-unit home-return hide region. */
                int warmup=getenv("WARMUP")?atoi(getenv("WARMUP")):90;
                float radius=radii[actor]+((frame<warmup || (frame-warmup)%(on+off)<on)?-2:2);
                supply_mario(actor,angle,radius);
                o->hitboxRadius=o->header.gfx.scale[0]*1500;
                o->hitboxHeight=o->header.gfx.scale[1]*4000;
                tweester_act_chase();
                mario.numCollidedObjs=0;o->numCollidedObjs=0;
                if(detect_object_hitbox_overlap(&mario,o) && first_contact<0) {first_contact=frame;contacts++;}
                if(getenv("AVOID_CONTACT") && first_contact>=0)break;
                float d=distance_to_warp();
                if(d<best) {best=d;bx=o->oPosX;by=o->oPosY;bz=o->oPosZ;ba=angle;bon=on;boff=off;bframe=frame;bcontact=first_contact;}
                if(trace)printf("TRACE,%d,%.9g,%.9g,%.9g,%d,%.9g,%.9g,%.9g,%.9g\n",frame,o->oPosX,o->oPosY,o->oPosZ,o->oAction,mario.oPosX,mario.oPosY,mario.oPosZ,o->oDistanceToMario);
                if(o->oAction!=TWEESTER_ACT_CHASE) {hides++;break;}
            }
        }
        if(trials)printf("BEST,actor=%d,trials=%d,hides=%d,contacts=%d,distance=%.9g,x=%.9g,y=%.9g,z=%.9g,angle=%d,on=%d,off=%d,frame=%d,firstContact=%d\n",actor,trials,hides,contacts,best,bx,by,bz,ba,bon,boff,bframe,bcontact);
    }
    return 0;
}
