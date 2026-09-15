/* Execute real surface clearing/loading, floor/ceiling/wall queries and the
 * ground quarter step on explicit fixtures. This is NOT a whole game run.
 * The driver supplies an ordinary upright elevator and static Area 2 terrain.
 * Other actors, action dispatch, scheduling and controller reachability are
 * omitted. Native pointer translation and two unreached action calls are
 * declared below; none supplies a floor or modifies a collision answer.
 */
#include <assert.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "sm64.h"
#include "engine/math_util.h"
#include "engine/surface_collision.h"
#include "engine/surface_load.h"
#include "game/debug.h"
#include "game/interaction.h"
#include "game/mario.h"
#include "game/mario_step.h"
#include "game/object_list_processor.h"
#include "trig_tables.inc.c"
#define o gCurrentObject

struct Object *gCurrentObject, *gMarioObject;
struct MarioState *gMarioState;
struct SurfaceNode *sSurfaceNodePool;
struct Surface *sSurfacePool;
s16 sSurfacePoolSize;
s32 gSurfaceNodesAllocated, gSurfacesAllocated;
s32 gNumStaticSurfaceNodes, gNumStaticSurfaces;
u32 gTimeStopState;
SpatialPartitionCell gStaticSurfacePartition[NUM_CELLS][NUM_CELLS];
SpatialPartitionCell gDynamicSurfacePartition[NUM_CELLS][NUM_CELLS];
s16 gCheckingSurfaceCollisionsForCamera, gFindFloorIncludeSurfaceIntangible;
TerrainData *gEnvironmentRegions;
struct NumTimesCalled gNumCalls;
s32 gNumFindFloorMisses;
struct Surface gWaterSurfacePseudoFloor;
const BehaviorScript bhvDDDWarp[] = {0};
void *segmented_to_virtual(const void *p) { return (void *)p; }
static unsigned ledge_transitions;
static unsigned object_updates;
void cur_obj_update(void) { object_updates++; }
u32 set_mario_action(struct MarioState *m, u32 action, u32 arg) {
    (void)m; (void)arg; assert(action == ACT_LEDGE_CLIMB_DOWN);
    ledge_transitions++; return 0;
}
s16 set_mario_animation(struct MarioState *m, s32 animation) {
    (void)m; (void)animation; return 0;
}
#include "source_functions.inc"
#include "source_mesh.inc"
#include "source_actors.inc"

static struct Surface surfaces[2300];
static struct SurfaceNode nodes[7000];
static struct Object elevator, mario;
static struct MarioState mario_state;
static unsigned long long queries, quarter_steps, ledge_checks;
static unsigned floor_failures, outside, stops, low_gap_stops, failed_alignment;
static float first_stop_base=10000;
static float min_x=10000,max_x=-10000,min_z=10000,max_z=-10000;
static unsigned transformed_poses, stopped_scheduler_cases, descent_paths;
static int other_nearest_x=-10000;

static void load_static(void) {
    TerrainData *v=ssl_seg7_area_2_collision+2, *p=v+3*ssl_seg7_area_2_collision[1];
    RoomData *rooms=NULL;
    sSurfacePool=surfaces; sSurfaceNodePool=nodes; sSurfacePoolSize=2300;
    while (*p<64 || *p>=101) { int type=*p++; load_static_surfaces(&p,v,type,&rooms); }
    assert(*p==65 && gSurfacesAllocated==1558 && gSurfaceNodesAllocated<7000);
    gNumStaticSurfaces=gSurfacesAllocated; gNumStaticSurfaceNodes=gSurfaceNodesAllocated;
}

static void reload(float base) {
    memset(&elevator,0,sizeof(elevator));
    elevator.activeFlags=ACTIVE_FLAG_ACTIVE;
    elevator.oRoom=-1;
    elevator.oPosY=base; elevator.oPosZ=256;
    elevator.oDistanceToMario=19000; elevator.oCollisionDistance=20000;
    elevator.oDrawingDistance=4000;
    elevator.header.gfx.scale[0]=elevator.header.gfx.scale[1]=elevator.header.gfx.scale[2]=1;
    elevator.collisionData=ssl_seg7_collision_pyramid_elevator;
    gCurrentObject=&elevator; gMarioObject=&mario; gMarioState=&mario_state;
    mario.oPosY=base; mario.oPosZ=256;
    gTimeStopState=0;
    clear_dynamic_surfaces();
    load_object_collision_model();
    assert(gSurfacesAllocated==1594 && gSurfaceNodesAllocated<7000);
    for(int i=1558;i<1594;i++) assert(surfaces[i].object==&elevator);
}

static void check(float x,float z,float base,float gap,int full) {
    struct Surface *floor=NULL;
    float h=find_floor(x,base+gap,z,&floor);
    queries++;
    if(!floor || floor->object!=&elevator || h!=base) {
        if(floor_failures++<3) fprintf(stderr,"floor: x=%g z=%g base=%g gap=%g h=%g\n",x,z,base,gap,h);
    }
    if(!full) return;
    memset(&mario_state,0,sizeof(mario_state));
    mario_state.action=ACT_WALKING;
    mario_state.pos[0]=x; mario_state.pos[1]=base+gap; mario_state.pos[2]=z;
    Vec3f next={x,base+gap,z};
    int result=perform_ground_quarter_step(&mario_state,next);
    quarter_steps++;
    if(next[0]<-459 || next[0]>460 || next[2]<-203 || next[2]>716) {
        if(outside++<3) fprintf(stderr,"outside: x=%g z=%g base=%g gap=%g -> %g,%g\n",x,z,base,gap,next[0],next[2]);
    }
    if(next[0]<min_x) min_x=next[0];
    if(next[0]>max_x) max_x=next[0];
    if(next[2]<min_z) min_z=next[2];
    if(next[2]>max_z) max_z=next[2];
    if(result==GROUND_STEP_HIT_WALL_STOP_QSTEPS) {
        stops++;
        if(gap<=100) low_gap_stops++;
        if(base<first_stop_base) first_stop_base=base;
    }
    /* A wall correction can cross the diagonal between the two base faces;
     * the owner and height must agree, not the triangle pointer before it. */
    if(gap<=100 && (mario_state.pos[1]!=base || !mario_state.floor ||
                    mario_state.floor->object!=&elevator)) failed_alignment++;
    /* Check the real ledge-down function at the corrected, still raised pose.
     * All queried gaps here are <=110, below its independent >160 trigger. */
    mario_state.pos[0]=next[0]; mario_state.pos[1]=base+gap; mario_state.pos[2]=next[2];
    mario_state.forwardVel=0;
    check_ledge_climb_down(&mario_state); ledge_checks++;
}

/* Every table-indexed yaw of either horizontal Grindel and every pitch of
 * Spindel, with their stock transverse coordinates. This checks transforms,
 * not the gameplay invariant that those owner coordinates stay unchanged. */
static void other_meshes(void) {
    for(unsigned actor=0;actor<8;actor++) {
        TerrainData *mesh=actor<3 ? ssl_seg7_collision_grindel :
            actor==3 ? ssl_seg7_collision_spindel : ssl_seg7_collision_0702808C;
        unsigned turns=(actor>=1 && actor<=3) ? 4096 : 1;
        for(unsigned turn=0;turn<turns;turn++) {
            struct Object support={0};
            support.oPosX=actor_positions[actor][0];
            support.oPosY=actor_positions[actor][1];
            support.oPosZ=actor_positions[actor][2];
            float scale=(actor==1 || actor==2) ? 0.9f : 1.0f;
            support.header.gfx.scale[0]=support.header.gfx.scale[1]=support.header.gfx.scale[2]=scale;
            if(actor==3) support.oFaceAnglePitch=turn*16;
            else support.oFaceAngleYaw=turn*16;
            gCurrentObject=&support;
            TerrainData transformed[600], *p=mesh+1;
            assert(mesh[1]*3<=600);
            transform_object_vertices(&p,transformed);
            for(int v=0;v<mesh[1];v++) {
                int x=transformed[v*3],z=transformed[v*3+2];
                if(actor==0) assert(x>510);
                else if(actor<=3) assert(x< -509);
                else assert(z< -253);
                if(actor==1 && x>other_nearest_x) other_nearest_x=x;
            }
            transformed_poses++;
        }
    }
}

static void ordinary_descents(void) {
    const int coords[]={-459,0,460};
    for(unsigned ix=0;ix<3;ix++) for(unsigned iz=0;iz<3;iz++) {
        reload(4000);
        memset(&mario_state,0,sizeof(mario_state));
        mario_state.action=ACT_WALKING;
        mario_state.pos[0]=coords[ix]; mario_state.pos[1]=4000;
        mario_state.pos[2]=coords[iz]+256;
        elevator.oAction=PYRAMID_ELEVATOR_ACT_CONSTANT_VELOCITY;
        for(int frame=1;frame<=11;frame++) {
            bhv_pyramid_elevator_loop();
            clear_dynamic_surfaces();
            elevator.header.gfx.throwMatrix=NULL;
            load_object_collision_model();
            assert(mario_state.pos[1]-elevator.oPosY==10);
            Vec3f next;
            vec3f_copy(next,mario_state.pos);
            int result=perform_ground_quarter_step(&mario_state,next);
            assert(result==GROUND_STEP_NONE || result==GROUND_STEP_HIT_WALL_CONTINUE_QSTEPS);
            assert(mario_state.pos[1]==4000-10*frame);
        }
        descent_paths++;
    }
}

int main(void) {
    load_static();
    other_meshes();
    ordinary_descents();
    /* Exhaustive integer interior at the lowest and highest ordinary bases.
     * Every integer Y in between also gets a coarse interior and a dense seam
     * sweep, including fractional queries near the four wall planes. */
    const float gaps[]={0,10,100,110};
    const float edges[]={-459,-458.999f,-435,-411,-410,-409.999f,-0.001f,0,
                         0.001f,410,411,411.001f,436,459.999f,460};
    for(int base=128;base<=4966;base++) {
        reload(base);
        if(base==128 || base==4966) {
            for(int x=-459;x<=460;x++) for(int z=-203;z<=716;z++)
                check(x,z,base,10,1);
        }
        for(unsigned g=0;g<sizeof(gaps)/sizeof(gaps[0]);g++) {
            for(unsigned x=0;x<sizeof(edges)/sizeof(edges[0]);x++)
                for(unsigned z=0;z<sizeof(edges)/sizeof(edges[0]);z++)
                    check(edges[x],edges[z]+256,base,gaps[g],1);
            for(int x=-459;x<=460;x++) check(x,x+256,base,gaps[g],1);
        }
    }
    /* Time stop: exercise BOTH real guards. The existing live floor remains.
     * This fixture does not pretend that the elevator keeps descending. */
    reload(4000);
    int count=gSurfacesAllocated, node_count=gSurfaceNodesAllocated;
    struct ObjectNode sentinel={0};
    elevator.header.next=&sentinel;
    for(unsigned flags=64;flags<128;flags++) {
        gTimeStopState=flags;
        assert(update_objects_during_time_stop(&sentinel,&elevator.header)==1);
        assert(!object_updates);
        clear_dynamic_surfaces(); load_object_collision_model();
        assert(gSurfacesAllocated==count && gSurfaceNodesAllocated==node_count);
        stopped_scheduler_cases++;
    }
    check(0,256,4000,0,1);
    printf("{\"versions\":\"compiled US or JP\",\"baseHeights\":4839,\"floorQueries\":%llu,"
           "\"quarterSteps\":%llu,\"ledgeChecks\":%llu,\"floorFailures\":%u,"
           "\"correctedOutsideInterior\":%u,\"earlyStops\":%u,\"lowGapStops\":%u,"
           "\"firstHighGapStopBase\":%.9g,\"alignmentFailures\":%u,"
           "\"ledgeTransitions\":%u,\"correctedXZ\":[%.9g,%.9g,%.9g,%.9g],"
           "\"timeStopRetainsLoadedFloor\":true,\"frozenSchedulerCases\":%u,"
           "\"otherSupportTransforms\":%u,\"nearestGrindelMaximumX\":%d,"
           "\"elevenDescentPaths\":%u}\n",queries,quarter_steps,ledge_checks,
           floor_failures,outside,stops,low_gap_stops,first_stop_base,failed_alignment,
           ledge_transitions,min_x,max_x,min_z,max_z,stopped_scheduler_cases,
           transformed_poses,other_nearest_x,descent_paths);
    fflush(stdout);
    /* This positive stop requires the ALREADY supplied 110-unit gap. It is
     * not a producer of that gap and cannot refute low-gap alignment. */
    assert(stops==4770 && first_stop_base==4952);
    assert(!floor_failures && !outside && !low_gap_stops && !failed_alignment && !ledge_transitions);
    return 0;
}
