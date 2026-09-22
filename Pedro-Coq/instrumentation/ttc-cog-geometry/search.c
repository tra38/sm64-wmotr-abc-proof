/* Offline candidate discovery, never linked into the game or emulator.
 * The collision, surface-loading and air-quarter-step bodies below are pinned
 * source, not reimplementations. Host execution is not a Clight/N64 proof.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "sm64.h"
#include "surface_terrains.h"
#include "special_presets.h"
#include "level_misc_macros.h"
#include "engine/math_util.c"
#include "engine/surface_load.c"
#include "engine/surface_collision.c"
#include "game/mario_step.c"
#include "helpers.inc.c"
#include "levels/ttc/areas/1/collision.inc.c"
#include "levels/ttc/rotating_hexagon/collision.inc.c"
#include "levels/ttc/rotating_triangle/collision.inc.c"
#include "inputs.inc.c"

struct Object *gCurrentObject, *gMarioObject;
struct MarioState *gMarioState;
s32 gSurfacesAllocated, gSurfaceNodesAllocated;
s32 gNumStaticSurfaces, gNumStaticSurfaceNodes;
u32 gTimeStopState;
s16 *gEnvironmentRegions;
s16 gFindFloorIncludeSurfaceIntangible, gCheckingSurfaceCollisionsForCamera;
__typeof__(gNumCalls) gNumCalls;
__typeof__(gNumFindFloorMisses) gNumFindFloorMisses;
s16 gCurrLevelNum=LEVEL_TTC;
s16 level_trigger_warp(struct MarioState *m, s32 op) { (void)m; (void)op; abort(); }
const BehaviorScript bhvDDDWarp[] = {0};
/* Host data already uses native pointers. This adapter is only for the
 * irrelevant DDD room comparison; it is not an N64-address refinement. */
void *segmented_to_virtual(const void *p) { return (void *)p; }

static struct Object marioObject, objects[8];
static struct MarioState mario;
static struct Area area;
static struct Surface surfaces[2300];
static struct SurfaceNode nodes[7000];
static const int pairs[4][2]={{0,3},{0,4},{4,2},{3,2}};
static unsigned loadedMask=~0u;

static void load_static(void) {
    TerrainData *p=(TerrainData *)ttc_seg7_collision_level;
    TerrainData *vertices=NULL;
    RoomData *rooms=NULL;
    sSurfaceNodePool=nodes; sSurfacePool=surfaces; sSurfacePoolSize=2300;
    clear_static_surfaces();
    while (*p != TERRAIN_LOAD_CONTINUE) {
        if (*p == TERRAIN_LOAD_VERTICES) { p++; vertices=read_vertex_data(&p); }
        else { int type=*p++; if (!vertices) abort(); load_static_surfaces(&p, vertices, type, &rooms); }
    }
    gNumStaticSurfaces=gSurfacesAllocated;
    gNumStaticSurfaceNodes=gSurfaceNodesAllocated;
}

static void pose(int lower,int upper,int ly,int uy) {
    int i;
    memset(objects,0,sizeof(objects));
    for(i=0;i<8;i++) {
        struct Object *o=&objects[i];
        o->oPosX=positions[i][0]; o->oPosY=positions[i][1]; o->oPosZ=positions[i][2];
        o->oFaceAngleYaw=(i==lower)?ly:(i==upper)?uy:initialYaws[i];
        o->header.gfx.scale[0]=o->header.gfx.scale[1]=o->header.gfx.scale[2]=1;
        o->oCollisionDistance=400; o->oDrawingDistance=4000;
        o->collisionData=(TerrainData *)(isTriangle[i]?ttc_seg7_collision_07015650:ttc_seg7_collision_07015584);
    }
    loadedMask=~0u;
}

static void load_at(float x,float y,float z) {
    unsigned mask=0;
    int i;
    marioObject.oPosX=x; marioObject.oPosY=y; marioObject.oPosZ=z;
    for(i=0;i<8;i++) {
        float d=dist_between_objects(&objects[i],&marioObject);
        objects[i].oDistanceToMario=d;
        if(d<400) mask|=1u<<i;
    }
    if(mask!=loadedMask) {
        clear_dynamic_surfaces();
        for(i=0;i<8;i++) {
            gCurrentObject=&objects[i];
            load_object_collision_model();
        }
        loadedMask=mask;
        if(gSurfacesAllocated>=2300 || gSurfaceNodesAllocated>=7000) abort();
    }
    gCurrentObject=&marioObject;
}

static void init_probe_mario(float x,float y,float z, float vx,float vz) {
    memset(&mario,0,sizeof(mario));
    mario.pos[0]=x; mario.pos[1]=y; mario.pos[2]=z;
    mario.vel[0]=vx; mario.vel[1]=-4; mario.vel[2]=vz;
    mario.action=ACT_FREEFALL; mario.marioObj=&marioObject;
    mario.area=&area; area.terrainType=TERRAIN_STONE;
    vec3f_copy(marioObject.header.gfx.pos,mario.pos);
    mario.floorHeight=find_floor(x,y,z,&mario.floor);
    mario.ceilHeight=vec3f_find_ceil(mario.pos,mario.floorHeight,&mario.ceil);
}

static int owner(struct Surface *s) {
    int i;
    if(!s) return -2;
    for(i=0;i<8;i++) if(s->object==&objects[i]) return i;
    return -1;
}

static int exact_position(float x,float y,float z) {
    return mario.pos[0]==x && mario.pos[1]==y && mario.pos[2]==z;
}

static int probe(float x,float y,float z,float dx,float dy,float dz,int lower,int upper) {
    Vec3f next={x+dx,y+dy,z+dz}, query;
    struct Surface *floor,*ceil,*oldFloor=mario.floor;
    float oldHeight=mario.floorHeight, fh,ch;
    int branch,result;
    vec3f_copy(query,next);
    resolve_and_return_wall_collisions(query,150,50);
    resolve_and_return_wall_collisions(query,30,50);
    fh=find_floor(query[0],query[1],query[2],&floor);
    ch=vec3f_find_ceil(query,fh,&ceil);
    branch=owner(floor)==lower && owner(ceil)==upper && ch-fh>0 && ch-fh<=160 && next[1]<=fh;
    result=perform_air_quarter_step(&mario,next,0);
    return branch && result==AIR_STEP_LANDED &&
        exact_position(x,y,z) && mario.floor==oldFloor && mario.floorHeight==oldHeight;
}

static void replay_example(float x,float y,float z,float nx,float nz,int lower,int upper) {
    static int count;
    static float saved[8][2];
    int i,v;
    float stride=0;
    x=roundf(x); z=roundf(z);
    if(count==8) return;
    for(i=0;i<count;i++) if((x-saved[i][0])*(x-saved[i][0])+(z-saved[i][1])*(z-saved[i][1])<900) return;
    load_at(x,y,z); init_probe_mario(x,y,z,0,0);
    if(!mario.floor || mario.floorHeight+100>=y) return;
    update_mario_geometry_inputs(&mario);
    if(!exact_position(x,y,z) || !(mario.input&INPUT_OFF_FLOOR) || (mario.input&INPUT_SQUISHED)) return;
    for(v=0;v<5;v++) {
        static const float d[]={1,4,16,32,64};
        init_probe_mario(x,y,z,-nx*d[v]*4,-nz*d[v]*4);
        if(probe(x,y,z,-nx*d[v],-1,-nz*d[v],lower,upper)) {stride=d[v];break;}
    }
    if(stride!=1) return;
    init_probe_mario(x,y,z,0,0);
    saved[count][0]=x;saved[count++][1]=z;
    printf("{\"kind\":\"replay_candidate\",\"pair\":[%d,%d],\"yaw\":[0,0],\"pos\":[%.9g,%.9g,%.9g],\"inward\":[%.9g,%.9g],\"tested_stride\":%.9g,\"actual_floor\":%.9g,\"actual_ceiling\":%.9g}\n",slots[lower],slots[upper],x,y,z,-nx,-nz,stride,mario.floorHeight,mario.ceilHeight);
}

static void regression(void) {
    Vec3f q={1313,-2100.5f,-1098};
    int r;
    pose(0,3,0,0); load_at(1313,-2088,-1098);
    init_probe_mario(1313,-2088,-1098,0,0);
    if(mario.floorHeight!=-8191 || !mario.floor) abort();
    if(!probe(1313,-2088,-1098,.2401123046875f,-1,1.9202880859375f,0,3)) abort();
    init_probe_mario(1313,-2088,-1098,0,0); mario.action=ACT_GROUND_POUND; mario.vel[1]=-50;
    r=perform_air_quarter_step(&mario,q,0);
    if(r!=0 || mario.pos[1]!=-2100.5f || mario.pos[0]!=1313 || mario.pos[2]!=-1098) abort();
    puts("{\"kind\":\"regression\",\"recorded_pedro_return\":true,\"recorded_first_descent\":true}");
}

static unsigned hash_bytes(const void *p,size_t size) {
    const unsigned char *b=p;
    unsigned h=2166136261u;
    while(size--) h=(h^*b++)*16777619u;
    return h;
}

static unsigned long long pointKeys[131072];
static unsigned pointTags[131072],pointTag;
static int fresh_point(float x,float z) {
    unsigned a,b,index;
    unsigned long long key;
    memcpy(&a,&x,4);memcpy(&b,&z,4);
    key=((unsigned long long)a<<32)|b;
    index=(a*2654435761u+b*2246822519u)&131071;
    while(pointTags[index]==pointTag) {
        if(pointKeys[index]==key) return 0;
        index=(index+1)&131071;
    }
    pointTags[index]=pointTag;pointKeys[index]=key;
    return 1;
}

int main(int argc,char **argv) {
    int step=argc>1?atoi(argv[1]):4096, segments=argc>2?atoi(argv[2]):32;
    int pi,ly,uy,e,t,oi,vi;
    static const float offsets[]={-.5f,-.125f,.125f,.5f,1,2,4,8,16,32,48};
    static const float strides[]={1,4,16,32,64};
    gMarioState=&mario; gMarioObject=&marioObject;
    if(sizeof(float)!=4 || sizeof(TerrainData)!=2 ||
       sizeof(gSineTable)!=COUNT_SINE*4 ||
       hash_bytes(gSineTable,sizeof(gSineTable))!=EXPECT_SINE ||
       sizeof(ttc_seg7_collision_07015584)!=COUNT_HEXAGON*2 ||
       hash_bytes(ttc_seg7_collision_07015584,sizeof(ttc_seg7_collision_07015584))!=EXPECT_HEXAGON ||
       sizeof(ttc_seg7_collision_07015650)!=COUNT_TRIANGLE*2 ||
       hash_bytes(ttc_seg7_collision_07015650,sizeof(ttc_seg7_collision_07015650))!=EXPECT_TRIANGLE) abort();
    load_static(); regression();
    for(pi=0;pi<4;pi++) {
        int lo=pairs[pi][0], hi=pairs[pi][1];
        unsigned long long tests=0,offFloor=0,candidates=0,refreshStable=0,gp=0;
        unsigned poses=0,poseCandidates=0,poseGp=0,examples=0;
        for(ly=0;ly<65536;ly+=step) for(uy=0;uy<65536;uy+=step) {
            TerrainData vertices[600],*p;
            int n, a,b, fi, fj, edgeCount=0, edges[48][2];
            unsigned long long before=candidates,beforeGp=gp;
            pose(lo,hi,ly,uy); poses++; pointTag++;
            gCurrentObject=&objects[lo]; p=(TerrainData *)objects[lo].collisionData+1;
            n=*p; transform_object_vertices(&p,vertices);
            /* Derive the top perimeter from triangle edge multiplicities. */
            p++; n=*p++;
            for(fi=0;fi<n;fi++,p+=3) {
                if(vertices[p[0]*3+1]!=positions[lo][1] || vertices[p[1]*3+1]!=positions[lo][1] ||
                   vertices[p[2]*3+1]!=positions[lo][1]) continue;
                for(fj=0;fj<3;fj++) {
                    a=p[fj]; b=p[(fj+1)%3];
                    for(e=0;e<edgeCount;e++) if(edges[e][0]==b && edges[e][1]==a) break;
                    if(e<edgeCount) {edges[e][0]=edges[e][1]=-1;}
                    else {edges[edgeCount][0]=a; edges[edgeCount++][1]=b;}
                }
            }
            for(e=0;e<edgeCount;e++) if(edges[e][0]>=0) {
                float ax,az,bx,bz,nx,nz,len;
                a=edges[e][0]*3; b=edges[e][1]*3;
                ax=vertices[a]; az=vertices[a+2]; bx=vertices[b]; bz=vertices[b+2];
                nx=bz-az; nz=ax-bx; len=sqrtf(nx*nx+nz*nz); nx/=len; nz/=len;
                if(nx*((ax+bx)*.5f-positions[lo][0])+nz*((az+bz)*.5f-positions[lo][2])<0) {nx=-nx;nz=-nz;}
                for(t=0;t<=segments;t++) for(oi=0;oi<(int)(sizeof(offsets)/sizeof(*offsets));oi++) {
                    float x=ax+(bx-ax)*((float)t/segments)+nx*offsets[oi];
                    float z=az+(bz-az)*((float)t/segments)+nz*offsets[oi];
                    float y=positions[lo][1];
                    if(!fresh_point(x,z)) continue;
                    tests++; load_at(x,y,z);
                    if(!(loadedMask & (1u<<lo)) || !(loadedMask & (1u<<hi))) continue;
                    init_probe_mario(x,y,z,0,0);
                    if(!mario.floor || mario.floorHeight+100>=y) continue;
                    offFloor++;
                    for(vi=0;vi<(int)(sizeof(strides)/sizeof(*strides));vi++) {
                        init_probe_mario(x,y,z,-4*nx*strides[vi],-4*nz*strides[vi]);
                        if(probe(x,y,z,-nx*strides[vi],-1,-nz*strides[vi],lo,hi)) break;
                    }
                    if(vi==(int)(sizeof(strides)/sizeof(*strides))) continue;
                    candidates++;
                    init_probe_mario(x,y,z,0,0); mario.action=ACT_GROUND_POUND; mario.vel[1]=-50;
                    update_mario_geometry_inputs(&mario);
                    if(!exact_position(x,y,z) || !(mario.input & INPUT_OFF_FLOOR) ||
                       (mario.input & INPUT_SQUISHED)) continue;
                    refreshStable++;
                    if(ly==0 && uy==0 && pi==0) {
                        replay_example(x,y,z,nx,nz,lo,hi);
                        load_at(x,y,z); init_probe_mario(x,y,z,0,0);
                        mario.action=ACT_GROUND_POUND; mario.vel[1]=-50;
                        update_mario_geometry_inputs(&mario);
                    }
                    if(probe(x,y,z,0,-12.5f,0,lo,hi)) {
                        gp++;
                        if(examples++<10) printf("{\"kind\":\"gp_candidate\",\"pair\":[%d,%d],\"yaw\":[%d,%d],\"pos\":[%.9g,%.9g,%.9g]}\n",slots[lo],slots[hi],ly,uy,x,y,z);
                    }
                }
            }
            poseCandidates+=candidates>before; poseGp+=gp>beforeGp;
        }
        printf("{\"kind\":\"counts\",\"pair\":[%d,%d],\"poses\":%u,\"point_samples\":%llu,\"off_floor_samples\":%llu,\"pedro_samples\":%llu,\"poses_with_pedro\":%u,\"refresh_stable_samples\":%llu,\"gp_first_quarter_samples\":%llu,\"poses_with_gp_first_quarter\":%u}\n",slots[lo],slots[hi],poses,tests,offFloor,candidates,poseCandidates,refreshStable,gp,poseGp);
        fflush(stdout);
    }
    return 0;
}
