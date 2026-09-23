/* Bounded geometry filter at the eight recorded RANDOM cog angles.
 * This is a host-side necessary-condition probe, not Mario placement or entry.
 * Reuse the pinned collision bodies and authentication from the existing scan. */
#define main angle_grid_main
#include "../ttc-cog-geometry/search.c"
#undef main

int main(int argc, char **argv) {
    static const float offsets[]={-.5f,-.125f,.125f,.5f,1,2,4,8,16,32,48};
    static const float strides[]={1,4,16,32,64};
    unsigned points=0, candidates=0, stable=0;
    int edges[48][2], edge_count=0;
    TerrainData vertices[600], *p;
    if(argc!=9) return 2;
    gMarioState=&mario; gMarioObject=&marioObject;
    load_static(); regression();
    pose(0,3,0,0);
    for(int i=0;i<8;i++) {
        char *end; long angle=strtol(argv[i+1],&end,10);
        if(*end || angle < -2147483647L || angle > 2147483647L) return 2;
        objects[i].oFaceAngleYaw=(int)angle;
    }
    gCurrentObject=&objects[0]; p=(TerrainData *)objects[0].collisionData+1;
    transform_object_vertices(&p,vertices);
    p++; int triangles=*p++;
    for(int i=0;i<triangles;i++,p+=3) {
        if(vertices[p[0]*3+1]!=positions[0][1] || vertices[p[1]*3+1]!=positions[0][1]
            || vertices[p[2]*3+1]!=positions[0][1]) continue;
        for(int j=0;j<3;j++) {
            int a=p[j],b=p[(j+1)%3],e;
            for(e=0;e<edge_count;e++) if(edges[e][0]==b && edges[e][1]==a) break;
            if(e<edge_count) edges[e][0]=edges[e][1]=-1;
            else {if(edge_count==48) abort();edges[edge_count][0]=a;edges[edge_count++][1]=b;}
        }
    }
    pointTag++;
    for(int e=0;e<edge_count;e++) if(edges[e][0]>=0) {
        int a=edges[e][0]*3,b=edges[e][1]*3;
        float ax=vertices[a],az=vertices[a+2],bx=vertices[b],bz=vertices[b+2];
        float nx=bz-az,nz=ax-bx,len=sqrtf(nx*nx+nz*nz);nx/=len;nz/=len;
        if(nx*((ax+bx)*.5f-positions[0][0])+nz*((az+bz)*.5f-positions[0][2])<0) {nx=-nx;nz=-nz;}
        for(int t=0;t<=32;t++) for(unsigned o=0;o<sizeof(offsets)/sizeof(*offsets);o++) {
            float x=ax+(bx-ax)*((float)t/32)+nx*offsets[o];
            float z=az+(bz-az)*((float)t/32)+nz*offsets[o],y=positions[0][1];
            if(!fresh_point(x,z)) continue;
            points++;load_at(x,y,z);init_probe_mario(x,y,z,0,0);
            if(!mario.floor || mario.floorHeight+100>=y) continue;
            unsigned v;
            for(v=0;v<sizeof(strides)/sizeof(*strides);v++) {
                init_probe_mario(x,y,z,-4*nx*strides[v],-4*nz*strides[v]);
                if(probe(x,y,z,-nx*strides[v],-1,-nz*strides[v],0,3)) break;
            }
            if(v==sizeof(strides)/sizeof(*strides)) continue;
            candidates++;init_probe_mario(x,y,z,0,0);update_mario_geometry_inputs(&mario);
            if(!exact_position(x,y,z) || !(mario.input&INPUT_OFF_FLOOR) || (mario.input&INPUT_SQUISHED)) continue;
            stable++;
            if(stable<=5) printf("{\"kind\":\"geometry_candidate\",\"position\":[%.9g,%.9g,%.9g],\"stride\":%.9g}\n",x,y,z,strides[v]);
        }
    }
    printf("{\"kind\":\"geometry_counts\",\"pair\":[29,32],\"point_samples\":%u,\"close_gap_candidates\":%u,\"refresh_stable_candidates\":%u}\n",points,candidates,stable);
    return 0;
}
