/* A bounded witness search with favorable RNG outcomes, not RNG schedules.
 * It branches over both random turns, all 100 legal walk durations, and both
 * jump turns. Outside the home radius it chooses the legal duration 20.
 * Quantized duplicate removal and a beam limit make failure INCONCLUSIVE.
 * Static terrain, one actor and a fixed Mario pose are the declared world.
 */
#define SEARCH_DEPTH 24
#define SEARCH_BEAM 1024
#define SEARCH_HASH 262144
struct Choice { unsigned short duration; signed char sign; unsigned char jump; };
struct SearchNode {
    struct Object object;
    float distance, score;
    unsigned frames, count;
    struct Choice path[SEARCH_DEPTH];
};
static struct SearchNode beam_a[SEARCH_BEAM],beam_b[SEARCH_BEAM];
static unsigned long long seen[SEARCH_HASH];
static float target_x,target_z,closest_distance=1e20f;
static struct Choice current_path[SEARCH_DEPTH],best_path[SEARCH_DEPTH];
static unsigned current_count,best_count,current_frame,best_frame;
static float best_x,best_y,best_z;
static FILE *choice_trace;
static int reached_rim;

static void observe(void) {
    float dx=o->oPosX-target_x, dz=o->oPosZ-target_z;
    float d=dx*dx+dz*dz;
    if(d<closest_distance) {
        closest_distance=d; best_frame=current_frame; best_count=current_count;
        best_x=o->oPosX; best_y=o->oPosY; best_z=o->oPosZ;
        memcpy(best_path,current_path,sizeof(best_path));
    }
    if(o->oPosX>=-3112 && o->oPosX<=-3071 &&
       o->oPosZ>=1434 && o->oPosZ<=2970 && o->oFloorHeight>=72) reached_rim=1;
    if(choice_trace) fprintf(choice_trace,"%u,%.9g,%.9g,%.9g,%d,%d,%d,%u,%.9g,%d\n",
        current_frame,o->oPosX,o->oPosY,o->oPosZ,(s16)o->oMoveAngleYaw,
        o->oAction,o->oGoombaWalkTimer,o->oMoveFlags,o->oFloorHeight,o->activeFlags);
}
static int decision(void) {
    float dx=o->oPosX-o->oHomeX, dy=o->oPosY-o->oHomeY, dz=o->oPosZ-o->oHomeZ;
    return o->oAction==GOOMBA_ACT_WALK && !o->oGoombaTurningAwayFromWall &&
        !(o->oMoveFlags & (OBJ_MOVE_HIT_WALL|OBJ_MOVE_HIT_EDGE)) &&
        sqrtf(dx*dx+dy*dy+dz*dz)<=1000 && o->oGoombaWalkTimer==0;
}
static void choose(struct Choice c) {
    grant_values[0]=grant_kind[!c.jump];
    grant_values[1]=grant_sign[c.sign>0];
    grant_values[2]=grant_duration[c.duration-100];
    grant_at=0; grant_count=c.jump ? 2 : 3;
}
/* Stop after preparation, immediately before a genuine random choice. */
static int advance(struct SearchNode *result) {
    for(unsigned i=0;i<4096;i++) {
        grant_count=grant_at=0;
        float distance=prepare();
        if(decision()) {
            result->object=goomba; result->distance=distance;
            result->frames=current_frame; result->count=current_count;
            memcpy(result->path,current_path,sizeof(result->path));
            float dx=o->oPosX-target_x,dz=o->oPosZ-target_z;
            result->score=dx*dx+dz*dz;
            return 1;
        }
        /* With a fixed Mario and no other actors, a far actor cannot move
         * back into range. This branch is abandoned, not treated as a win. */
        if(distance_activation && (o->activeFlags&ACTIVE_FLAG_FAR_AWAY) && distance>4000)
            return 0;
        act_move(distance); current_frame++; observe();
    }
    return 0;
}
static unsigned long long node_key(const struct SearchNode *n) {
    const struct Object *p=&n->object;
    int fields[]={ (int)floorf(p->oPosX/8),(int)floorf(p->oPosZ/8),
        (int)floorf(p->oPosY/2),(s16)p->oMoveAngleYaw/512,
        p->oMoveFlags,p->oGoombaTurningAwayFromWall,
        (int)(p->oForwardVel*10),(int)(p->oVelY*2) };
    unsigned long long h=1469598103934665603ull;
    for(unsigned i=0;i<sizeof(fields)/sizeof(fields[0]);i++) {h^=(unsigned)fields[i];h*=1099511628211ull;}
    return h ? h : 1;
}
static int new_key(unsigned long long h) {
    unsigned p=(unsigned)h&(SEARCH_HASH-1);
    for(unsigned n=0;n<SEARCH_HASH;n++,p=(p+1)&(SEARCH_HASH-1)) {
        if(seen[p]==h) return 0;
        if(!seen[p]) {seen[p]=h;return 1;}
    }
    return 0;
}
static int compare_nodes(const void *a,const void *b) {
    float x=((const struct SearchNode*)a)->score,y=((const struct SearchNode*)b)->score;
    return (x>y)-(x<y);
}
static int choice_search(int argc,char **argv) {
    assert(argc>=5);
    target_x=strtof(argv[2],NULL); target_z=strtof(argv[3],NULL);
    unsigned depth=strtoul(argv[4],NULL,10);
    assert(depth>0 && depth<=SEARCH_DEPTH);
    mario_z=700; distance_activation=1; grant_rng=1;
    if(argc>5 && !strcmp(argv[5],"south")) {start_x=-2100;start_z=3316;}
    if(argc>6) distance_activation=atoi(argv[6]);
    load_mesh(); start(0);
    struct SearchNode *a=beam_a,*b=beam_b;
    unsigned count=advance(&a[0]);
    assert(count==1);
    for(unsigned d=0;d<depth && count;d++) {
        unsigned kept=0;
        memset(seen,0,sizeof(seen));
        for(unsigned i=0;i<count;i++) for(unsigned choice=0;choice<202;choice++) {
            struct Choice c={100,1,0};
            if(choice>=200) {c.jump=1;c.sign=choice==200 ? -1 : 1;}
            else {c.duration=100+choice/2;c.sign=choice%2 ? 1 : -1;}
            goomba=a[i].object; gCurrentObject=&goomba;
            memset(&gNumCalls,0,sizeof(gNumCalls));gNumFindFloorMisses=0;
            current_frame=a[i].frames; current_count=a[i].count;
            memcpy(current_path,a[i].path,sizeof(current_path));
            current_path[current_count++]=c;
            choose(c); act_move(a[i].distance); current_frame++; observe();
            struct SearchNode next;
            if(!advance(&next) || !new_key(node_key(&next))) continue;
            if(kept<SEARCH_BEAM) b[kept++]=next;
            else {
                unsigned worst=0;
                for(unsigned j=1;j<kept;j++) if(b[j].score>b[worst].score) worst=j;
                if(next.score<b[worst].score) b[worst]=next;
            }
        }
        qsort(b,kept,sizeof(b[0]),compare_nodes);
        printf("CHOICE_DEPTH,depth=%u,kept=%u,closest=%.9g,x=%.9g,y=%.9g,z=%.9g,rim=%d\n",
            d+1,kept,sqrtf(closest_distance),best_x,best_y,best_z,reached_rim);
        fflush(stdout);
        struct SearchNode *swap=a;a=b;b=swap;count=kept;
    }
    printf("CHOICE_PATH,frames=%u",best_frame);
    for(unsigned i=0;i<best_count;i++)
        printf(",%s:%d:%u",best_path[i].jump?"jump":"walk",best_path[i].sign,best_path[i].duration);
    printf("\n");
    if(argc>7) {
        choice_trace=fopen(argv[7],"w"); assert(choice_trace);
        fprintf(choice_trace,"frame,x,y,z,yaw,action,timer,flags,floor,active\n");
        start(0); current_count=0;current_frame=0;
        struct SearchNode ready;
        assert(advance(&ready));
        unsigned replay_count=best_count;
        struct Choice replay_path[SEARCH_DEPTH];memcpy(replay_path,best_path,sizeof(replay_path));
        for(unsigned i=0;i<replay_count;i++) {
            choose(replay_path[i]);act_move(ready.distance);current_frame++;observe();
            advance(&ready);
        }
        fclose(choice_trace);
    }
    return 0;
}

/* Checked example of legal random outcomes reaching the OUTSIDE approach.
 * It does not reach the rim. No seed or scheduler is claimed for this list. */
static int replay_west(const char *trace_path) {
    const struct Choice path[]={
        {130,-1,0},{197,1,0},{199,1,0},{173,1,0},
        {100,-1,1},{100,-1,1},{100,-1,1},{100,-1,0}};
    target_x=-3200;target_z=2925;mario_z=700;distance_activation=1;grant_rng=1;
    load_mesh();start(0);
    if(trace_path) {
        choice_trace=fopen(trace_path,"w");assert(choice_trace);
        fprintf(choice_trace,"frame,x,y,z,yaw,action,timer,flags,floor,active\n");
    }
    struct SearchNode ready;
    assert(advance(&ready));
    for(unsigned i=0;i<sizeof(path)/sizeof(path[0]);i++) {
        current_path[current_count++]=path[i];
        choose(path[i]);act_move(ready.distance);current_frame++;observe();
        assert(advance(&ready));
    }
    if(choice_trace) fclose(choice_trace);
    assert(best_frame==847 && best_x==-3196.341552734375f && best_y==0 &&
        best_z==2895.0380859375f && !reached_rim);
    printf("WESTERN_WAYPOINT,frame=%u,x=%.9g,y=%.9g,z=%.9g,rim=%d\n",
        best_frame,best_x,best_y,best_z,reached_rim);
    return 0;
}
