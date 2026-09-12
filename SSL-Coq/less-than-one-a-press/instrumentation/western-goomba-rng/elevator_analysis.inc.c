/* Source-driven scene inputs for the isolated RNG search. The elevator loop
 * is extracted unchanged. Its caller's timer convention is supplied here;
 * live platform attachment and collision loading are NOT simulated.
 * Frame 0 is the IDLE update that sees Mario already on the elevator. */
struct StockGoomba { float x, spawn_y, y, z; int triplet; };
static struct StockGoomba stock[9];
static struct Object lift, pole;
static float second_pole_grip_y, second_pole_hitbox_top;

static void build_scene(void) {
    for(unsigned i=0;i<6;i++) {
        const s16 *p=source_singletons[i];
        stock[i]=(struct StockGoomba){p[0],p[1],find_floor_height(p[0],p[1]+200,p[2]),p[2],0};
    }
    const s16 *p=source_triplet_parent[0];
    for(unsigned i=0;i<3;i++) {
        s16 angle=i*(0x10000/3);
        s16 dx=500.0f*coss(angle),dz=500.0f*sins(angle);
        float py=find_floor_height(p[0],p[1]+200,p[2]);
        float x=p[0]+dx,z=p[2]+dz;
        stock[6+i]=(struct StockGoomba){x,py,find_floor_height(x,py+200,z),z,1};
    }
    assert(stock[0].y==640 && stock[1].y==0 && stock[2].y==0 &&
           stock[3].y==640 && stock[4].y==640 && stock[5].y==0);
    assert(stock[6].x==3681 && stock[6].z==3587 && stock[6].y==0);
    assert(stock[7].x==2932 && stock[7].z==4020 && stock[7].y==0);
    assert(stock[8].x==2931 && stock[8].z==3155 && stock[8].y==0);
    memset(&pole,0,sizeof(pole));gCurrentObject=&pole;
    pole.oBhvParams=source_pole_params[1];
    bhv_pole_init();
    second_pole_hitbox_top=source_poles[1][1]+pole.hitboxHeight;
    second_pole_grip_y=second_pole_hitbox_top-100;
    assert(second_pole_grip_y==4020 && second_pole_hitbox_top==4120);
    memset(&lift,0,sizeof(lift));memset(&mario,0,sizeof(mario));
    gCurrentObject=&lift;gMarioObject=&mario;mario.platform=&lift;
    lift.oPosX=source_elevator[0][0];lift.oPosZ=source_elevator[0][2];
    lift.oPosY=lift.oHomeY=source_elevator[0][1];
    for(unsigned frame=0;frame<901;frame++) {
        if(lift.oAction!=lift.oPrevAction) {
            lift.oTimer=0;lift.oSubAction=0;lift.oPrevAction=lift.oAction;
        }
        bhv_pyramid_elevator_loop();
        elevator_y[frame]=lift.oPosY;
        lift.oTimer++;
        if(lift.oAction!=lift.oPrevAction) {
            lift.oTimer=0;lift.oSubAction=0;lift.oPrevAction=lift.oAction;
        }
        assert(lift.oPosX==0 && lift.oPosZ==256);
    }
    assert(elevator_y[0]==4966 && elevator_y[9]==4966 && elevator_y[10]==4956);
    assert(elevator_y[493]==128 && elevator_y[502]==128 && elevator_y[900]==128);
    gCurrentObject=&goomba;
}

/* Declared ordinary post-initialization fields. DROP_TO_FLOOR uses the real
 * floor call above; SET_HOME follows it, and ON_GROUND is set by that command.
 * This is an initialization fixture, not execution of the full script. */
static void start_stock(unsigned actor) {
    assert(actor<9);
    start_x=stock[actor].x;start_y=stock[actor].y;start_z=stock[actor].z;
    start(0);o->oMoveFlags=OBJ_MOVE_ON_GROUND;o->oDrawingDistance=4000;
}

static float base_gap(float x,float z) {
    float dx=fmaxf(-511-x,fmaxf(0,x-512));
    float dz=fmaxf(-255-z,fmaxf(0,z-768));
    return sqrtf(dx*dx+dz*dz);
}
static int below_frame(float y) {
    for(unsigned frame=0;frame<901;frame++) if(elevator_y[frame]<=y) return frame;
    return -1;
}
static int report_scene(const char *trace_path) {
    load_mesh();build_scene();
    FILE *trace=trace_path ? fopen(trace_path,"w") : NULL;
    if(trace_path) assert(trace);
    if(trace) {
        fprintf(trace,"frame,seconds,elevator_y\n");
        for(unsigned i=0;i<901;i++) fprintf(trace,"%u,%.9g,%.9g\n",i,i/30.0,elevator_y[i]);
        fclose(trace);
    }
    printf("ELEVATOR,gripY=%.9g,hitboxTopY=%.9g,belowGripFrame=%d,belowHitboxFrame=%d,below640Frame=%d,bottomFrame=493,settledFrame=502\n",
        second_pole_grip_y,second_pole_hitbox_top,below_frame(second_pole_grip_y),
        below_frame(second_pole_hitbox_top),below_frame(640));
    for(unsigned i=0;i<9;i++) {
        struct StockGoomba p=stock[i];
        printf("ACTOR,id=%u,x=%.9g,spawnY=%.9g,homeY=%.9g,z=%.9g,triplet=%d,gapToBase=%.9g,belowHeightFrame=%d\n",
            i,p.x,p.spawn_y,p.y,p.z,p.triplet,base_gap(p.x,p.z),below_frame(p.y));
        assert(p.spawn_y<second_pole_grip_y && p.y+75<second_pole_grip_y);
    }
    /* The full base is MORE generous than legal Mario center positions.
     * Vertical separation can only increase this distance. This excludes
     * fresh spawner activation while confined to this rectangle, conditional
     * on the stock parent remaining at its normally initialized position. */
    float parent_gap=base_gap(source_triplet_parent[0][0],source_triplet_parent[0][2]);
    assert(parent_gap>3000);
    printf("TRIPLET_PARENT,minHorizontalDistance=%.9g,activationThreshold=3000,canSpawnFromBase=0\n",parent_gap);
    return 0;
}
