/* Conditional mechanics experiment, not a controller-reachable setup.
 * Reuse the plugin ABI and read helpers. Never call its old setup/input path.
 * Candidate pose, negative depth and automatic-dialog checkpoint are supplied
 * once. The game then creates the gap, closes the dialog and runs 90 updates.
 */
#define GetKeys UnusedLifecycleGetKeys
#define RomOpen UnusedLifecycleRomOpen
#define RomClosed UnusedLifecycleRomClosed
#define PluginStartup LifecyclePluginStartup
#define debugger_update_callback UnusedLifecycleDebuggerUpdate
#include "../jp-lifecycle/jp_lifecycle_probe.c"
#undef debugger_update_callback
#undef RomClosed
#undef RomOpen
#undef GetKeys
#undef PluginStartup
#include <stdlib.h>
#include <mupen64plus/m64p_frontend.h>

enum {
    S_COPY = 0x80378800, S_QUERY1 = 0x802538a0, S_QUERY2 = 0x802538e4,
    S_DIALOG = 0x80257838, S_SINK = 0x80254164,
    S_SURFACE_POOL = 0x8038ee9c, S_SURFACE_COUNT = 0x8035fe00,
    S_DIALOG_ID = 0x80330424, S_AUTO_DIALOG = 0x20001305,
    S_STAR_DANCE = 0x00001307, S_DEPTH = 0xc0,
    S_HORIZON = 90
};
static unsigned sKind, sPhase, sPolicy, sPrepared, sSeeded, sDone;
static unsigned sSeedTimer, sReleaseTimer, sFirstReset, sFirstMove;
static unsigned sQueries, sMisses, sRetries, sTargets, sSteps, sCopies;
static unsigned sAController, sAPressed, sADown, sSeedWrites, sLateWrites;
static unsigned sTimer = UINT32_MAX, sQueryInFrame;
static unsigned sClose, sClosePoll, sEndDialogSeen;
static unsigned sDialogSinks;
static unsigned sMovesBeforeReset, sMissesBeforeReset, sRetriesBeforeReset;
static uint32_t sOwner, sSeedFloor, sApplyReturn;
static uint32_t sBefore[3];
static float sStartY, sReleaseY, sMaxGap, sMinDistance = 1e9f;
static const char *sRun;
static ptr_CoreDoCommand sCommand;

EXPORT m64p_error CALL PluginStartup(m64p_dynlib_handle core, void *context,
                                    void (*callback)(void *, int, const char *)) {
    m64p_error answer=LifecyclePluginStartup(core,context,callback);
    sCommand=(ptr_CoreDoCommand)dlsym(core,"CoreDoCommand");
    return sCommand ? answer : M64ERR_INCOMPATIBLE;
}

static void seed_store(uint32_t address, uint32_t value) {
    if (sSeeded) { sLateWrites++; abort(); }
    sSeedWrites++;
    W32(address, value);
}

static void pose(float x, float y, float z) {
    unsigned i;
    float xyz[3] = {x, y, z};
    uint32_t object = R32(A_MARIO_OBJECT);
    for (i = 0; i < 3; i++) {
        seed_store(A_MARIO_STATES + M_POS_X + 4*i, fbits(xyz[i]));
        seed_store(object + O_POS_X + 4*i, fbits(xyz[i]));
        seed_store(object + GFX_POS_X + 4*i, fbits(xyz[i]));
        seed_store(A_MARIO_STATES + 0x48 + 4*i, 0); /* velocity */
    }
    seed_store(A_MARIO_STATES + 0x54, 0); /* forward speed */
    seed_store(A_MARIO_PLATFORM, 0);
    seed_store(object + 0x214, 0);
}

static void sample(const char *tag) {
    uint32_t o = R32(A_MARIO_OBJECT), m = A_MARIO_STATES;
    fprintf(stderr, "SUPPORT_%s,timer=%u,step=%d,area=%u,action=%08x,state=%u,"
            "pos=(%.9g,%.9g,%.9g),display=(%.9g,%.9g,%.9g),raw=(%.9g,%.9g,%.9g),"
            "depth=%.9g,platform=%08x,topTimer=%u,stop=%08x\n", tag,
            R32(A_GLOBAL_TIMER), sReleaseTimer ? (int)(R32(A_GLOBAL_TIMER)-sReleaseTimer) : -1,
            R16(A_CURR_AREA), R32(m+M_ACTION), R16(m+0x18),
            rfloat(m+M_POS_X),rfloat(m+M_POS_Y),rfloat(m+M_POS_Z),
            rfloat(o+GFX_POS_X),rfloat(o+GFX_POS_Y),rfloat(o+GFX_POS_Z),
            rfloat(o+O_POS_X),rfloat(o+O_POS_Y),rfloat(o+O_POS_Z),
            rfloat(m+S_DEPTH),R32(A_MARIO_PLATFORM),R32(gTop+O_TIMER),R32(A_TIME_STOP_STATE));
}

/* Only proposes a point on a recorded live surface. The subsequent original
 * game's floor query must validate both height and owner; this is not a
 * replacement implementation of find_floor. */
static uint32_t propose_floor(float *x, float *y, float *z) {
    uint32_t base = R32(S_SURFACE_POOL), count = R32(S_SURFACE_COUNT), best = 0;
    unsigned i;
    float highest = -11000.0f;
    for (i = 0; i < count && i < 2300; i++) {
        uint32_t p = base + 48*i;
        float nx = rfloat(p+28), ny = rfloat(p+32), nz = rfloat(p+36), h;
        int j, inside = 1;
        if (R32(p+44) != sOwner || ny <= 0.01f) continue;
        if (sKind >= 3) {
            *x = ((int16_t)R16(p+10)+(int16_t)R16(p+16)+(int16_t)R16(p+22))/3.0f;
            *z = ((int16_t)R16(p+14)+(int16_t)R16(p+20)+(int16_t)R16(p+26))/3.0f;
        }
        for (j = 0; j < 3; j++) {
            uint32_t a = p+10+6*j, b = p+10+6*((j+1)%3);
            float ax=(int16_t)R16(a), az=(int16_t)R16(a+4);
            float bx=(int16_t)R16(b), bz=(int16_t)R16(b+4);
            if ((az-(int16_t)*z)*(bx-ax)-(ax-(int16_t)*x)*(bz-az) < 0) inside=0;
        }
        if (!inside) continue;
        h = -(nx*(int16_t)*x+nz*(int16_t)*z+rfloat(p+40))/ny;
        if (h > highest) { best=p; highest=h; }
        if (sKind >= 3) break; /* one explicitly sampled face per Tox Box */
    }
    *y = highest;
    return best;
}

static void install_dialog_candidate(void) {
    float x = sKind == 0 ? -2048.0f : -2200.0f, y, z = -1024.0f;
    uint32_t floor = 0;
    if (sKind < 2) y = sKind == 0 ? 768.0f : 1280.0f;
    else {
        floor = propose_floor(&x, &y, &z);
        if (!floor) return;
    }
    pose(x,y,z);
    /* These are an explicit extra diagnostic checkpoint assumption. No star
     * contact or dialog reachability is inferred from these stores. */
    seed_store(A_MARIO_STATES+M_ACTION, S_AUTO_DIALOG);
    seed_store(A_MARIO_STATES+0x10, S_STAR_DANCE);
    seed_store(A_MARIO_STATES+0x18, 0x00010000); /* state 1, timer 0 */
    seed_store(A_MARIO_STATES+M_ACTION_ARG, 144); /* actual 30-star milestone */
    seed_store(A_MARIO_STATES+S_DEPTH, fbits(-0.5f));
    if (R32(S_QUERY1-8)!=0x0c0e0640 || R32(S_QUERY2-8)!=0x0c0e0640
        || R32(S_COPY+12)!=0xe5c40000) abort();
    if (!add_write_breakpoint(R32(A_MARIO_OBJECT)+GFX_POS_X,4)
        || !add_exec_breakpoint(S_QUERY1) || !add_exec_breakpoint(S_QUERY2)
        || !add_exec_breakpoint(S_DIALOG) || !add_exec_breakpoint(S_SINK)) abort();
    sStartY=y; sSeedFloor=floor; sSeedTimer=R32(A_GLOBAL_TIMER); sSeeded=1;
    fprintf(stderr,"SUPPORT_SEED,run=%s,kind=%u,phase=%u,policy=%u,horizon=%u,"
            "owner=%08x,proposedFloor=%08x,writes=%u,extraAssumption=dialog-checkpoint,"
            "initialGap=0\n",sRun,sKind,sPhase,sPolicy,S_HORIZON,sOwner,floor,sSeedWrites);
    sample("START");
}

static void support_debugger(unsigned int pc) {
    const uint64_t *r = (const uint64_t *)DGetCPUDataPtr(M64P_CPU_REG_REG);
    uint32_t m=A_MARIO_STATES, object=R32(A_MARIO_OBJECT), timer=R32(A_GLOBAL_TIMER);
    if (pc == A_APPLY_MARIO_PLATFORM_DISPLACEMENT) {
        if (gPuzzleArmed && !sSeeded && sPrepared && R32(gTop+O_TIMER)>=sPhase+1)
            install_dialog_candidate();
        if (sSeeded && !sDone) {
            unsigned i;
            for(i=0;i<3;i++) sBefore[i]=R32(m+M_POS_X+4*i);
            if (!sApplyReturn && r) { sApplyReturn=(uint32_t)r[31]; add_exec_breakpoint(sApplyReturn); }
            if (sReleaseTimer && timer-sReleaseTimer<S_HORIZON) sample("APPLY");
        }
    } else if (pc == sApplyReturn && sSeeded && !sDone) {
        if (sBefore[0]!=R32(m+M_POS_X) || sBefore[1]!=R32(m+M_POS_Y) || sBefore[2]!=R32(m+M_POS_Z)) {
            if (!sFirstReset) sMovesBeforeReset++;
            if (!sFirstMove) sFirstMove=timer;
            sample("MOVED");
        }
    } else if ((pc == S_QUERY1 || pc == S_QUERY2) && sSeeded && !sDone && r) {
        uint32_t floor=R32(m+M_FLOOR);
        {
            /* These are the two actual call-return sites. The existing Clight
             * query proof also checks that find_floor preserves State.pos. */
            float x=rfloat(m+M_POS_X), y=rfloat(m+M_POS_Y), z=rfloat(m+M_POS_Z);
            float distance=sqrtf((x+2200)*(x+2200)+(y-768)*(y-768)+(z+1024)*(z+1024));
            sQueryInFrame=pc==S_QUERY1 ? 1 : 2; sQueries++;
            if (distance<sMinDistance) sMinDistance=distance;
            if (!floor) { sMisses++; if(!sFirstReset) sMissesBeforeReset++; }
            if (sQueryInFrame==2) { sRetries++; if(!sFirstReset) sRetriesBeforeReset++; }
            if (sQueryInFrame==1 && !floor && distance<0.25f
                && fabsf(rfloat(object+GFX_POS_X)+2200)<0.25f
                && fabsf(rfloat(object+GFX_POS_Z)+1024)<0.25f
                && fabsf(rfloat(object+GFX_POS_Y)-1938.8648681640625f)<4) sTargets++;
            if (timer==sSeedTimer || sReleaseTimer || !floor || sQueryInFrame==2)
                fprintf(stderr,"SUPPORT_QUERY,timer=%u,index=%u,xyz=(%.9g,%.9g,%.9g),"
                        "floor=%08x,owner=%08x,height=%.9g,firstReset=%u\n",timer,sQueryInFrame,x,y,z,
                        floor,floor ? R32(floor+44):0,rfloat(m+M_FLOOR_HEIGHT),sFirstReset);
        }
    } else if (pc == S_COPY+12 && sSeeded && !sDone && r) {
        if ((uint32_t)r[4]==object+GFX_POS_X && (uint32_t)r[5]==m+M_POS_X) {
            sCopies++;
            if (!sFirstReset) { sFirstReset=timer; sample("RESET"); }
        }
    } else if (pc == S_SINK && sSeeded && !sDone && !sReleaseTimer) {
        sDialogSinks++;
    } else if (pc == S_DIALOG && sSeeded && !sDone) {
        if (R16(m+0x18)==24 && !sEndDialogSeen) { sEndDialogSeen=1; sample("LAST_DIALOG"); }
    }
    resume_from_breakpoint();
}

EXPORT int CALL RomOpen(void) {
    const char *value;
    sRun=getenv("SUPPORT_RUN"); if (!sRun) sRun="pilot";
    value=getenv("SUPPORT_KIND"); sKind=value ? strtoul(value,NULL,10):2;
    value=getenv("SUPPORT_PHASE"); sPhase=value ? strtoul(value,NULL,10):130;
    value=getenv("SUPPORT_POLICY"); sPolicy=value ? strtoul(value,NULL,10):0;
    return 1;
}

EXPORT void CALL RomClosed(void) {
    fprintf(stderr,"SUPPORT_RESULT,run=%s,seeded=%u,completed=%u,updates=%u,release=%u,"
            "firstReset=%u,firstMove=%u,startY=%.9g,releaseDisplayY=%.9g,maxGap=%.9g,"
            "queries=%u,misses=%u,retries=%u,targetCandidates=%u,minTargetDistance=%.9g,"
            "copies=%u,dialogSinks=%u,movesBeforeReset=%u,missesBeforeReset=%u,retriesBeforeReset=%u,"
            "controllerA=%u,pressedA=%u,downA=%u,lateWrites=%u\n",sRun,
            sSeeded,sDone,sSteps,sReleaseTimer,sFirstReset,sFirstMove,sStartY,sReleaseY,sMaxGap,
            sQueries,sMisses,sRetries,sTargets,sMinDistance,sCopies,sDialogSinks,
            sMovesBeforeReset,sMissesBeforeReset,sRetriesBeforeReset,sAController,sAPressed,sADown,sLateWrites);
}

EXPORT void CALL GetKeys(int control, BUTTONS *keys) {
    static const int axes[9][2]={{0,0},{-127,0},{127,0},{0,-127},{0,127},
        {-127,-127},{-127,127},{127,-127},{127,127}};
    uint32_t timer=R32(A_GLOBAL_TIMER), m=A_MARIO_STATES, object=R32(A_MARIO_OBJECT);
    unsigned i;
    memset(keys,0,sizeof(*keys)); if (control!=0) return;
    gPoll++;
    if (!gBreakpointTraceArmed) {
        if (DSetCallbacks(debugger_init_callback,support_debugger,debugger_vi_callback)!=M64ERR_SUCCESS) abort();
        gBreakpointTraceArmed=1;
    }
    if (gPoll>=150 && gPoll<156) keys->START_BUTTON=1;
    for(i=220;i<=280;i+=10) if(gPoll>=i && gPoll<i+2) keys->D_DPAD=1;
    if (gPoll>=330 && gPoll<336) keys->START_BUTTON=1;
    if (!gPuzzleArmed && gPoll>360 && R16(A_CURR_AREA)==1 && object) {
        find_area1_objects();
        if (gTop && gUpperWarp) { seed_store(gTop+O_PYRAMID_PILLARS_TOUCHED,4); gPuzzleArmed=1; }
    }
    if (gPuzzleArmed && !sPrepared && R32(gTop+O_TIMER)>=sPhase) {
        sOwner=sKind==2 ? gTop : 0;
        if (sKind>=3) {
            /* Stock Tox identity from home X/Z, not a supplied platform pointer. */
            static const float homeX[3]={-1284,1283,4873};
            for(i=0;i<OBJECT_COUNT;i++) {
                uint32_t p=pool_pointer(i);
                if (R16(p+O_ACTIVE_FLAGS) && rfloat(p+0x164)==homeX[sKind-3]) sOwner=p;
            }
            if (!sOwner) return;
            /* Pre-seed positioning only, to make its ordinary collision loader
             * consider Mario nearby. The next terrain pass constructs floors. */
            pose(rfloat(sOwner+O_POS_X),rfloat(sOwner+O_POS_Y)+800,rfloat(sOwner+O_POS_Z));
        }
        sPrepared=1;
    }
    if (!sSeeded || sDone) return;
    if (timer!=sTimer) {
        float gap=rfloat(object+GFX_POS_Y)-rfloat(m+M_POS_Y);
        uint16_t input=R16(m+2);
        sTimer=timer;
        if(gap>sMaxGap) sMaxGap=gap;
        if(input&2) sAPressed++;
        if(input&0x80) sADown++;
        if (!sClose && rfloat(object+GFX_POS_Y)>=1914.0f && timer>sSeedTimer+20) {
            sClose=1; sClosePoll=gPoll; sample("CLOSE_REQUEST");
        }
        if (!sReleaseTimer && sEndDialogSeen && R32(m+M_ACTION)!=S_AUTO_DIALOG) {
            sReleaseTimer=timer; sReleaseY=rfloat(object+GFX_POS_Y); sample("RELEASE");
        }
        if (sReleaseTimer) {
            sSteps=timer-sReleaseTimer;
            sample("POLL");
            if(sSteps==S_HORIZON) {
                sDone=1; sample("END");
                sCommand(M64CMD_STOP,0,NULL);
            }
        }
    }
    if (sClose && !sReleaseTimer && (gPoll-sClosePoll)%12==0) keys->B_BUTTON=1;
    if (sReleaseTimer && !sDone) {
        unsigned direction=sPolicy%9, buttons=sPolicy/9;
        keys->X_AXIS=axes[direction][0]; keys->Y_AXIS=axes[direction][1];
        keys->Z_TRIG=(buttons&1)!=0;
        keys->B_BUTTON=(buttons&2)!=0 && (timer-sReleaseTimer)%8==0;
        fprintf(stderr,"SUPPORT_INPUT,timer=%u,step=%u,x=%d,y=%d,b=%u,z=%u,a=%u\n",
                timer,timer-sReleaseTimer,keys->X_AXIS,keys->Y_AXIS,keys->B_BUTTON,keys->Z_TRIG,keys->A_BUTTON);
    }
    if(keys->A_BUTTON) sAController++;
}
