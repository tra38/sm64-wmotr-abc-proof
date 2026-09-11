/* Conditional fixture only: the low pose and raised display are supplied.
 * All query/list/owner/lifecycle observations after setup are read-only.
 * Reuse the existing authenticated JP lifecycle fixture and its input policy. */
#define GetKeys LifecycleGetKeys
#define debugger_update_callback LifecycleDebuggerUpdate
#include "../jp-lifecycle/jp_lifecycle_probe.c"
#undef debugger_update_callback
#undef GetKeys

enum {
    V_FIND_FLOOR = 0x80381900,
    V_FIND_FLOOR_RETURN = 0x80381b90,
    V_POST_PLATFORM_FLOOR = 0x802c7f88,
    V_STATIC_PARTITION = 0x8038be98,
    V_DYNAMIC_PARTITION = 0x8038d698,
    V_NODE_POOL = 0x8038ee98,
    V_SURFACE_POOL = 0x8038ee9c,
    V_NODE_COUNT = 0x8035fdfc,
    V_SURFACE_COUNT = 0x8035fe00
};
static uint32_t vFloorCaller;
static unsigned vMarioQueries;
static unsigned vQueries;
static unsigned vPressed, vDown, vControllerA;

static int v_pool_member(uint32_t p, uint32_t base, unsigned size, unsigned count) {
    return p >= base && (p - base) % size == 0 && (p - base) / size < count;
}

static void v_dump_list(unsigned query, const char *kind, uint32_t partition) {
    /* Both supplied queries have cell X=5, Z=7, floor-list index zero. */
    uint32_t head = partition + ((7 * 16 + 5) * 3) * 8;
    uint32_t node = R32(head);
    uint32_t nodes = R32(V_NODE_POOL), surfaces = R32(V_SURFACE_POOL);
    unsigned count = 0;
    fprintf(stderr, "VERTICAL_LIST,query=%u,kind=%s,head=%08x,next=%08x\n",
            query, kind, head, node);
    while (node != 0 && count < 7002) {
        uint32_t surface;
        unsigned i;
        if (!v_pool_member(node, nodes, 8, R32(V_NODE_COUNT))) break;
        surface = R32(node + 4);
        if (!v_pool_member(surface, surfaces, 48, R32(V_SURFACE_COUNT))) break;
        fprintf(stderr, "VERTICAL_NODE,query=%u,kind=%s,index=%u,node=%08x,next=%08x,surface=%08x,words=",
                query, kind, count, node, R32(node), surface);
        for (i = 0; i < 12; i++) fprintf(stderr, "%08x", R32(surface + 4 * i));
        fprintf(stderr, "\n");
        count++;
        node = R32(node);
    }
    fprintf(stderr, "VERTICAL_LIST_END,query=%u,kind=%s,count=%u,terminated=%d\n",
            query, kind, count, node == 0);
}

static void v_debugger_update(unsigned int pc) {
    const uint64_t *regs = (uint64_t *) DGetCPUDataPtr(M64P_CPU_REG_REG);
    if (pc == V_FIND_FLOOR) {
        vFloorCaller = regs == NULL ? 0 : (uint32_t) regs[31];
        resume_from_breakpoint();
        return;
    }
    if (pc == V_FIND_FLOOR_RETURN) {
        uint32_t sp = regs == NULL ? 0 : (uint32_t) regs[29];
        /* Same authenticated epilogue/stack layout used by the rank-1 probe. */
        uint32_t output = sp == 0 ? 0 : R32(sp + 0x4c);
        if (R16(A_CURR_AREA) == 1 && (output == A_MARIO_STATES + M_FLOOR
                || vFloorCaller == V_POST_PLATFORM_FLOOR)) {
            uint32_t floor = R32(output);
            int mario = output == A_MARIO_STATES + M_FLOOR;
            if (mario) vMarioQueries++;
            vQueries++;
            fprintf(stderr, "VERTICAL_QUERY,index=%u,timer=%u,kind=%s,caller=%08x,xyzBits=(%08x,%08x,%08x),floor=%08x,owner=%08x,action=%08x\n",
                    vQueries, R32(A_GLOBAL_TIMER), mario ? "geometry" : "platform",
                    vFloorCaller, R32(sp + 0x40), R32(sp + 0x44), R32(sp + 0x48),
                    floor, floor ? R32(floor + SURFACE_OBJECT) : 0,
                    R32(A_MARIO_STATES + M_ACTION));
            if (mario && vMarioQueries <= 2) {
                v_dump_list(vQueries, "dynamic", V_DYNAMIC_PARTITION);
                v_dump_list(vQueries, "static", V_STATIC_PARTITION);
            }
        }
        resume_from_breakpoint();
        return;
    }
    LifecycleDebuggerUpdate(pc);
}

EXPORT void CALL GetKeys(int control, BUTTONS *keys) {
    int before = gBoundaryInstalled;
    LifecycleGetKeys(control, keys);
    if (control != 0) return;
    if (!before && gBoundaryInstalled) {
        uint32_t object = R32(A_MARIO_OBJECT);
        /* Replace the inherited collision-centre/display fixture before any
         * subsequent game instruction. No action, floor or owner is supplied. */
        W32(object + O_POS_X, fbits(-2200.0f));
        W32(object + O_POS_Y, fbits(768.0f));
        W32(object + O_POS_Z, fbits(-1024.0f));
        W32(object + GFX_POS_X, fbits(-2200.0f));
        W32(object + GFX_POS_Y, 0x44f25bad);
        W32(object + GFX_POS_Z, fbits(-1024.0f));
        log_lifecycle("VERTICAL_SETUP");
        fprintf(stderr, "VERTICAL_SETUP_DEPTH,bits=%08x\n", R32(A_MARIO_STATES + 0xc0));
        if (DSetCallbacks(debugger_init_callback, v_debugger_update,
                debugger_vi_callback) != M64ERR_SUCCESS
                || !add_exec_breakpoint(V_FIND_FLOOR)
                || !add_exec_breakpoint(V_FIND_FLOOR_RETURN)) {
            fprintf(stderr, "VERTICAL_ERROR,kind=arm\n");
        }
    }
    if (gBoundaryInstalled) {
        unsigned input = R16(A_MARIO_STATES + 2);
        vPressed += (input & 2) != 0;
        vDown += (input & 0x80) != 0;
        vControllerA += keys->A_BUTTON != 0;
        if (gSawArea2) {
            fprintf(stderr, "VERTICAL_INPUTS,timer=%u,pressed=%u,down=%u,controller=%u\n",
                    R32(A_GLOBAL_TIMER), vPressed, vDown, vControllerA);
        }
    }
}
