/* Offline execution of read-only receipts; never connects to a running game.
 * Legacy experiments vary seed and clock mode; KEEP_CLOCK_MODE variants vary
 * only the seed. The selected predicate is recorded in the build receipt.
 * See README.md for the explicit frame-boundary model and evidence limits. */
#define _POSIX_C_SOURCE 200809L
#include <unicorn/unicorn.h>
#include <unicorn/mips.h>
#include <errno.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "config.h"

#ifndef KEEP_CLOCK_MODE
#define KEEP_CLOCK_MODE 0
#endif
#ifndef COG_SCHEDULE_ONLY
#define COG_SCHEDULE_ONLY 0
#endif
#ifndef REQUIRED_COG_MASK
#define REQUIRED_COG_MASK 3
#endif
#if REQUIRED_COG_MASK < 1 || REQUIRED_COG_MASK > 3
#error REQUIRED_COG_MASK must select lower, upper, or both cogs
#endif

#define RAM_SIZE 0x800000u
#define RETURN_SENTINEL 0x80001000u
static uc_engine *vm;
static unsigned char *ram, *original;
static unsigned halted, unknown, rejected, baseline, draws, pedro, frame_done;
static unsigned dma_calls;
static unsigned trace_enabled, trial_update, rng_pending, rng_before, rng_slot;
#ifdef ANIMATION_DMA
static unsigned char *rom;
static size_t rom_size;
#endif
static unsigned cog_updates[2];
static uint64_t fuel, fuel_limit = 5000000, draw_hash;
static uint32_t floor_anchor, positions[3], cog_yaws[2];
static const struct initial *start;
static const char *reason;
static void setup_cpu(void);

static void checked(uc_err error) {
    if (error) { fprintf(stderr, "evaluator API: %s\n", uc_strerror(error)); exit(2); }
}
static uint64_t sx(uint32_t p) { return p & 0x80000000u ? 0xffffffff00000000ULL | p : p; }
static void inconclusive(const char *why) { unknown = 1; reason = why; checked(uc_emu_stop(vm)); }
static uint32_t offset(uint32_t p, unsigned n) {
    p &= 0x1fffffffu;
    if (n > RAM_SIZE || p > RAM_SIZE - n) { inconclusive("unmapped-data"); return 0; }
    return p;
}
static uint32_t r32(uint32_t p) {
    p = offset(p, 4);
    return ((uint32_t)ram[p] << 24) | ((uint32_t)ram[p+1] << 16) | ((uint32_t)ram[p+2] << 8) | ram[p+3];
}
static uint16_t r16(uint32_t p) { p = offset(p, 2); return ((uint16_t)ram[p] << 8) | ram[p+1]; }
static void w32(uint32_t p, uint32_t v) {
    p = offset(p, 4); ram[p] = v >> 24; ram[p+1] = v >> 16; ram[p+2] = v >> 8; ram[p+3] = v;
}
static void w16(uint32_t p, uint16_t v) { p = offset(p, 2); ram[p] = v >> 8; ram[p+1] = v; }
static float rf(uint32_t p) { uint32_t b = r32(p); float f; memcpy(&f, &b, 4); return f; }
static uint64_t reg(int r) { uint64_t v = 0; checked(uc_reg_read(vm, r, &v)); return v; }
static void setreg(int r, uint64_t v) { checked(uc_reg_write(vm, r, &v)); }
static void reject(const char *why) {
    if (!rejected) reason = why;
    rejected = 1; checked(uc_emu_stop(vm));
}
static void block(uc_engine *u, uint64_t a, uint32_t size, void *data) {
    (void)u; (void)data;
    /* Counts translated block sizes, conservatively including unexecuted tails.
       Budget exhaustion is UNKNOWN. It is not evidence against a seed. */
    fuel += size / 4 + 1;
    if (fuel > fuel_limit) { inconclusive("instruction-budget"); return; }
    unsigned p = offset((uint32_t)a, size);
    if (!unknown && memcmp(ram+p, original+p, size)) inconclusive("changed-instruction-bytes");
}
static void position_check(void) {
    for (unsigned i = 0; i < 3; ++i)
        if (r32(A_MARIO_STATES + 0x3c + 4*i) != positions[i]) reject("mario-position");
}
static void point(uc_engine *u, uint64_t a, uint32_t size, void *data) {
    (void)u; (void)size; (void)data; uint32_t pc = (uint32_t)a;
#ifdef ANIMATION_DMA
    if (pc == ANIMATION_DMA) {
        /* External I/O contract for memory.c:dma_read, restricted to Mario's
           allocated 16 KiB animation buffer. The actual caller, table lookup,
           animation update and all gameplay code still execute. No live game
           or ROM is modified. OS queues/cache/thread state are not modeled. */
        uint32_t dest = (uint32_t)reg(UC_MIPS_REG_A0);
        uint32_t begin = (uint32_t)reg(UC_MIPS_REG_A1);
        uint32_t end = (uint32_t)reg(UC_MIPS_REG_A2);
        uint32_t buffer = r32(ANIMATION_BUFFER);
        if (end < begin || end-begin > 0x4000 || dest != buffer
            || (uint32_t)reg(UC_MIPS_REG_RA) != ANIMATION_DMA_RETURN) {
            inconclusive("unsupported-dma-request"); return;
        }
        uint32_t length = (end-begin+15u)&~15u;
        if (begin < ANIMATION_ROM_BEGIN || begin > ANIMATION_ROM_END
            || length > ANIMATION_ROM_END-begin
            || begin > rom_size || length > rom_size-begin) {
            inconclusive("dma-rom-bounds"); return;
        }
        unsigned target = offset(dest, length);
        if (unknown) return;
        memcpy(ram+target, rom+begin, length);
        ++dma_calls;
        setreg(UC_MIPS_REG_PC, reg(UC_MIPS_REG_RA));
        return;
    }
#endif
    if (pc == RETURN_SENTINEL) { halted = 1; checked(uc_emu_stop(vm)); return; }
    if (pc == A_RANDOM_U16) {
        ++draws;
        draw_hash = (draw_hash ^ r16(A_RANDOM_SEED16)) * 1099511628211ULL;
        draw_hash = (draw_hash ^ ((r32(A_CURRENT_OBJECT)-A_OBJECT_POOL)/0x260)) * 1099511628211ULL;
        if (trace_enabled) {
            if (rng_pending) { inconclusive("nested-rng-trace"); return; }
            rng_pending = 1; rng_before = r16(A_RANDOM_SEED16);
            rng_slot = (r32(A_CURRENT_OBJECT)-A_OBJECT_POOL)/0x260;
        }
        return;
    }
    if (trace_enabled && pc == PC_RNG_EXIT) {
        if (!rng_pending) { inconclusive("unpaired-rng-trace"); return; }
        fprintf(stderr, "DRAW,%u,%u,%u,%u,%u,%u\n", trial_update, draws, rng_slot,
                rng_before, r16(A_RANDOM_SEED16), (unsigned)reg(UC_MIPS_REG_V0)&65535u);
        rng_pending = 0; return;
    }
    if (pc == start->finish) {
        frame_done = 1; halted = 1;
        /* The boundary shim only supports the same CALL_LOOP command. */
        if ((uint32_t)reg(UC_MIPS_REG_V0) != (uint32_t)start->gpr[4]) inconclusive("level-command-changed");
        if (baseline != 1) {
            if (!COG_SCHEDULE_ONLY) {
                position_check();
                if (r32(A_MARIO_STATES+0x68) != floor_anchor || r32(A_MARIO_PLATFORM)) reject("support-changed");
                if (!pedro) reject("no-close-gap-return");
            }
            for (unsigned j = 0; j < 2; ++j) {
                if (cog_updates[j] != 1) inconclusive("cog-update-count");
                if ((REQUIRED_COG_MASK & (1u<<j))
                    && r32(A_OBJECT_POOL+(j?32:29)*0x260+0xd4) != cog_yaws[j]) reject("cog-moved");
            }
        }
        checked(uc_emu_stop(vm)); return;
    }
    if (pc == PC_AIR_EXIT) {
        uint32_t sp = (uint32_t)reg(UC_MIPS_REG_SP), f = r32(sp+0x30), c = r32(sp+0x34);
        float gap = rf(sp+0x2c) - rf(sp+0x28);
        if (f && c && (uint32_t)reg(UC_MIPS_REG_V0) == 1 && rf(sp+0x44) <= rf(sp+0x28)
            && gap > 0 && gap <= 160 && r32(f+0x2c) == A_OBJECT_POOL+29*0x260
            && r32(c+0x2c) == A_OBJECT_POOL+32*0x260) ++pedro;
    }
    for (unsigned i = 0; i < sizeof(path_points)/sizeof(path_points[0]); ++i) {
        if (trace_enabled && pc == path_points[i].pc && !strcmp(path_points[i].routine, "bhv_ttc_cog_update")) {
            uint32_t object = r32(A_CURRENT_OBJECT);
            fprintf(stderr, "COG,%u,%s,%u,%d,%.9g,%.9g\n", trial_update,
                    path_points[i].leaving ? "exit" : "enter", (object-A_OBJECT_POOL)/0x260,
                    (int32_t)r32(object+0xd4), rf(object+0xf8), rf(object+0xfc));
        }
        if (pc != path_points[i].pc || !path_points[i].leaving) continue;
        if (!strcmp(path_points[i].routine, "bhv_ttc_cog_update")) {
            uint32_t object = r32(A_CURRENT_OBJECT);
            for (unsigned j = 0; j < 2; ++j) if (object == A_OBJECT_POOL+(j?32:29)*0x260) {
                ++cog_updates[j];
                if (baseline != 1 && (REQUIRED_COG_MASK & (1u<<j)) && r32(object+0xd4) != cog_yaws[j]) reject("cog-moved");
            }
        }
        if (baseline != 1 && !COG_SCHEDULE_ONLY && !strcmp(path_points[i].routine, "execute_mario_action")) position_check();
    }
}
static void run(uint32_t pc) {
    halted = 0; fuel = 0;
    uc_err error = uc_emu_start(vm, sx(pc), 0, 0, 0);
    if (error) inconclusive(uc_strerror(error));
    else if (!halted && !rejected && !unknown) inconclusive("missing-boundary");
}
static void setup_cpu(void) {
    setreg(UC_MIPS_REG_CP0_STATUS, start->status);
    /* Function-boundary contract: no live HI/LO, default floating-point control.
       This is validated against receipts, not an N64 CPU refinement theorem. */
    setreg(UC_MIPS_REG_HI, 0); setreg(UC_MIPS_REG_LO, 0); setreg(UC_MIPS_REG_FCSR, 0);
    for (unsigned i = 0; i < 32; ++i) {
        setreg(UC_MIPS_REG_0+i, start->gpr[i]); setreg(UC_MIPS_REG_F0+i, start->fpr[i]);
    }
}
static void next_frame(void) {
    /* Explicit host boundary: hardware/OS/audio threads are not simulated.
       Fixed controller data is retained. Actual select_gfx_pool executes. */
    w32(A_GLOBAL_TIMER, r32(A_GLOBAL_TIMER)+1);
    w16(RENDER_FB, (r16(RENDER_FB)+1)%3); w16(RENDERING_FB, (r16(RENDERING_FB)+1)%3);
    w16(PROFILE_INDEX, r16(PROFILE_INDEX)^1);
    setup_cpu(); setreg(UC_MIPS_REG_RA, sx(RETURN_SENTINEL)); run(GFX_SELECT); setup_cpu();
}
static unsigned number(const char *text) {
    char *end; errno = 0;
    if (!*text || *text == '-') { fprintf(stderr, "invalid number\n"); exit(2); }
    unsigned long n = strtoul(text, &end, 10);
    if (errno || *end || n > 0xffffffffUL) { fprintf(stderr, "invalid number\n"); exit(2); }
    return (unsigned)n;
}
static void hook_point(uint32_t pc) {
    uc_hook hook; checked(uc_hook_add(vm, &hook, UC_HOOK_CODE, (void *)point, NULL, sx(pc), sx(pc)));
}
int main(int argc, char **argv) {
    if (argc < 7 || argc > 8) {
        fprintf(stderr, "usage: sweep SNAPSHOT_DIR CASE FIRST_SEED SEED_COUNT HORIZON BASELINE [RAM_OUT]\n"); return 2;
    }
    unsigned which = number(argv[2]), first = number(argv[3]), count = number(argv[4]);
    unsigned horizon = number(argv[5]); baseline = number(argv[6]);
    if (which >= sizeof(starts)/sizeof(starts[0]) || first > 65535 || !count
        || count > 65536-first || !horizon || horizon > 1200 || baseline > 2 || (baseline && count != 1)) return 2;
    if (getenv("SWEEP_FUEL")) fuel_limit = number(getenv("SWEEP_FUEL"));
    if (!fuel_limit || fuel_limit > 5000000) return 2;
    if (getenv("SWEEP_TRACE")) trace_enabled = number(getenv("SWEEP_TRACE"));
    if (trace_enabled > 1 || (trace_enabled && count != 1)) return 2;
    start = &starts[which]; char path[4096];
    if (snprintf(path, sizeof(path), "%s/%u-enter.ram", argv[1], start->frame) >= (int)sizeof(path)) return 2;
    FILE *in = fopen(path, "rb"); original = malloc(RAM_SIZE); ram = malloc(RAM_SIZE);
    if (!in || !original || !ram || fread(original, 1, RAM_SIZE, in) != RAM_SIZE || fgetc(in) != EOF) return 2;
    fclose(in); memcpy(ram, original, RAM_SIZE);
#ifdef ANIMATION_DMA
    in = fopen(ROM_FILE, "rb");
    rom_size = ROM_BYTES;
    rom = malloc(rom_size);
    if (!in || !rom || fread(rom, 1, rom_size, in) != rom_size || fgetc(in) != EOF) return 2;
    fclose(in);
#endif
    checked(uc_open(UC_ARCH_MIPS, UC_MODE_MIPS64 | UC_MODE_BIG_ENDIAN, &vm));
    checked(uc_ctl_set_cpu_model(vm, UC_CPU_MIPS64_R4000));
    checked(uc_mem_map_ptr(vm, 0, RAM_SIZE, UC_PROT_ALL, ram));
    if (KEEP_CLOCK_MODE && r16(A_TTC_SPEED_SETTING) != 2) {
        fprintf(stderr, "natural-RANDOM evaluator requires an already-RANDOM snapshot\n"); return 2;
    }
    uc_hook hook; checked(uc_hook_add(vm, &hook, UC_HOOK_BLOCK, (void *)block, NULL, 1, 0));
    hook_point(A_RANDOM_U16); hook_point(PC_AIR_EXIT); hook_point(RETURN_SENTINEL);
    if (trace_enabled) hook_point(PC_RNG_EXIT);
#ifdef ANIMATION_DMA
    hook_point(ANIMATION_DMA);
#endif
    for (unsigned i = 0; i < sizeof(path_points)/sizeof(path_points[0]); ++i) hook_point(path_points[i].pc);
    floor_anchor = r32(A_MARIO_STATES+0x68);
    for (unsigned i = 0; i < 3; ++i) positions[i] = r32(A_MARIO_STATES+0x3c+4*i);
    for (unsigned i = 0; i < 2; ++i) cog_yaws[i] = r32(A_OBJECT_POOL+(i?32:29)*0x260+0xd4);
    printf("seed,status,complete_updates,rng_calls,final_seed,rng_hash,reason,pc,dma_calls\n");
    for (unsigned seed = first; seed < first+count; ++seed) {
        memcpy(ram, original, RAM_SIZE); setup_cpu();
        unknown = rejected = draws = dma_calls = rng_pending = 0; reason = "none"; draw_hash = 14695981039346656037ULL;
        if (!baseline) {
            w16(A_RANDOM_SEED16, (uint16_t)seed);
            if (!KEEP_CLOCK_MODE) w16(A_TTC_SPEED_SETTING, 2);
        }
        unsigned input_seed = r16(A_RANDOM_SEED16), complete = 0;
        while (complete < horizon) {
            trial_update = complete;
            pedro = frame_done = 0; cog_updates[0] = cog_updates[1] = 0;
            run(start->entry);
            if (unknown || rejected || !frame_done) break;
            ++complete;
            if (complete < horizon) { next_frame(); if (unknown) break; }
        }
        printf("%u,%s,%u,%u,%u,%016llx,%s,%llx,%u\n", input_seed,
            unknown ? "unknown" : rejected ? "rejected" : "survived", complete, draws,
            r16(A_RANDOM_SEED16), (unsigned long long)draw_hash, reason, (unsigned long long)reg(UC_MIPS_REG_PC), dma_calls);
        if ((seed-first)%4096 == 0) { fflush(stdout); fprintf(stderr, "evaluated %u / %u seeds\n", seed-first+1, count); }
    }
    if (argc > 7) {
        FILE *out = fopen(argv[7], "wb");
        if (!out || fwrite(ram, 1, RAM_SIZE, out) != RAM_SIZE || fclose(out)) return 2;
    }
    checked(uc_close(vm)); free(ram); free(original);
#ifdef ANIMATION_DMA
    free(rom);
#endif
    return 0;
}
