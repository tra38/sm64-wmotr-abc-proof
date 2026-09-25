/* Stock callers and display copies, supplied quarter-step outcomes.
 * All unextracted helpers below are explicit test doubles. This cannot prove
 * their frames, collision reachability, or a complete shell gameplay bound. */
#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "sm64.h"
#include "engine/math_util.h"
#include "game/mario.h"
#include "game/mario_step.h"
#include "surface_terrains.h"

static int outcomes[4], quarter, stopped;
static float next_y;
static s32 perform_ground_quarter_step(struct MarioState *m, Vec3f p) {
    (void)p; m->pos[1]=next_y; return outcomes[quarter++];
}
static s32 perform_air_quarter_step(struct MarioState *m, Vec3f p, u32 arg) {
    (void)p; (void)arg; m->pos[1]=next_y; return outcomes[quarter++];
}
u32 mario_get_terrain_sound_addend(struct MarioState *m) {(void)m; return 0;}
void apply_gravity(struct MarioState *m) {(void)m;}
void apply_vertical_wind(struct MarioState *m) {(void)m;}
void update_shell_speed(struct MarioState *m) {(void)m;}
void update_air_without_turn(struct MarioState *m) {(void)m;}
s16 set_mario_animation(struct MarioState *m, s32 a) {(void)m;(void)a;return 0;}
u32 set_mario_action(struct MarioState *m, u32 a, u32 arg) {m->action=a;m->actionArg=arg;return 1;}
void mario_stop_riding_object(struct MarioState *m) {m->riddenObj=NULL;stopped++;}
void mario_set_forward_vel(struct MarioState *m, f32 v) {m->forwardVel=v;}
void play_sound(s32 s, f32 *p) {(void)s;(void)p;}
void play_mario_sound(struct MarioState *m, s32 s, s32 v) {(void)m;(void)s;(void)v;}
void adjust_sound_for_speed(struct MarioState *m) {(void)m;}
s32 lava_boost_on_wall(struct MarioState *m) {(void)m;return 1;}
#include "source_functions.inc"

int main(void) {
    struct MarioState m; struct Object obj, shell;
    struct MarioBodyState body; struct Surface floor;
    const int ground[]={GROUND_STEP_NONE,GROUND_STEP_LEFT_GROUND,
        GROUND_STEP_HIT_WALL_STOP_QSTEPS,GROUND_STEP_HIT_WALL_CONTINUE_QSTEPS};
    const int air[]={AIR_STEP_NONE,AIR_STEP_LANDED,AIR_STEP_HIT_WALL,
        AIR_STEP_GRABBED_LEDGE,AIR_STEP_GRABBED_CEILING,AIR_STEP_HIT_LAVA_WALL};
    const float heights[]={-8192,0,768,1938.8648681640625f,8192};
    unsigned tests=0, early=0; float largest=0;
    for(int mode=0;mode<2;mode++) {
        int n=mode?6:4, count=n*n*n*n;
        for(int code=0;code<count;code++) for(int h=0;h<5;h++) {
            memset(&m,0,sizeof m);memset(&obj,0,sizeof obj);
            memset(&body,0,sizeof body);memset(&floor,0,sizeof floor);
            m.marioObj=&obj;m.marioBodyState=&body;m.floor=&floor;m.riddenObj=&shell;
            floor.normal.y=1;m.pos[1]=768;m.forwardVel=32;
            m.action=mode?ACT_RIDING_SHELL_FALL:ACT_RIDING_SHELL_GROUND;
            obj.header.gfx.pos[1]=10000;next_y=heights[h];quarter=stopped=0;
            int c=code;for(int i=0;i<4;i++){outcomes[i]=(mode?air:ground)[c%n];c/=n;}
            assert((mode?act_riding_shell_air(&m):act_riding_shell_ground(&m))==0);
            assert(quarter>=1 && quarter<=4);
            float gap=obj.header.gfx.pos[1]-m.pos[1];
            assert(gap==(mode?42:45));if(gap>largest)largest=gap;
            /* Repeat with the previous display: no stacking in these callers. */
            quarter=0;m.action=mode?ACT_RIDING_SHELL_FALL:ACT_RIDING_SHELL_GROUND;
            assert((mode?act_riding_shell_air(&m):act_riding_shell_ground(&m))==0);
            assert(obj.header.gfx.pos[1]-m.pos[1]==gap);tests++;
        }
    }
    for(int input=0;input<2;input++) {
        memset(&m,0,sizeof m);memset(&obj,0,sizeof obj);
        m.marioObj=&obj;m.pos[1]=768;obj.header.gfx.pos[1]=813;
        m.input=input?INPUT_Z_PRESSED:INPUT_A_PRESSED;quarter=0;
        assert(act_riding_shell_ground(&m)==1);
        assert(quarter==0 && obj.header.gfx.pos[1]==813 && m.pos[1]==768);early++;
    }
    printf("shell_gap: outcome_sequences=%u, repeated_calls=%u, early_exits=%u, max_gap=%.0f\n",
           tests,tests,early,largest);
    puts("Scope: supplied helper outcomes; no live terrain, no clean route, no Coq promotion.");
}
