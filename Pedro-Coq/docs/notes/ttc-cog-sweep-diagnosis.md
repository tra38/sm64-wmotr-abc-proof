# Why did both seed sweeps stop at three updates?

Investigated 2026-09-23 for US/JP at decomp pin
`9921382a68bb0c865e5e45eb594d9c64db59b1af`.

**Three is not a general stillness limit. The comparison with the video used
different success conditions and radically different preparation coverage.**
Our sweeps require both cog slots 29 and 32 to keep their yaws fixed. The
video's graph and probability argument concern one cog. Neither sweep varies
all other objects' initial timers and phases. Reporting the maximum without
making these distinctions prominent invites an incorrect comparison.

The [video review](ttc-cog-video-rng-sequence.md) already noted the one-cog
versus two-cog distinction. Reinspection of the supplied clip's opening
captions and graph around 6:27 confirms that wording. The graph reports
streaks found while advancing simulated game time, which changes the whole
state. It is not an enumeration of seeds with all non-RNG state held fixed.
Its original simulator and game version remain independently unverified.

## A controlled diagnostic exceeds three

The new [diagnostic driver](../../instrumentation/ttc-cog-random-seed-sweep/diagnose.py)
replays the longest seeds from each prior family: 37 STOPPED-derived seeds
at snapshot 0 and 25 actual-RANDOM seeds at snapshot 836, in each version.
It uses a 20-update diagnostic horizon and compares three acceptance criteria:
the original two-cog predicate, lower-cog yaw alone, and upper-cog yaw alone.
Single-cog diagnostics do not require Mario preservation. They retain the
same initial game state, seed, input and actual executed game code. They do
not freeze, reposition or edit the other cog; they simply allow it to move.

| Family and seed | Both cogs fixed | Lower cog only | Upper cog only |
| --- | --- | --- | --- |
| Captured RANDOM, seed 13372 | 3 | **4** | 3 |
| Captured RANDOM, seed 48274 | 3 | 3 | **5** |
| Historical STOPPED-derived, seed 32 | 3 | **5** | 3 |

Counts are complete stationary updates before the selected cog moves. US and
JP agree. These are examples from a deliberately small selected sample, not
exhaustive single-cog maxima. They are also not Pedro-hold witnesses: movement
of the other cog may invalidate the spot. Determining whether that movement
is geometrically harmless requires the complete collision and action path.

All 124 original two-cog sample replays reproduce their prior CSV results.
Detailed tracing gives identical status/count/draw fingerprints to tracing
disabled for the selected examples, and matches all 14 ordered RNG calls in
the independently recorded three-update RANDOM baseline in each version.
The two single-cog variants of the RANDOM sample have no unknown results.
The historical upper-only sample has one unknown per version, seed 828,
after three completed updates: it reaches unsupported OS/device I/O. Those
are not counted as failures and did not occur in the original two-cog sweep.
The [metadata receipt](ttc-cog-sweep-diagnosis-results.json) retains these
statuses, sampled seeds, relevant cog draws, outcomes and trace hashes.

## The actual fourth-update failure

For the captured RANDOM phase, seed **48274** executes this sequence:

| Update, zero-based | Lower magnitude draw and next target | Upper magnitude draw and next target | Result |
| --- | --- | --- | --- |
| 0 | 43505, divisible by 7: zero | 27377, divisible by 7: zero | Both still |
| 1 | 45045, divisible by 7: zero | 62979, divisible by 7: zero | Both still |
| 2 | 38411, remainder 2: -400 | 33390, divisible by 7: zero | Both still this update |
| 3 | No new lower-cog draw; existing target accelerates it to -50 | 56364, divisible by 7: zero, if execution continues | Lower yaw moves; upper still |
| 4 | Lower continues moving | 4740, remainder 1: +200 | Upper still this update |
| 5 | Lower continues moving | Existing target accelerates upper to +50 | Upper yaw moves |

Each magnitude selection also consumes its sign draw. The original two-cog
check rejects during update 3 when lower yaw changes from 45000 to 44950.
The upper-only diagnostic continues the same execution and accepts five
complete updates before upper movement in update 5. Thus the earlier rejection
is not a hidden three-frame horizon, missing sign draw, or rejection merely
because a nonzero target was selected. The other-cog checks actually matter.

## Why the same maximum is unsurprising, without assuming it is a theorem

Both families guarantee the first stationary update from their incoming cog
speeds and zero targets. Extending the hold then requires favorable magnitude
selections for **both** cogs. As a rough independent-uniform approximation,
that is about `1/49` per extension instead of `1/7` for one cog. The two sign
draws do not add success conditions; the two different magnitude draws do.

Applied heuristically to 65,536 seeds, that approximation predicts about
`65536 / 49^2 = 27.3` seeds reaching three stationary updates and only
`65536 / 49^3 = 0.56` reaching four. This is intuition about scale, not an
independence proof, a distribution guarantee or a TTC impossibility argument.
The real deterministic seed/call correlations must still be executed.

The exact counts are different despite the shared maximum:

| Milestone | Historical STOPPED-derived seeds, per snapshot/version | Captured RANDOM seeds, per version |
| --- | --- | --- |
| At least 2 complete stationary updates | 1,329 | 1,351 |
| At least 3 | 37 | 25 |
| At least 4, with both cogs fixed | 0 | 0 |

The earlier three snapshot times had identical short schedules; the corrected
RANDOM phase gives a different distribution. US/JP duplication also does not
supply independent preparations: their logical continuations agree here.

## The video is right about additional combinations

Other objects can consume RNG before or between cog decisions, changing which
values reach each cog. Their timers, action states, positions and activation
conditions create additional possible schedules. Those starting-state
combinations were not enumerated by our seed-only sweeps.

For one fully fixed initial non-RNG state and fixed inputs, however, each seed
already determines those objects' future decisions. More calls do not become
freely selectable extra random variables: they advance the same deterministic
stream. To explore additional combinations we must vary permitted preparations
or controller continuations, and then recompute the whole schedule for each.

The traces show that other draws are included. In the historical seed-32
example, the first complete update makes 63 RNG calls, four from the two
selected cogs and 59 from other consumers. In the captured RANDOM seed-48274
example, it makes seven calls, four from those cogs and three from elsewhere.
Different draw counts and indices really are executed; their existence alone
does not force a four-update two-cog success within either fixed family.

The appropriate next comparison is to identify which cog must stay fixed for
the video's geometry, check whether motion of the other cog preserves the
complete spot, and search a broader explicit family of naturally reached
object phases. Our three-update results neither contradict the video's
reported longer one-cog streaks nor rule out a 1,200-frame preparation. No
Coq theorem or full-game refinement obligation was discharged by this audit.
