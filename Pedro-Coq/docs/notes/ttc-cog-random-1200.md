# RANDOM-mode 1,200-frame investigation

Checked 2026-09-21 against source
`9921382a68bb0c865e5e45eb594d9c64db59b1af`. Scope is `VERSION_US` and
`VERSION_JP`; experiments labeled US-only below were not independently replayed
in JP.

**The requested 1,200-frame RANDOM-mode preserving RNG strategy remains open.**
The [STOPPED control](ttc-cog-1200-frame-hold.md) cannot simply be transferred
to RANDOM mode: this initialization has already selected nonzero cog targets
before the first controlled update. The tested inputs that preserve the
STOPPED spot change Mario's speed or action, but not the ordered RNG draws.
This is a finite investigation, not an exclusion of other inputs, prepared
objects, entry histories or cog geometries.

## Actual RANDOM-mode continuation

The new `search_edge_a` RANDOM build declares the same initial position
`(1308, -2088, -1088)` and yaw as the stopped diagnostic. The source patch
changes only the established near-cog initialization and clock selection;
its hash is
`16ee9de2548eaf57a07df9cd916cf83b1d4df2c5391f66be84939cd275491f32`.
No cog pose, target, RNG seed or subsequent game state is assigned by the
observer. Both game versions use recorded controller inputs and disabled cheats.

At input snapshot 0, the lower cog (slot 29) and upper cog (slot 32) both
have yaw and speed zero, but their target speeds are **800 and 200**.
Their first observed updates each change speed to **50** and yaw from
**0 to 50**, without an RNG call inside either cog update. Both updates
finish before Mario's action. A new random value during Mario's action
cannot revise the targets already used by those updates.

The full path consequently fails the fixed-cog Pedro check at update 0.
Geometry refresh also finds an actual supporting cog floor. By the entry to
Mario's next action, he has moved to approximately
`(1306.02893, -2088, -1086.3158)` and references slot 29 as his platform.
The two versions agree on all **5,993 normalized observations** over 125
recorded frames. This failed start supplies no RANDOM-mode preserving prefix;
an empty prefix is not reported as a successful RNG comparison.

## Preserving inputs versus RNG control

These comparisons use the earlier STOPPED initialization and its complete
constant-stick control, so both branches of each comparison start with the
same game state. They do not compare a STOPPED seed against a RANDOM seed.

| Input change | Versions checked | Complete preserving prefix | RNG result within that prefix |
| --- | --- | --- | --- |
| Reduce raw stick from `(75,28)` to `(40,15)` at frame 100 | US | 1,200 updates | All 2,104 ordered draws match the control |
| B at frame 4, A at frame 5, then original stick | US and JP | 224 updates | All 391 ordered draws match the control |
| R at frame 4, then original stick | US | 224 updates | All 391 ordered draws match the control |
| B at frame 4, then original stick | US | 5 updates; update 5 loses the spot | The first 10 draws match; later effects are outside the preserving prefix |

The smaller stick ends the long run with forward speed about **31.25314**,
rather than the control's **205.56729**. Thus speed control is real here, but
it does not itself produce RNG control. The R press changes the recorded
camera yaw, but introduces no RNG difference in the checked window.

The B/A path reaches `ACT_DIVE` and close-gap landing on frame 4, then cancels
`ACT_DIVE_SLIDE` into `ACT_FORWARD_ROLLOUT` on frame 5. The rollout includes
a rising air quarter rejected by the ceiling, followed by a close-gap landed
return. Mario stays at the same XYZ at every recorded internal boundary and
the following snapshots. Neither the action exits nor the complete RNG trace
shows a new particle/RNG effect during the preserving window. US and JP agree
on all **10,739 normalized observations**, including the added cog records.

Without A on frame 5, the dive-slide ground step returns wall-stop while
still retaining the distant floor at -8191. Source inspection identifies
the later `align_with_floor` assignment `m->pos[1] = m->floorHeight` in this
path. By complete action exit Mario is at Y=-8191 in `ACT_GROUND_BONK`,
with vertical-star request mask 2. The complete action therefore loses the
spot even though the earlier ground-step boundary did not. A particle request
on this failed update is not a preserving RNG-control witness. This is a
dive-slide failure, not an exclusion of the distinct slide-kick caller.

## Checking the real cog schedule

The optional `--trace-cogs` observer records the entry and return of each
`bhv_ttc_cog_update`, its object slot, current/target speed, yaw, direction,
seed and next RNG-call index. It uses the same loaded-instruction checks and
read-only interface as the existing observer. A replay with this addition
reproduces all **3,007 original control events** after removing only the new
cog records. This checks that adding the observation does not alter that run.

The receipt checker verifies paired calls, the binary32 speed approach,
target selection from both actual draws, yaw change, incoming/following cog
snapshots, and the global RNG sequence. It verifies that all eight cog updates
occur before Mario's action in each observed frame. Slots 30 and 31 execute
between the relevant slots 29 and 32. In the RANDOM trace, that interval has
zero RNG calls on 110 frames and two on 15 frames. Consequently, the old
consecutive-two-cog arithmetic example is not an executed schedule for this
replay. The draw counts are observed facts for these trials, not universal
constants for TTC.

The preserving-prefix checker is separate from the earlier ordinary-air
checker. It permits the rollout's ceiling-rejected rising quarter, while
still requiring a complete action update, off-floor geometry refresh, a
close-gap return between the selected cogs in every accepted update, no
platform, fixed cog poses, and fixed Mario XYZ at all observed helper/air
boundaries and bracketing snapshots. The retained floor pointer and height
must also match the initial snapshot throughout that prefix; this comparison
uses raw per-run pointers before cross-version normalization. It does not certify unobserved
instruction boundaries or establish a Clight/retail refinement. The final
snapshot without a following bracket is never counted as another complete
Mario update.

## Formal boundary

The new proof executes the complete generated cog update with speed and
yaw zero, direction +1, and either target 800 or target 200. Its statement
retains explicit generated-compatible layout, function binding and CompCert
memory premises. It does not assume an RNG oracle or a callee execution.
The proved result is speed, angular velocity and yaw 50, with target and
the disjoint seed cell unchanged. It isolates why these entry conditions
cannot produce the first stationary update, regardless of the seed value.

`TTCCogApproachExecution.generated_cog_approach_departure_with_store` executes
the real helper and proves its false return. The complete caller result is
`TTCCogExecution.generated_cog_departure_update_executes_us_jp`, consumed by
`MainTheorem.checked_ttc_cog_local_mechanism_us_jp`. There is no assumed
helper execution in this new branch. Nonzero floating-point equality uses
CompCert's proved `Float32.of_to_bits` identity; no new arithmetic assumption
is introduced. This extends the capstone's concrete execution coverage to
the observed failing target conditions, without discharging the still-open
preserving-input or reachability obligations.

This is separate from instantiating the memory/layout conditions using the
retail observations, proving the whole object scheduler, reaching another
useful RANDOM phase, or proving a 1,200-frame strategy. Those obligations
remain open. The original zero-speed/zero-target local execution result is
retained; it does not establish a repeated two-cog schedule.

## Reproduction and remaining work

The [receipt builder](../../instrumentation/ttc-cog-geometry/report-random-control.py)
and [results](../../instrumentation/ttc-cog-geometry/results-random-control.json)
retain input, source-patch, ROM, ELF, observer and trace hashes, all relevant
first-failure boundaries, and cross-version comparisons. Raw traces are in
the ignored `Pedro-Coq/build/cog-placement/` tree. The new inputs are
`analog-after100.csv`, `b4.csv`, `b4-a5.csv` and `r4.csv` in the same
instrumentation directory. See its README for commands.

A successful continuation still needs a natural RANDOM-mode cog phase
compatible with the actual collision queries and at least one demonstrated
preserving input choice that changes an accepted RNG draw. Only then can
the actual interleaved schedule be searched and checked through 1,200 complete
updates. Neither condition has been supplied by the experiments above.

Validation passed: the full Pedro proof pipeline, its no-holes check, the
repository discipline audit, Python compilation and the replay receipt
checks. Five negative controls reject damaged host-log copies: wrong cog yaw,
wrong seed, wrong RNG index, a missing cog entry, and a moved following
snapshot. The active capstone's before/after `Print Assumptions` outputs are
identical, containing the same six standard Coq/CompCert assumptions. The
new complete cog-update theorem has that same footprint. This audit says
nothing by itself about gameplay reachability or closing the 1,200-frame goal.

The private site was checked: it remains owner-only, with no external
visitors, and its overall open verdict agrees. Publication of these newer
findings is pending because the required Sites skill/helper bundle is absent;
no site source or access setting was changed.
