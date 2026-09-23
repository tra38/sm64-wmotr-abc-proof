# F02: the chosen warp-acceptance checkpoint

The user has fixed the target: movement, collision and stored display
positions disagree immediately after the upper SSL warp is accepted,
while Mario is still in Area 1. The purpose is to test an Ink installation.
Arrival in Area 2 is not the chosen checkpoint. This records the claim and
its completion criteria; it is not a new proof or route closure.

## The exact claim

Can an allowed no-new-A continuation reach the return of the accepted
upper-warp interaction with Mario's three stored position vectors not all
equal? Read all three at that one checkpoint: MarioState position, Mario
Object collision position and Mario Object graphical position. This is an
existence question, not a claim that every warp creates disagreement.

In the generated US/JP code, the checkpoint is the successful nonfading
`interact_warp` return for the upper SSL warp, after its call setting
`ACT_DISAPPEARED` with argument `0x00040002`, before the first execution of
`act_disappeared`. The later `level_trigger_warp` call and area loading are
different checkpoints. The disappearing action first stops Mario and
copies the cached floor height into his movement/display position.

The selected start and execution model remain the project's normally
initialized SSL entry and ordinary controller gameplay with no new A press.
US and JP results must be reported separately. For the existing conditional
negative-depth transfer investigation, negative depth and a valid coin/star
opportunity may be granted. That diagnostic does not prove a no-A seed or a
clean route from normal entry. Neither version grants the desired position
split, first floor miss, live top selection, warp acceptance or capture.

## What disagreement means for Ink

The three vectors do not have to be pairwise different. The useful retry
copies display into movement before interaction, so its concrete target at
warp acceptance is movement = display, with collision still at the low warp
contact. For the checked vertical candidate, the desired readings are:

| Position record | Target at accepted-warp return |
| --- | --- |
| Movement | `(-2200, 1938.8648681640625, -1024)` |
| Collision | `(-2200, 768, -1024)` |
| Stored display | `(-2200, 1938.8648681640625, -1024)` |

These are target readings, not a newly recorded handler-return snapshot.
They do not require walking upward after acceptance: the retry is earlier.
A different nonzero gap could satisfy the literal disagreement claim while
being useless for installation, so the result must say which was achieved.

Keep two verdicts separate. The chosen checkpoint tests disagreement after
acceptance. The installation check then follows the rest of that Area-1
update to see whether its final platform query actually captures the useful
top. It does not require the gap to persist afterward. In the existing
supplied JP receipt, the first post-update poll has all three positions
equal at the high point and the top remembered as Mario's platform. Later
synchronization therefore does not by itself refute installation.

## Completion and existing evidence

A positive gameplay result needs a controller-produced predecessor and
same-continuation readings at the specified acceptance checkpoint; it must
not inject the desired split. Report capture separately. If only the agreed
negative-depth/reward grants are used, report a conditional result. A
negative theorem must exclude this checkpoint outcome in its explicitly
fixed domain; a failed finite search or a proved local helper does not
exclude every allowed history. Star collection and Area-2 displacement are
outside this batch's completion criterion.

The existing retry-call and stopping-copy proofs, generated interaction
ordering checks and supplied JP installation receipt are reusable. The
receipt was rechecked successfully while fixing this target: four dynamic
and 26 static floor snapshots, 21 retained Area-1 polls and the first Area-2
effect. It does not record the newly chosen `interact_warp` return itself
or provide a controller predecessor to its supplied setup. No new Coq
theorem, gameplay experiment or counterexample estimate is added here.

Sources: [generated interaction order](../../proofs/Area1InteractionShortCircuitClosure.v),
[generated update schedule](../../proofs/Area1QueryScheduleClosure.v),
[completed retry](../../proofs/InkRetryCallCompletion.v),
[stopping copy](../../proofs/InkWarpStop.v), and
[conditional JP receipt](ink-vertical-installation.md).
