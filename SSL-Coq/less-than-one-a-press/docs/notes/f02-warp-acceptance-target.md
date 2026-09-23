# F02: the chosen warp-acceptance checkpoint

The user has fixed the target: movement, collision and stored display
positions disagree immediately after the upper SSL warp is accepted,
while Mario is still in Area 1. The purpose is to test an Ink installation.
Arrival in Area 2 is not the chosen checkpoint. The 23 September batch now
adds a US/JP proof for the final accepted-warp call and a read-only JP replay
at this exact checkpoint. The local proof is complete and this replay fails
as an Ink candidate. The all-gameplay existence question remains open.

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
ordering checks and supplied JP installation receipt remain reusable. That
supplied receipt contains four dynamic and 26 static floor snapshots, 21
retained Area-1 polls and the first Area-2 effect. It still does not record
the chosen `interact_warp` return or provide a controller predecessor. The
new exact-checkpoint observation below is a different, clean replay.

## Proved: the final action-setting call preserves the split it receives

[InkWarpAcceptance.v](../../proofs/InkWarpAcceptance.v) opens the real
generated US/JP `set_mario_action` call for `ACT_DISAPPEARED`. Its selected
cutscene initializer changes no memory. The remaining setter writes only
the State control fields, leaving position storage unchanged. The actual
nonfading warp branch's final call and return therefore neither create nor
erase disagreement among movement, collision and display.

The exact backward statement is
`iwa_acceptance_tail_neither_creates_nor_erases_split`: after a completed
execution of that final tail, the three position records disagree if and
only if they disagreed on entry to the tail. The State pointer and normal
separation of State storage from the Object pool are explicit. No useful
gap, negative depth or position-preserving external-call contract is assumed.

This tail starts **after `mario_stop_riding_object`**. It does not yet frame
the earlier `segmented_to_virtual`, `play_sound` or stop-riding calls in the
whole handler. It also does not prove a controller predecessor, the final
floor selection or platform capture. The backward search has a concrete
cut: any successful candidate must bring its gap to the final action call;
that call cannot supply one. The stronger claim that the whole handler
preserves every position is not being reported as proved.

The result is exported as
`MainTheorem.current_f02_warp_acceptance_boundary` and included in the Ink
backward boundary. This replaces a source-level expectation about the final
call with a completed execution proof. Adding it to the boundary does not
discharge the all-history Ink claim.

## Observed: the clean JP replay has no gap at acceptance

The new [read-only observer](../../instrumentation/jp-warp-acceptance/README.md)
extends the existing zero-A four-pillar controller replay, without injecting
positions, actions, pointers or timing. It preserves the existing Rank-5
and Rank-13 receipts exactly and records all nine position cells at seven
ordered checkpoints in timer 2807, still in Area 1.

| Checkpoint | Movement, collision and display | Action argument | Platform |
| --- | --- | --- | --- |
| Upper-warp handler entry | All `(-2033.87939453125, 768, -1037.05859375)` | `0` | None |
| Successful handler return, before disappearing | Same three vectors | `0x00040002` | None |
| First disappearing-action return | Same three vectors | `0x00040001` | None |
| Final Area-1 platform-query return | Same three vectors | `0x00040001` | None |

The nonfading branch, disappearing-action entry and ordinary-copy return
also have those same vectors. The cached floor exists at height 768 and has
no Object owner. The original top was identified by stock behavior and slot
61 at timer 348; at acceptance no active top remains. Its former slot is
inactive and has been reused. A position-based controller hint is not used
as proof of top identity.

This is a negative result for **this clean JP run**, not an exclusion of
every controller history, a US runtime result or a verified retail-to-Clight
simulation. It does not turn the separate supplied vertical fixture into a
clean route. There is still no clean counterexample or complete impossibility
proof for the fixed question. Atlas estimates are unchanged.

## Validation

The required selected audit passed at
`build/audit/20260923-174608-0567umuq`: 594 registered sources, build and
proof/link checks passing, 424 of 518 proof modules in MainTheorem's import
closure, and 94 standalone modules. The main Ink boundary has nine allowed
foundations; the new boundary and split theorem each have seven. These
counts are hygiene checks, not gameplay coverage.

The live replay is saved under
`build/instrumentation/jp-warp-acceptance/run.hNkR0W/`. Its semantic validator,
exact expected receipt and older Rank-5/Rank-13 receipts pass. Four checker
tests cover the saved observation, bad provenance/checkpoints, missing or
reordered samples, and accepting a test-only different display for reporting.

Sources: [generated interaction order](../../proofs/Area1InteractionShortCircuitClosure.v),
[generated update schedule](../../proofs/Area1QueryScheduleClosure.v),
[completed retry](../../proofs/InkRetryCallCompletion.v),
[stopping copy](../../proofs/InkWarpStop.v), and
[conditional JP receipt](ink-vertical-installation.md). The new proof and
exact-checkpoint replay are linked above.
