# Ink gaps: when they are used, and when they disappear

This is a consolidation of existing evidence, inspected at proof commit
`6fe670624342d5655ca3452ebb62b5ad4de494bd` on
`codex/ssl-pyramid-item-proof`, on 6 October 2026. No gameplay trial, search
or new predecessor generator was added. The source references below use the
stock C in `build/pinned-sm64/src/game`, revision
`9921382a68bb0c865e5e45eb594d9c64db59b1af`, and the actual generated US/JP
Clight registered in the inspected proof repository. The separate decomp
checkout is at `36fbf8d693a9fc2bdec0c77402f8e96d07d2f461`; its guarded TAS
hooks in `level_update.c` are outside this registered stock program and are
not gameplay steps in this argument. The other seven inspected C files
match the pinned copies after line-ending normalization. Existing proof
audits and receipts retain their own snapshots. The requested bounded Coq
fallback/contact supplement is documented separately below; chronology
receipts alone do not become an all-history execution theorem.

**A gap can do its job and then disappear in the same update.** All three
supplied JP controls demonstrate this. Collision records low warp contact,
geometry obtains a high floor, the warp is accepted, and the disappeared
action aligns Mario to that floor before the final platform query. By the
next complete boundary the positions agree. The retained platform pointer,
rather than the original position gap, then carries the effect into Area 2.
No reviewed receipt establishes a clean approach that creates and transports
this useful combination to the warp.

## Three records, three differences

M, C and D mean movement, collision and display **Y**. XYZ are tracked
separately whenever contact, movement or querying is involved. Differences
below are real-number differences between the stored binary32 values, not
claims about executing an additional floating-point subtraction.

Let `H = 1938.8648681640625`, the checked timer-131 top height. The controls
share X/Z `(-2200,-1024)` in all three records, idle entry, depth zero and a
cleared remembered platform. The retail fixture patches XYZ and clears the
platform; idle is inherited from the game and depth zero is observed. The
Wafel recipes separately patch action/depth. Neither supplies derived
gameplay access to the unusual pose.

| Supplied control | M / C / D | D−C | M−C | D−M |
| --- | --- | --- | --- | --- |
| Original | 768 / 768 / H | 1170.8648681640625 | 0 | 1170.8648681640625 |
| Variant | 1861 / 768 / 768 | 0 | 1093 | −1093 |
| Hybrid, additional control | 1861 / 768 / H | 1170.8648681640625 | 1093 | 77.8648681640625 |

These controls are neither an exhaustive installer classification nor
uninterrupted controller-reached states. Their gap sizes are examples, not
universal minimum thresholds.

| Writer | Effect, under its receiver/storage conditions | What disappears; what can transfer |
| --- | --- | --- |
| Ordinary display refresh | D := M | D−M becomes zero; D−C becomes M−C. Collision can still be low. |
| Ordinary raw collision copy | C := M | M−C becomes zero; D−C becomes D−M. A raised display can remain. |
| Failed-first-floor fallback | M := D | D−M becomes zero; M−C becomes D−C. The raised coordinate can now feed the real retry. |
| Quicksand sink | D := binary32(D − depth) | Negative depth can enlarge both display differences without moving M or C. |
| Stopping floor alignment | M := cached floor height, then D := M | The chosen floor replaces M and D. The later raw copy can transfer it to C. |

An overwrite is therefore not necessarily an undo. In particular, Original
loses D−M through the very copy that makes its second query useful.

## The actual order and the positions each check consumes

C references are relative to `src/game/`; generated references are relative
to `generated/`. US/JP have the same decisive ordering unless noted.

| Phase | Read or write | Source reference |
| --- | --- | --- |
| Terrain/object work, then earlier platform apply | Cached platform can move State M; the complete ordinary platform phase preserves C and D. | `object_list_processor.c:654`; `platform_displacement.c:72–171` |
| Object contact detection | Raw Object C XYZ and hitboxes determine overlap; collided pointers/types are cached. This is earlier than geometry and action movement. | `object_collision.c:25–55`; `object_list_processor.c:658` |
| Mario geometry preparation | Wall corrections and the first floor query read M XYZ. Only a null first floor copies D XYZ into M and retries. Floor success alone does not land Mario. | `mario.c:1318–1329`; US `us_mario.v:7079–7165`, JP `jp_mario.v:7029–7115` |
| Warp interaction | Uses the cached collision contact, subject to actual action/interaction gates. Acceptance sets `ACT_DISAPPEARED`, argument `0x40002`. Setting that action does not itself copy the positions. | `mario.c:1376,1705–1707`; `interaction.c:403,855–896,1789`; US/JP `*_interaction.v:5654/5646` |
| Interaction short circuit | A successful handler breaks the interaction-handler loop. It does not return from the complete Mario callback. | `interaction.c:1794–1816`; US/JP `*_interaction.v:11008/10912` |
| Action execution | With nonnull floor, the newly selected disappeared action executes in this same update. A null floor returns from the action helper, not from the outer callback. | `mario.c:1710–1736`; US/JP `*_mario.v:9447/9393` |
| Disappeared action and floor alignment | Animation call, then `stop_and_set_height_to_floor`: M.Y takes cached floor height, D XYZ takes M XYZ; angle/render/countdown tails follow. | `mario_actions_cutscene.c:430–440`; `mario_step.c:223–233`; US/JP step `:1741–1769/:1780–1808` |
| Post-action effects and ordinary raw copy | Sinking and other action tails precede the callback's `copy_mario_state_to_object`. In the canonical branch C XYZ takes M XYZ. | `mario.c:1749` onward; `object_list_processor.c:224–237,267–289`; US/JP object processor `:1690/:1689` |
| Remaining callbacks, unloading, final platform selection | `update_mario_platform` queries raw C XYZ. It installs the returned floor's owner only when the absolute difference between saved raw Y and returned height is strictly less than four units. Display is not this query's coordinate. | `object_list_processor.c:662–670`; `platform_displacement.c:31–64`; US/JP platform `:548–595/:547–594` |
| Delayed transition and first Area-2 apply | Object updates finish before warp initiation. These two NULL-callback change-area countdown frames have no object update; other callbacks can update objects. Area entry/reinitialization precedes Area-2 objects; JP retains the platform pointer, while US spawning clears it. | `level_update.c:981,989,875–880,974,463–471,389–390`; `object_list_processor.c:460–465` |

Detecting contact, accepting the warp, selecting a floor, capturing its owner,
retaining that pointer and applying its old displacement are distinct events.
Low C at the contact check does not force low C at the final query. The
ordinary same-sample null-selection theorem explicitly requires State at
selection to equal the collision sample; these controls violate that
condition. Applying it here would assume away the tested mechanism.

## What happens inside each supplied installation update

The three emulator logs are `build/concrete-ink-backward/` directories
`emulator-y768.9R0ESh` (Original), `emulator-y1861-low.RjJrb5` (Variant), and
`emulator-y1861.NYCSpS` (Hybrid). `raw.log:309` records their timer-492 initial
boundary; `:310–312` record handler entry, accepted return and disappeared
entry. No ordinary approach to that supplied boundary is claimed.

| Checkpoint | Original M/C/D | Variant M/C/D | Hybrid M/C/D | Useful effect |
| --- | --- | --- | --- | --- |
| Contact sample before geometry | 768/768/H | 1861/768/768 | 1861/768/H | Low C XYZ can register upper-warp contact. |
| Geometry completed / accepted warp | H/768/H | 1861/768/768 | 1861/768/H | Original: first query misses, D→M retry selects top. Others: first query already selects top; D is not read by fallback. |
| After disappeared stopping copy | H/768/H | H/768/H | H/768/H | The cached high floor now becomes M and D; C is still the earlier raw record at this cut. |
| After ordinary raw copy / final top query | H/H/H | H/H/H | H/H/H | C becomes high, enabling the four-unit capture test. The warp has already accepted. |
| Next complete boundary, timer 493 | H/H/H | H/H/H | H/H/H | Original gaps are gone; the captured top pointer remains. |

At M=1861, the top is eligible through the floor query's 78-unit buffer. M is
still about 77.864868 units below it. That does not meet the final four-unit
platform guard. The later **disappeared floor snap**, rather than query
success alone, supplies the exact high position used for final capture.

For Original, the fallback is the first D−M eraser. It preserves the useful
effect as M−C. The raw copy later erases M−C and D−C, after warp acceptance
and the high geometry query. For Variant, geometry leaves its initial three
differences intact; floor alignment replaces low D with high D and increases
M to H. Its original negative D−M is removed, while D−C becomes H−768.
The raw copy then removes both collision differences. Hybrid follows the
Variant floor route; its raised D is unnecessary for that first query.

The three logs' `:358/360`, timer 515, observe the first Area-2 apply using
the old top slot 61, now inactive, action 2, object timer 1. M XYZ changes
from `(0,5500,256)` to `(365.5927734375,5500,-1096.8026123046875)`; C and D
remain the spawn XYZ at that apply-return cut. At timer 516 (`:362`), all
three agree at the displaced point and the platform clears. `:389` records
Area 2, the apply observations and zero A counters.

These are **useful within the same update despite disappearing before its
end**, with **zero complete updates of the supplied entry split** observed
after installation begins. Pointer retention is a different lifetime:
separate neutral Wafel controls in `20261002-expanded/retention-controls.json`
record 22 Area-1 retained polls and successful first Area-2 displacement.
Those polls are not 22 updates of gap survival.

The emulator lifecycle uses a pillar-completion grant once at timer 360 and
one pose boundary at 492, with no later pose patches/restores. Before Area 2
the suffix is neutral, A released. It uses stick `(-127,-96)` at timers
516–575, then neutral. These are conditional lifecycle diagnostics, not a
patch-free controller route from accepted SSL entry. The exact checked
controls authenticate their fixtures, not every sampled input in Wafel's
installation-prefix frame contract.

## Producer lifetimes and approach opportunities

### Floor alignment and the stopped crawl/slide lead

An accepted ground quarter sets M and the remembered floor to H. Its normal
display refresh sets D=H. A later alignment to that same cache therefore
creates no D−M gap. It can leave M−C until the raw copy; warp interaction
has already run before this action. This is a scoped zero-display-gap result,
not an exclusion of every earlier contact/high-floor combination.

Stopped crawl is different. At its reached refresh, records are
`M=M0, C=Cold, D=M0`. The later remembered-floor snap gives
`M=Hcached, C=Cold, D=M0`. It creates D−M=`M0−Hcached`, while M−C becomes
`Hcached−Cold` and D−C stays `M0−Cold`. The stopped quarter's low local query
answer **does not install a new low cache**; the accepted cache stores were
skipped. The cache needs an earlier, legitimate writer.

`InkStoppedCrawlAlignment.isca_real_ground_result_two_reaches_alignment`
connects the actual return and speed guard to this snap. The final matrix
pointer assignment preserves the positions, but the preceding ten matrix
helper calls and remaining animation/sound/action tail are not composed into
a full frame. The first actual later eraser inside that suffix is therefore
not yet identified. If the split reaches C:=M unchanged, that copy removes
M−C but leaves the raised display as D−C=D−M; a next fallback could consume
it before the next ordinary display refresh. This is a possible continuation,
not proved survival through one complete update.

Creation is after the current warp check. It cannot retroactively affect
that check. A useful later check requires deriving cached height, the actual
wall/ceiling/water exit, XYZ motion, matrix/action tail, next floor miss and
cached contact. No reachable maximum or approach window is established;
crouch slide needs its own intervening-caller proof. **Unresolved.**

References: `mario_step.c:270–304,339`; `mario_actions_moving.c:88–91,1278–1291`;
`InkFloorProducerEffect:33,146`; `InkGroundReturnFrame:460`;
[stopped-floor report](ink-stopped-floor-producer.md).

### Platform application before collision

The full platform phase can change M XYZ before contact while preserving
C/D XYZ in the ordinary Object pool. From `M0/Cold/Dold` to
`M1/Cold/Dold`, D−C is unchanged, M−C becomes `M1−Cold`, and D−M becomes
`Dold−M1`. Collision then reads low C; geometry reads changed M. **This phase
is early enough in principle** to supply the Variant kind of split before
warp acceptance, without needing to retain it to update end.

The actual translation adds only X/Z velocity. The proved nonrotating tail
adds zero new Y under its reached local-Y and rotation-test conditions. A
rotating phase needs real platform ownership, live angular velocities,
matrix inputs and complete movement/query/contact geometry. Tox Box face
animation alone does not set the rotation-speed fields this helper reads.

In 56 of the 68 supplied dialog-support continuations, real platform apply
moves M horizontally while raised D survives. Its detected new vertical
movement is zero. Geometry still finds a floor and the display refresh
erases D−M during that same release update. No useful completed approach
update is demonstrated. Generic rotating support remains **unresolved**;
the specified nonrotating vertical contribution is locally proved zero.

References: `InkPlatformMovement:315`; `InkPlatformProducerHeight:344`;
`platform_displacement.c:107–121,160`; [four-producer report](ink-concrete-producers.md).

### Fresh bounce, later flight and knockback

The first bounce snap writes M:=binary32(actorY+liveHeight), with C/D
unchanged under the actual classifier-to-snap receiver/storage frame. With
incoming M0, its new M−C is `snap−Cold`, D−M is `Dold−snap`, and D−C is
unchanged. The local actual-read theorem bounds **new upward M rise** by
251 under finite/ranged values, live height at most 250, actual completed
classifier/handler calls and separate State/enemy storage. It neither bounds
an inherited total split nor establishes that height ceiling for every actor
history. Chosen cloned XYZ/HOLP does not grant arbitrary live dimensions.

Warp's handler row precedes the bounce rows. An accepted warp breaks the
handler loop before a fresh bounce in that pass; an earlier fresh bounce has
no second warp check before the raw copy. A completed air step refreshes
D:=M even with internal floor failure, erasing D−M but leaving M−C at its
copy cut. The later mandatory C:=M removes M−C. This completes before the
next ordinary collision check under the specified callback/tail frame.

Therefore the **fresh bounce M−C alone** is erased before a later warp check
can consume it in this ordinary completed-callback case. This is an ordering
exclusion, not merely a short lifetime. It does not exclude inherited D
gaps, nonzero particle effects, later object writers, changed contacts or a
different action/copy history. Dry damage has no direct Y placement; its
later movement and copies need their own actual continuation.

The finite bounce receipt supplies 16 synchronized contact poses; 12 bounce.
All 384 complete boundaries over 24 neutral/A-released updates per trial
have M=C=D. Highest detected end-update collision gap is zero; no subframe
peak was measured. Clear-air arithmetic peaks of +128 or +840 are altitude,
not surviving position separation or a universal flight maximum. No approach
window to Ink is established by this receipt.

References: `interaction.c:89,102–105`; `mario_step.c:651–654`;
`InkBounceLiveReadBoundary:43`; `InkAirReturnFrame:275`;
`InkMarioRawCopyCall:118`; `InkMarioZeroParticleTail:152`;
[collision lifetime](ink-bounce-collision-lifetime.md) and
[live-height reads](bounce-live-height-read-connections.md).

### Negative-depth dialog accumulation

After action execution, a real sink changes D to binary32(D−depth), leaving
M/C under its explicit optional-matrix and receiver/storage conditions.
Retained negative depth can accumulate display height during stalled
automatic dialog without the ordinary action refresh. Dialog also skips
the interaction-handler loop, so a large gap during the stall does not yet
mean warp acceptance.

The exact-chain theorem composes N **real sink calls** with retained storage;
it does not manufacture N complete scheduled gameplay updates. From D=768,
retained depth −4 gives D=1936 after 292 calls and D=1940 after 293 calls.
There is no proved gameplay maximum under a granted negative seed. The
accepted classified no-A history contract separately excludes upward sinking;
complete seed-reachability coverage remains open. Temporary negatives clamped
before a usable sink are not useful seeds.

The largest reviewed detected gap is **1834**, from the supplied trial
`k3-t41-p0`: all records start at `(-1334.66663,105,-4820.3335)`, depth −0.5;
3668 real sinks make D.Y=1939 at release timer 4070, while M/C.Y remain 105.
Platform apply then changes movement Z from −4820.3335 to −4756.3335 before
the first ordinary D:=M copy at that same timer. This is accumulation over
3668 sink calls, not a lifetime of a fixed 1834-unit gap. The released gap
survives **zero complete ordinary continuation updates**.

The top-supported trial `k2-t130-p0` starts synced at
`(-2200,1899.65039,-1024)`, accumulates 79 sinks, and releases at timer 570
with D.Y=1939.15039. Actual platform movement yields
`(-2181.51172,1899.65039,-961.052002)` before geometry; the first floor query
succeeds and the same update refreshes display. All 68 trials reset on their
first release update and find floors across their 6120 continuation updates.
They grant an additional dialog/support checkpoint, not just a valid reward
and negative seed. No uninterrupted controller-reached approach is recorded.

A first-floor miss could consume raised D **before** that refresh, as
Original demonstrates conditionally. None of these 68 continuations supplies
the required floorless actual XYZ, low cached contact, display and top timing
together. This producer is **persistent during specified stalled sink
sequences**, but its useful release/approach continuation is **unresolved**.

References: `mario.c:1545–1553,1749`; `InkQuicksandExecution:83`;
`InkQuicksandProducerSize:81,126,191`; `InkDialogInteractionGate:95`;
`InkPostDialogGroundReset:153`; `instrumentation/jp-dialog-support-search/`
`expected-results.json` and `expected-traces.json.gz`;
[support interpretation](ink-stopped-floor-producer.md#how-large-bounds-versus-detections).

## Other refresh/helper results do not become global exclusions

Ordinary ground/air D:=M copies and the non-ejecting Tweester copy erase
D−M at their proved completed cuts, including an internal missing-floor
result. They can leave M−C. Shell refresh-then-offset gives D−M of 45 grounded
or 42 airborne in its scoped caller case; repeated calls reset before adding,
and C:=M does not erase that small display offset. Early shell cancellations
can preserve an inherited gap without creating a larger one. Water, ledge,
cannon, visual anchors and other-context catalog entries retain their existing
scoped bounds/availability/helper labels; none supplies a measured approach
window merely by existing elsewhere in the game. See
[gap comparison](ink-gap-backward.md) and [shell review](shell-gap-investigation.md).

The mandatory raw-copy proof uses canonical global/object identities,
readable State Y and valid separate pool storage at the **reached copy cut**.
The callback-return frame further requires the **actual caller-local particle
mask to be zero**, not just a measured MarioState particle field of zero.
Nonzero spawn effects and later callbacks remain outside that tail theorem.
The air return frames its own real angle/return/free suffix, not every later
action call. None of these premises is silently promoted to every-history
coverage.

## Coq supplement: fallback and cached warp contact

The completed copy was already proved. The new connection composes that
copy with the **actual completed `find_floor` execution**, its resolved list
calls and the following floor-height store, and derives preservation of the
Object pool and named contact cells. It does not assume those calls harmless.

| Phase / condition | M / C / D consequence | Cached contact consequence | Evidence kind |
| --- | --- | --- | --- |
| Earlier object collision | Contact samples raw C XYZ before the nonterrain/Mario phase. | Detection fills raw collision types/count/list. | Exact generated sequence and field/getter certificates; a complete detection-to-copy execution is not constructed here. |
| First floor query, after wall corrections | Actual query leaves stored M XYZ unchanged. | Completed call and height store preserve Object pool and State contact cells. | New real-call frame, independent of floor success. Earlier wall calls remain outside this frame. |
| Taken fallback copy: Original | 768/768/H → H/768/H; D−M becomes0, M−C becomes H−768, D−C unchanged. | Cache present at copy cut is unchanged. | Completed full-coordinate copy reused; new retry/contact frame. |
| Taken fallback copy: Variant | 1861/768/768 → 768/768/768; all three Y differences become0. | Existing cache is unchanged; low destination does not generate new contact. | Conditional on actually taking fallback. The successful Variant receipt bypasses it. |
| Taken fallback copy: Hybrid | 1861/768/H → H/768/H; D−M becomes0; high movement/collision difference remains. | Existing cache is unchanged. | Conditional on actually taking fallback, unlike its recorded first-query success. |
| Actual second query and height store | Copied M XYZ remains D's original XYZ; lookup does not normalize it. Floor pointer/height and named floor counters/flag can change. | Entire Object pool and State contact cells120/128/164 remain unchanged through this segment. | New composed real execution, including local allocation/free and list-call effects. |
| Later interaction pass | Reads the cached type mask imported before geometry and an object pointer from the cached list; fallback itself does not detect a new contact. | Eligibility, object identity/type/status and actual handler dispatch still need their reached conditions. | Exact generated getter/caller/handler source plus existing local nonfading acceptance theorem. Whole supporting-call continuity remains open. |
| Floor-null gate after interactions | If the actual fresh floor read is still NULL, action execution is skipped. A floor found earlier is not a proof of interaction acceptance. | Cached handler acceptance and floor validity are separate. | Exact generated guard/order; bounded execution guard documented with the new theorem below. |
| Later warp scheduling request | If the live delayed operation is nonzero, the complete actual trigger call makes no memory change. | Selecting disappeared does not itself replace an earlier pending death operation. | New completed US/JP guard/call frame; survival of that pending value through intervening execution remains open. |

`InkFallbackContact.ifct_taken_fallback_transfers_display_and_preserves_contact`
produces both the intermediate copy memory and the real retry-return memory.
It frames all Object-pool loads, so C XYZ, the raw contact-type word at112,
count at118 and four cached pointers at120/124/128/132 are protected, as are stored D
coordinates and other enemies' fields. Actual composite checks identify these
offsets; raw position is160/164/168. State contact-type at164 and
interact/used-object fields120/128 are protected separately. This is equality
to the **copy-cut cache**, not an assertion that it is already the original
detection cache.

The conditions remain explicit: selected US/JP global symbols; canonical
MarioState and ordinary Object-pool receiver; slot<240; actual loaded
`marioObj`; all three display loads; no shadowing of the resolved copy/floor
names; and a completed actual taken-retry execution. Separate global symbols
derive State/pool nonaliasing and separation from the three real floor
counter/flag globals. Loaded cells supply block validity; real allocation,
stores, list calls and frees are accounted for. No live floor-list coverage,
returned top, intact platform, fixed action or controller reachability is
assumed as a conclusion.

`ifct_primary_query_preserves_contact` adds the first query's contact frame
with an explicit valid incoming Object-pool block condition.
`ifct_floor_coordinate_casts_are_local` identifies the actual three local
signed-16 casts, and `ifct_completed_local_casts_do_not_write_position` proves
their completed execution changes no memory. The whole floor-call frame
also preserves M XYZ. The signed-16 query sample is not a write of truncated
coordinates back into MarioState. Fallback restores stored D XYZ; it does
not automatically put Mario on a platform, at a portal or in a main universe.

`InkFallbackSourceOrder` verifies the real top-level ordering, the input mask
import, null-guarded copy/retry, cached list getter and its actual caller
arguments, nonfading disappeared setter and interaction-loop break. It
contains no replacement scheduler or idealized gameplay transition. These
source certificates are separate from completed-call memory theorems.

`ifso_reached_null_floor_returns_before_dispatch` additionally constructs
the real post-interaction suffix execution: the selected global MarioState
pointer load and a live null floor load at104 give a zero return with unchanged
memory, bypassing the action loop and remaining action tail. It does not
assume a completed suffix or assume the earlier retry-null value survived;
null is required at this **fresh, later read**.

For a **successful retry**, floor validity alone does not accept the warp.
The actual interaction pass must be enabled (including action tangibility
and collision-type mask), obtain the relevant cached upper-warp object,
pass its status/dispatch gates, choose the nonfading subtype, have action
different from `ACT_EMERGE_FROM_PIPE`, complete sound/riding cleanup, then
reach the real disappeared setter. The existing accepted-tail theorem begins
after that cleanup. Later action execution, capture, pointer retention and
Ink apply remain separate. The fading-warp countdown is not used here.

For a **failed retry**, the real geometry suffix contains a later floor-null
branch requesting operation18 (death), after its ceiling/gas/water work,
before interactions (`mario.c:1336,1365–1366`). The source certificate does
not prove retry-null survives those intervening calls. At zero lives
the scheduler can choose game-over20. This source request is not yet a
completed death-installation theorem. Interactions still precede the fresh
floor-null test: double-null at the retry does not prove the test remains
null after every intervening call. If it is still null at that guard, the
action helper returns before dispatch, even if the interaction selected
disappeared. The outer Mario callback still reaches its ordinary raw copy
under the existing completed-callback conditions.

`InkFailedRetryGuard.ifg_pending_operation_blocks_actual_trigger_call`
proves the actual complete `level_trigger_warp` call is memory-unchanged
when its real signed-short pending-operation load is nonzero. The death/
game-over specialization therefore blocks replacing18/20 with object-warp4
**at that call**. It does not prove the initial latch was empty, install the
death operation, preserve it through sound/interactions/countdown/resets, or
prove which later area transition occurs. This sharpens the older abstract
first-writer latch without pretending its whole-history projection is closed.

The two proposed fallback routes have different verdicts. **Already cached
portal contact followed by useful fallback is not excluded**: Original's
conditional receipt demonstrates that pattern. **Arriving at the portal only
because of fallback does not create a new cached contact during this proved
copy/query segment**; its cache remains what it was. A later detection pass
or another actual contact writer must supply that ingredient. This excludes
fallback as the sole new-contact writer, not every subsequent approach or
all Ink installations. Death-preemption across the full failed-retry history
remains conditional on the named missing connections above.

## What the backward and approach receipts actually establish

The supplied final-dialog countercheck inherits Variant's split and automatic
dialog state 24, depth zero. After its first complete update,
M=C=1861 and D=768; after its second, all equal 1935.7481689453125. It measures
**one complete update of an inherited M−D difference**, but zero complete
updates of the low C needed for that Variant. Neutral/A-released replay for
24 updates never accepts the warp or enters Area 2. This is not a discovered
gap producer.

The 146 actual unequal-parent suffixes use one earliest patch and no
intermediate patch/restore. All 123 ground/freefall proposals inherit raw
`(-2200,768,-1024)` and accept the warp on their first update, before ordinary
movement; none of the 23 dialog proposals does. Sixty-five record a null
floor and cached −11000 at the failed parent checkpoint, but the diagnostic
has no dedicated death classifier; missing
floor is not a measured count of deaths. Forty-seven capture/retain the top
at later Area-1 polls, but none obtains the checked Area-2 displacement. The
exact pointer effects inside unloading/entry are not observed by this test;
it does not show those pointers disappearing in Area 1.

The later ten-minute finite search tries 20,770 earlier proposals, including
1311 synchronized starts, and accepts no extension. Its strongest validated
chain remains the supplied installation update. This excludes only the tested
continuations. No number of empty samples proves missing generators or all
legal histories impossible. The current audit adds no new runtime trial.

Approach evidence must contain actual XYZ motion, action/timer, velocity,
controller-edge history, cached contacts, floor/owner/platform and lifecycle.
The existing receipts record those fields for their selected supplied
contexts; they do not authorize arbitrary repositioning between checkpoints.
US entry clearing and JP old-slot retention are distinct. A usable global
no-Ink result still needs every surviving producer and pointer continuation
covered or excluded under an explicit accepted contract.

## Checked supplement and validation

The normal discipline audit `build/audit/20261006-162221-k7hku8rg/report.json`
passes all 13 checks: compilation, source inventory, proof-hole and link
discipline, eight selected assumption checks and integration. There are 652
registered sources, 480 of 574 proof modules in MainTheorem's import closure,
94 standalone-only modules and zero reported problems. The existing backward
boundary has nine allowed foundations; the new fallback boundary has seven.
These counts do not discharge the explicit gameplay conditions above.

Four new modules are registered and connected through
`InkFallbackBoundary` and `InkBackwardHistory` to
`MainTheorem.current_ink_fallback_contact_boundary` and the existing backward
boundary. The new progress is the actual floor-call/contact frame and reached
null/pending guard executions, rather than another isolated copy proof.
The source-order certificates remain distinct from those execution claims.
The pipeline uses the `sm64-item-proof` switch, Coq 8.16.1 and CompCert 3.15,
with its established memory limit unchanged.

The existing receipt checker was rerun over the three exact retail logs;
all three pass. The offline readback and normalized source hashes are in
`build/audit/ink-gap-lifetime-20261006/receipt-reread.json`. This is verification
of saved observations, not a new game run. No broad search, runtime trial or
new predecessor generator was launched. Atlas estimates remain unchanged.

## Compact verdicts

| Case | Classification and complete-update count | Has a useful check already consumed it? | Established approach / scope |
| --- | --- | --- | --- |
| Original control | Useful inside installation update; supplied entry split survives 0 complete updates afterward. | Yes: low contact, D→M retry and high floor, then top capture after C:=M. | Exact supplied JP runtime success. No clean creation/approach window. |
| Variant control | Useful inside installation update; supplied entry split survives 0 complete updates afterward. | Yes: low contact, high first query, then disappeared alignment before final capture. | Exact supplied JP runtime success. D=768 is not a graphical contact requirement. No clean creation/approach window. |
| Hybrid control | Same-update useful; 0 complete entry-split updates afterward. | Yes; first query uses high M, so raised D is unnecessary there. | Additional conditional control, not a separate reached route. |
| Accepted ground refresh/alignment | D−M erased at refresh; M−C may remain until raw copy. | Current warp check precedes creation; no later warp pass before copy. | Scoped local display-gap result; no whole-family exclusion. |
| Stopped crawl / slide | Unresolved after first remembered-height snap; no full-update survival count proved. | Not current warp check. A next retry might consume transferred display effect if it survives. | Cache provenance, matrix/action tail, next XYZ/floor/contact missing. |
| Platform apply | Same-update interval early enough in principle; full-update persistence unresolved. | Collision and geometry follow before ordinary copies. | Specified nonrotation adds 0 Y; live useful rotation/support history open. |
| Fresh bounce collision gap | Erased before a later warp check in the specified completed-copy/zero-mask callback. | No second warp check between fresh bounce and copy. | Scoped ordering obstruction; inherited display/late writers outside scope. Measured end-boundary gap 0 in 384 supplied checks. |
| Negative-depth dialog | Accumulates through retained real sinks; released gap lasts 0 complete updates in 68 trials. | Dialog gates interactions; a release retry could use D, but all sampled first queries succeed. | Maximum detected 1834; no gameplay maximum, clean seed or useful release approach. |
| Supplied final-dialog countercheck | Inherited M−D survives 1 complete update; low C survives 0. | No: low C lost while dialog prevents interaction. | One specific 24-update replay, not all dialog histories. |

For **Original**, the raised display must exist when a first actual floor
query fails, with low contact already cached and the top eligible on retry.
Fallback removes the display/movement difference by putting its height into
movement; later raw copying removes the collision split. It has already done
its job in the supplied JP lifecycle. A clean approach window is unknown.

For **Variant**, high movement and low collision must coexist when contact
is sampled and geometry queries the top. No raised display is required. The
accepted disappeared action then snaps to the cached top, refreshes display,
and the raw copy raises collision for final capture. Those overwrites help
installation rather than refute it. The exact supplied test works; no
controller-reached creation or approach length is established.

The precise open question is **creation early enough for the relevant
consumer**, followed by the required owner/lifetime continuation. A subframe
lifetime alone is not an exclusion. This audit consolidates local proofs,
conditional installation receipts and finite failures; it does not close Ink
or either star route.
