# Working backward from Ink: first, make the gap

Updated 24 September 2026. This pass sizes the 20 remaining cases in the
[position-split catalog](position-split-catalog.md). It does not start a
journey to the warp before a candidate can supply the required separation.

## The height we are trying to explain

The successful supplied vertical setup starts with movement and collision at
`(-2200,768,-1024)` and stored display at
`(-2200,1938.8648681640625,-1024)`. Before the first floor query, display is
**1170.8648681640625 units above movement**. This is the target for this sizing
pass, not a proved minimum for every possible Ink installation. After the
retry, movement can join display up high while collision stays low. Those
are different checkpoints; saying that the retry erases the movement/display
gap does not mean that it defeats Ink.

There are two basic ways to make this positive gap: raise the stored display,
or lower actual Mario without replacing that display. We also need collision
to end up low. A later movement-to-collision copy could provide that part,
but only if the display survives until then. Simply lifting Mario in a
Tweester does not establish any of those separations.

## When we count a case as insufficient

For this comparison, a proved upper bound below **1170.8648681640625** earns
**Insufficient — already proved**, with its starting conditions and endpoint
attached. We can finish that conditional case without first proving every
surrounding gameplay history. This closes that way of supplying this setup's
gap; it does not declare the whole mechanism or every possible Ink setup
impossible. The target is not a universal minimum. A result about a keeper
or consumer of an existing gap must not be used to reject that supporting role.

Two completed copies qualify now: the normal Tweester copy and the ordinary
ground-step copy, each with **zero** gap. The ground result is
`ipg_ground_refresh_completes_without_old_display` in
[InkPostDialogGroundReset.v](../../proofs/InkPostDialogGroundReset.v); its
frame preserves movement Y, and `ipg_whole_ground_call_has_completed_copy_checkpoint`
connects it to the real whole call. Both results keep their explicit storage
and execution conditions. Air/water callers are not promoted by the ground proof.
These are existing proofs, not new theorem or audit results.

The shell, water, ledge and cannon shortfalls keep **Insufficient** labels
qualified by their source or finite-calculation scope. Their numbers alone do
not earn a gameplay-proof label. Unknown bounds stay open. In particular,
the retry's zero movement/display gap afterward is not an exclusion: it can
leave the useful collision/display split intact.

## How the obvious candidates measure up

| Candidate | What it can add or leave behind | Verdict for this supplied height pair |
| --- | --- | --- |
| Tweester, normal continuation | **0** at its completed display copy | **Insufficient — already proved** at this checkpoint, even after a failed internal floor query. |
| Ordinary ground-step copy | **0** at its completed display copy | **Insufficient — already proved** at this checkpoint. Earlier retry and later adjustments remain separate. |
| Shell | **42** in the air or **45** on the ground after the ordinary refresh | A real offset, much too small by itself. Do not add both or stack frames without proving that the refresh is skipped. |
| Water pitch and bob | **207.99609375** in a generous one-refresh calculation at movement Y=768 | Still **962.8687744140625** short. This is an expression envelope, not a reachable swimming maximum. |
| Ledge release | A nominal **100-unit** downward cap at the local write | Potentially the right sign, too small alone. The following action can refresh the display. |
| Cannon firing | Actual Y rises by **0 to 118.16981506347656** in the checked pitch expressions | From matching positions, display is left at or below movement: the wrong sign. The ordinary firing guard also requires A. |
| Negative sand depth | Each display subtraction adds **minus the depth** | Large enough arithmetically; the useful gameplay setup is not granted. |
| Floor alignment, platform movement, animation, bounce snap | Depends on the incoming heights, selected translation or support displacement | These are concrete position writers. There is no justified maximum useful retained gap for the whole group yet. |

The full catalog gives every remaining case an amount or formula, evidence
level and explicit limit. A push may help lose the floor sideways without
being the height source. A dialog or skipped update may keep an existing
gap without creating it. A query conversion or camera-only movement does
not itself move the three stored records. These distinctions prevent us
from counting the same gap several times.

## What the Tweester proof actually closes

[TweesterGap.v](../../proofs/TweesterGap.v) cuts the actual generated US and JP
`act_tornado_twirling` bodies just after the early ejection test. Every
completed continuation contains the subsequent position work, the floor
query and either floor-result branch, followed by the real `vec3f_copy` from
movement to display. At the end of that copy, movement Y and display Y are
the same loaded binary32 value. No floor-success premise or incoming
display-height bound is needed.

The connection resolves the actual copy function and its actual pointer
arguments, then reuses the completed copy proof including allocation, free
and preservation of other valid cells. Its ordinary storage conditions are
a valid Object-pool slot, separate MarioState storage, the reached
`marioObj` pointer and readable movement Y at the copy. It assumes the stated
continuation completes. It does not assume that every earlier helper is
harmless: those executions remain in the prefix, and the storage conditions
are stated at the copy checkpoint.

`twg_non_ejecting_continuation_has_no_gap_checkpoint` supplies that checkpoint.
`twg_copy_cannot_install_supplied_vertical_gap` excludes movement Y=768 with
display Y=1938.8648681640625 there. The combined boundary is exported as
`MainTheorem.current_f02_tweester_gap_boundary`.

The early ejection branch is **outside** this theorem, as are the following
angle call and the surrounding action/update history. Source inspection
shows that ejection returns before the position-update branches. That makes
it a different candidate, not a loophole already covered by this proof.
We have not proved that every complete Tweester history fails to install Ink.

## What still deserves a producer test

For a downward-position candidate, record the old display and the actual
new height at the writer. Floor alignment gives `old display Y - floor Y`;
a bounce snap gives `old display Y - (object Y + hitbox height)`; platform
movement changes the old gap by minus its vertical displacement. Animation
depends on the selected signed translation. The platform phase preserves
both display and collision, so it does not create high display with low
collision from three matching records during that phase. A later collision
copy could help, provided another display copy has not already removed the
gap. The next useful bounded target is a specific reached downward writer
and its next copies, not a blanket assumption that one must exist.

For negative depth, one subtraction using depth
`-1170.8648681640625` would take display Y=768 exactly to the supplied target.
That is only an arithmetic sizing example; the negative-seed grant does
not supply arbitrary magnitude or a useful pose. The existing checked
small-seed example instead uses 1,318 uninterrupted subtractions of depth
`-0.5` at supported Y=1280, reaching display Y=1939. It still needs actual
Mario to drop **512 units** to Y=768 while that display remains. Neither
the real reward/dialog predecessor nor that retained drop is established.

Only after such a producer works do we spend effort on reaching the upper
warp, the first floor miss, live top timing and capture. The separately
supplied JP installation remains a conditional success. No clean route,
no whole-family impossibility result and no changed atlas probability are
claimed by this sizing pass.

## Transport follow-up: rapid home oscillation

The user requested this specific transport check despite the producer-first
priority. The [new diagnostic](../../instrumentation/tweester-transport/README.md)
confirms the source steering mechanism and tests 188,416 supplied schedules
per version. None reaches useful warp proximity before first overlap or
hiding in those tests. A separate relaxed approach supplies a western-ledge
pose whose widest hitbox overlaps Mario at the low warp-contact point.
That conditional contact is not a controller route or a gap producer.

Source inspection follows ordinary ejection into another air-step display
copy; the formal theorem above still stops at the normal copy. Warp
acceptance also breaks the interaction loop before the later Tweester
handler. A subsequent-action proposal needs a specific interruption or
position writer; neither moving the enemy nor simultaneous hitbox contact
already provides Ink. No theorem or probability is promoted by this follow-up.

## Receipts

The selected audit
`build/audit/20260924-140311-qxc9hdrb` passed compilation, hole/link checks and
allowed-foundation checks: 596 registered sources, 426 of 520 proof modules
in MainTheorem's import closure and 94 standalone modules. The new main
boundary and the two selected Tweester theorems each use seven allowed
foundations; the existing main Ink boundary uses nine. This is a selected
dependency build, not a fresh audit of every standalone module.

[ink_gap_arithmetic.py](../../pipeline/ink_gap_arithmetic.py) reproduces the
[finite arithmetic receipt](ink-gap-arithmetic.json). It reads the identical
5,120-entry generated US/JP sine-table initializers, checks 32,767 positive
pitch values, 65,536 signed reset pitches, 32,768 nonnegative bob-timer
values and 14,564 allowed cannon pitches. The water calculation grants the
pitch and bob maxima independently, uses a reset-derived bob height and
one fresh display copy at Y=768, and rounds its operations to binary32.
It does not prove that those maxima can occur together, that bob state
survives every call, or that repeated calls without a refresh are bounded.
This receipt is a reproducible expression calculation, not a Coq theorem
or a gameplay replay.
