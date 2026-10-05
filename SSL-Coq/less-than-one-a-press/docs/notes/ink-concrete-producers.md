# Four concrete Ink gap producers

We now have source-linked Coq results for all four families. They settle
particular writes and short execution segments, not the complete route.
No new controller-reachable Ink setup has been found in this batch.

There are two different sizing questions. The Original example keeps movement
and collision at Y=768 and needs display Y=1938.8648681640625: a rise of
1170.8648681640625. The supplied Variant works with movement Y=1861 and
collision/display Y=768: a 1093-unit movement/collision split. A result about
one direction of mismatch does not automatically exclude the other.

| Producer | What the new proof settles | What still needs checking |
| --- | --- | --- |
| Floor alignment | An accepted ground quarter installs the same movement and cached floor height. Composing it with the real display refresh and following alignment snap leaves **zero display gap at that snap**, whatever the floor height. The new stopped-crawl connection instead leaves display at pre-snap movement height and sets movement to the remembered height at the first alignment store. | The stopped query returns a local answer and does not replace that remembered height. Its earlier provenance and the reason the quarter stops remain open; so do the whole matrix/action tail, collision copy and next useful contact. Crouch slide needs its separate caller connection. See the [stopped-floor proof and gap measurements](ink-stopped-floor-producer.md). |
| Platform displacement | The actual X/Z translations preserve local Y. A reached nonrotating tail sends that Y to the real setter, whose complete three-coordinate execution leaves State Y equal to the supplied local Y. There is **no direct addition of platform vertical velocity** in this helper. | Connect the post-getter local bindings and rotation test to a full invocation. Pitch/roll/yaw matrix branches still need quantitative effects; the existing complete platform-phase proof preserves collision and display, even when movement changes. Floor following is a different writer. |
| Bounce snap and flight | The earlier low-actor snap stays below 1018 only under its listed conditions. The new matched falling-contact result bounds newly created upward movement/display separation by **251**, under live hitbox≤250, finite-range and initially synchronized-display conditions, independently of actor placement. A completed actual air-step call refreshes display and frames its angle/return/free tail; collision Y at the copy cut is preserved. | Derive live dimensions and legitimate higher/cloned placement/contact histories. The contact-to-bounce reads must match; sound and later action/raw-copy effects are separate. Clear-air 30/80 profiles add 128/840 altitude, not surviving display gap. No universal flight maximum follows. See the [bounce/cloning follow-up](ink-bounce-flight-clones.md). |
| Negative depth / dialog | Among the three position records, a real sink changes display only; it can also translate the graphical matrix. Supplied depth **-1170.8648681640625** maps display 768 exactly to the checked top height. With retained depth **-4**, 292 consecutive real sink calls give 1936 and 293 give 1940. The accepted classified stock no-A contract instead makes depth nonnegative, so the sink cannot raise display. | The supplied-seed magnitude test is not a reached dialog. It needs a supported starting pose, actual intervening calls, retained depth/display and transfer to the low floorless collision pose. The unrestricted seed-history coverage remains open outside the accepted contract. |

The negative-depth calculation rules out a simple size objection: a small
negative can accumulate enough display rise if it is retained. It does not
grant that retention. At the checked low pose (-2200,768,-1024), the first
floor query already misses, so that pose cannot simply be used as the starting
point for hundreds of ordinary dialog updates. A supported baseline of 1280
would need only 660 units of rise to reach 1940, but still needs the distinct
512-unit lowering/transfer while display survives. No such continuation is
proved here.

Zero display-minus-movement gap is not an exclusion of a movement/collision
split. The accepted floor quarter can change movement while collision is still
old, so its normal refresh can leave movement and display together above
collision. The floor result therefore closes the named raised-display snap
case only; the later collision copy and contact order still matter for Variant.

The bounce direction also matters. The fire Fly Guy code describes repeated
shrinking during its fire action, and its hitbox is scaled. A negative live
height would make the snap lower Mario, which could leave display above him.
The finite binary32 example 1861 + (-1093) = 768 checks that arithmetic only.
It does not establish that this scale has a registered contact: scaling also
changes the radius, and negative dimensions may prevent overlap. A further
source-linked proof connects the passed contact-height guard to the real bounce
snap: when the actor top used at contact is still the actual bounce sum, Mario
cannot be snapped below his compared raw collision bottom. Thus a top at 768
cannot pass that fresh guard against raw bottom 1861, regardless of whether
its hitbox height is negative. Matching those live values from detection to
the handler remains explicit; a high movement/low raw record could already
exist before the bounce. Geometry
preparation runs before interactions, and the stock warp handler runs before
the bounce handlers. A bounce therefore cannot create a gap and have the
earlier warp check consume it in that same ordinary interaction pass.
The new completed-air-call proof checks its compulsory display copy and real return tail, independently of actor position or velocity. Earlier bounce sound, action entry and subsequent action/raw-copy effects still need their own connection.

For platforms, moving the platform itself upward or downward is not evidence
that this helper changes Mario Y by that amount. The generated implementation
adds only horizontal velocity; vertical movement in the displacement helper
comes from its rotation calculation. There is an important stock-source
restriction: a Tox Box's visible roll changes its face angles, not the angular
velocity fields consumed by this helper. The pyramid top writes yaw angular
velocity and vertical velocity, not pitch or roll angular velocity. Neither
visual roll nor vertical travel establishes a useful rotation displacement.
The existing direct pitch-writer census checks 29 named callbacks; connecting
fresh zero fields and their later preservation to a live rider remains a
history obligation. No universal platform gap bound is claimed.

## How Mario could reach the actions

Access to an action is different from access to its useful split. This source
review identifies ordinary controller paths to several actions, without
pretending that they reach the special pose or support needed by Ink.

| Producer | Ordinary no-A access in the source | What that access does not supply |
| --- | --- | --- |
| Floor alignment | From idle, Z enters crouching; holding Z and moving the stick enters crawling. Walking plus a Z press enters crouch slide. Crawling and sliding can reach the alignment helper. | The exceptional stopped quarter, lower remembered floor, large mismatch and surviving copies. Entering crawling is not a witness for that setup. |
| Platform displacement | Mario can remember an owned dynamic floor when the final raw-position floor query finds it within four units; a live retained platform and an enabled apply phase are then required. SSL Area 1 has the top and three Tox Boxes. | Boarding at the right time, live owner/list preservation and the actual useful angular-velocity fields. Visible Tox Box rolling does not supply those fields. |
| Bounce / knockback | Walking off a ledge can enter freefall without A. A falling contact from above can then reach the bounce handler; ordinary hostile contact can cause knockback without A. | A correctly positioned actor, fresh overlap, live scale and a useful split that survives subsequent motion and copies near the warp. |
| Negative depth / dialog | A no-exit reward and milestone dialog do not themselves require A. | Under the accepted classified stock history contract, a useful negative seed requires an earlier physical A press. Granting the reward opportunity does not grant that seed or the later low-position transfer. |

The action constructors are in `mario_actions_stationary.c` (idle/crouching/
crawling), `mario_actions_moving.c` (walking, crouch slide and freefall), and
`interaction.c` (falling contact, bounce and knockback). The platform conditions
are in `platform_displacement.c`; the stock rotation-field distinction is in
`tox_box.inc.c` and `pyramid_top.inc.c`. Existing `InkCrouchSlideHistory`,
`InkPlatformDeparture`, `InkPlatformDistance`, `Area1PlatformExhaustiveness`,
`Area1NonlocalPlatformInstallationClosure` and `InkStockSeedConditional`
provide the relevant scoped proof inputs. These source paths are not a new
Coq theorem covering every allowed gameplay history. No independent clean
no-A gap producer emerged from this prerequisite review.

## Checked boundary and limitations

The new modules are [InkFloorProducerEffect.v](../../proofs/InkFloorProducerEffect.v),
[InkPlatformProducerHeight.v](../../proofs/InkPlatformProducerHeight.v),
[InkBounceProducerEffect.v](../../proofs/InkBounceProducerEffect.v) and
[InkQuicksandProducerSize.v](../../proofs/InkQuicksandProducerSize.v).
[InkConcreteProducerBoundary.v](../../proofs/InkConcreteProducerBoundary.v)
bundles their actual generated US/JP execution cuts. It is exposed as
`MainTheorem.current_ink_concrete_producer_boundary` and included in the
existing backward-history boundary. Completed caller executions and explicit
numeric/storage conditions remain premises. None is a new coverage axiom.

The floor theorem stops at the real alignment snap and retains the matrix tail
as an execution obligation. The bounce theorem stops at the height snap before
sound and retains its real suffix. The platform result starts at reached cuts
with explicit local bindings; it is not yet a full platform-entry theorem.
The sink-chain theorem uses consecutive real callee invocations; it does not
silently add a dialog scheduler between them. The accepted conditional seed
exclusion and the granted negative-seed transfer test remain distinct.

The [stopped-floor follow-up](ink-stopped-floor-producer.md) now connects the
real corrected-vector query and its cache frame, the complete post-refresh
angle/return/free tail, and the stopped crawling caller to its actual first
alignment snap. The gap at that snap is pre-snap movement minus remembered
height. The query's lower local answer does not supply the remembered value.
The final matrix-pointer assignment preserves the positions, but the preceding
matrix helper's calls and later action/copy effects are not yet framed. The
next producer target is the earlier origin of a large movement/cache mismatch
and its stopping exit, followed by survival to the next useful check.

The largest reviewed **detected** display gap is 1834 units in the earlier
conditional dialog-support receipt, after supplied negative depth/dialog/support;
it refreshes on release and gives no Ink. That is not a clean no-A maximum.
No reachable maximum for the stopped-floor or rotating-platform family is
proved. The linked measurement table states each bound and detection at its
own checkpoint instead of treating a supplied pose as a discovered producer.

No new search was run, no full family was excluded, and all subjective atlas
estimates are unchanged.

## Validation receipt

The selected audit `20261004-182715-naa8lkt4` passed compilation, proof-hole
checks, link discipline and allowed-foundation checks with Coq 8.16.1 and
CompCert 3.15 in the `sm64-item-proof` switch. It checked 630 registered sources
with zero inventory problems. The main import closure contains 458/552 proof
modules; 94 are standalone. The existing backward boundary has nine allowed
foundations; the new main producer boundary, floor boundary, platform boundary,
bounded bounce snap, fresh-contact bounce result and sink boundary each have
seven. These counts describe the existing foundations of the execution model;
they do not discharge the explicit gameplay premises above. The generated
catalog check and its five code tests also pass. No new axioms or proof holes
were introduced.

The [stopped-floor follow-up](ink-stopped-floor-producer.md) extends that
receipt with audit `20261004-200321-m_64kz9h`: 634 registered sources,
462/556 main import closure, 94 standalone and no problems. All 13 selected
statements pass compilation and allowed-foundation checks; the backward
boundary has nine foundations and the others seven each. The actual
ground-call result, caller snap and final pointer-store connections now enter
the existing boundary. Earlier cached-floor creation, the stopping cause and
the complete matrix/action tail remain explicit open gameplay connections.
