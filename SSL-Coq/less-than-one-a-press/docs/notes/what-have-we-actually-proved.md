# What Have We Actually Proved?

Review of proof repository **5c06fff57155dc22d12f60c69f4c1c46d890e09a**, on **codex/ssl-pyramid-item-proof**, 6 October 2026. This is a fixed review of that version, not a live progress counter. The checkout had an unrelated CLAUDE.md edit and an untracked root build directory; neither is evidence for this review or changed by it. The game facts use the pinned stock C and generated US/JP Clight described in the [lifetime audit](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/docs/notes/ink-gap-lifetime-audit.md). No gameplay search, solver, new theorem or new runtime trial was run for this review.

The four approved additions review evidence at **cac0adb6b0a72667980df60859bbdb042af66b63**, inspected 6 October 2026: other platform routes, target credit, Goomba raising/PU transport and Eyerok particles. The existing Ink, pole, Eyerok and elevator chapters preserve their **5c06fff57155dc22d12f60c69f4c1c46d890e09a** evidence baseline. This extension adds no theorem or gameplay trial.

**We have useful proofs. We do not yet have a complete proof that both pyramid stars require a new A press.** Some proposed tricks fail under clearly stated conditions. Other supplied setups work, but their gameplay setup is missing. A completed local proof and an unfinished route can both be true.

## The eight conclusions, before the details

| Category | Current conclusion | The qualification that matters most |
| --- | --- | --- |
| [Ink](#review-ink) | Three supplied JP setups install a useful retained top pointer. Several proposed gap sources and copy mistakes have scoped exclusions. | Creating the right split through allowed gameplay, before the right checks, remains open. The supplied setups are not controller-reachable witnesses. |
| [The pole issue](#review-pole) | Ordinary no-A releases exist; staged Goomba damage can get Mario to the ring. The normalized soft-bonk departure fails within its envelope. | A real enemy must reach the useful contact, and the same continuation must lead onward. Neither requirement is supplied by the damage demonstration. |
| [Eyerok](#review-eyerok) | Named hand rides, departures and speed-building cycles have conditional height/speed barriers. Some local boarding and reboarding tricks work. | The whole live hand/action/support history is not classified. A model-wide barrier is not yet a barrier for every gameplay route. |
| [The elevator](#review-elevator) | The checked ordinary launches fail. An aligned Mario cannot perform the eleven-descent hold under the proved query contract. Fresh triplet spawning has a separate contracted exclusion. | Ground-pound entry, harder falls, changed support and enemy/coin installation still need their actual histories. A granted height window is not an escape. |
| [Other platform routes](#review-other-platforms) | Relocation, clones, skipped queries and Area-2 support changes have source/model or run-specific exclusions. | Earlier useful ownership and the actual allocator/callback/query interval are not covered for every history. |
| [Target credit](#review-target-credit) | Correct target collection and all five Puzzle consumptions are necessary inside the certified account; real local contact consumers are proved. | Actual award/save and revisit/contact-history refinement remain open. Access alone is not credit. |
| [Goomba raising / PU transport](#review-goomba-pu) | Named 91-update schedules fail: favorable 46 rises reach Y1017, below Y1791. | Longer preparation, legitimate repeatable raising, physical transport and live handoff remain open. |
| [Eyerok particles](#review-eyerok-particles) | Own fragments allocate before free; sibling fragments require at least 70 updates against a one-active-update window in the archived model. | Real allocator/callback coverage and post-unload seed classification remain required. Other particles and cross-area reuse are separate. |

The original four names are obstacles and mechanism families, not four disjoint pieces of code. Ink is an exterior installation intended to help at the elevator. The pole is the later lower-route barrier. Eyerok means using the boss hands as transport or speed machinery, not simply defeating the boss. The elevator means getting out of the upper-entry cage, or arranging an interaction there that makes escape possible. The added chapters separate other installers, reward accounting, enemy raising/transport and fragment-slot reuse without adding another unapproved category.

### How to read a claim

Coq is the proof checker; Clight is the generated representation of the C program used by these execution proofs. A game update is one pass through the gameplay loop. Movement often divides that update into four quarter-steps; those are not four extra rendered frames.

A **local execution proof** follows a particular piece of the actual generated program with stated memory and entry conditions. It can establish what every completed execution of that piece does. It does not automatically establish that the game reaches that entry.

A **conditional model theorem** may cover arbitrarily many steps inside a specified model. Its remaining question is whether every relevant gameplay step obeys those model rules. An **exhaustive finite certificate** checks every case in a declared finite set. A **bounded test** checks only its selected trials. A **supplied-state success** shows payoff from a patched starting condition; a reachable route needs one uninterrupted controller replay from the accepted start, without those patches.

Assumptions below have three different statuses: **accepted** starting/rules contracts; **derived** facts already proved in the indicated segment; and **still required** connections to earlier or later gameplay. A settled dependency is not reopened merely because another interval is unfinished. Passing compilation or an assumption audit checks the proof machinery; file and theorem counts do not measure route completion. The atlas's percentages are subjective judgments of route promise, not calibrated confidence, failure statistics or percentages completed.

The current gameplay scope accepts normally initialized SSL Area 1, with the agreed clean state and controller history. It covers ordinary controller play and defined, in-bounds glitches. No memory corruption or arbitrary state writes count as gameplay. Holding A without a new edge (a new press) and never having pressed A are different claims: a held-A departure needs a legitimate earlier held state. The seed argument below concerns a physical press in its tracked history.

<details>
<summary>The overall theorem and the starting-boundary distinction</summary>

The [current capstone](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/MainTheorem.v#L1565) still takes whole-program refinement, evidence-bearing route classification and the remaining writer-family exclusions as premises. Those premises are not proved by naming them, and an initialized Area-1 start does not supply them. The review therefore makes no global star impossibility claim.

The README's headline describes an Area-2 goal; its [linked gameplay boundary](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/README.md#L26) starts in Area 1. These are different interfaces. We use the agreed Area-1 start when discussing reachability, and preserve the explicit clean-pyramid/route premises of the capstone rather than silently connecting the two.

</details>

<a id="review-ink"></a>

## Ink: a gap can do its job before it disappears

### What the trick is asking

Ink aims to enter the pyramid while remembering the spinning top as Mario's platform. JP can carry the old address through the transition. When Area 2 first applies platform motion, it can read the old top's remaining movement fields and displace Mario outside the ordinary elevator start. **Capture**, **retention** and **displacement** are separate jobs: first remember the owner, then keep the reference, then obtain useful motion from it. US's entry clearing is a different case.

The interesting part is that Mario has more than one position. **M** is movement position in MarioState. **C** is raw collision position in Mario's Object. **D** is the stored display position, which need not equal the final visible animated mesh. Y is vertical; XYZ always means X, Y, Z.

**D−C** is display above collision; **M−C** is movement above collision; **D−M** is display above movement. A negative value means the first record is lower. The game can copy one record into another, removing one difference while transferring its effect.

### What the supplied controls actually show

At X=-2200, Z=-1024, let H=1938.8648681640625, the checked timer-131 top height. Original begins at M/C/D=768/768/H. Variant begins at 1861/768/768. Hybrid adds a raised display to Variant: 1861/768/H. These are three supplied controls, not every possible installer and not three reached gameplay poses.

Collision detection runs before Mario's geometry. It reads low C XYZ and records portal contact. Geometry then queries at M. Original's first query misses, so fallback copies D XYZ into M and retries. It becomes H/768/H: D−M disappears, but the 1170.8648681640625-unit effect is now M−C. Variant already has a 1093-unit M−C gap. Its first query can find the top because the lookup allows a floor 78 units above its integer query Y.

Finding the floor is not landing on it. Variant remains about 77.864868 units below the checked top at that point. After the cached warp is accepted, Mario enters the nonfading disappeared action, the game's waiting state for this portal. It still performs ordinary floor alignment: M snaps to the cached floor height and D follows. The later raw copy makes C follow M. The final platform check now sees H/H/H and can capture the owner with a height difference strictly below four units.

So the entry split disappears before the next complete boundary, **after useful checks have consumed it**. The retained pointer carries the effect onward. A zero gap at frame end would miss the installation mechanism.

| Phase in the supplied installation update | Original M/C/D | Variant M/C/D | Hybrid M/C/D |
| --- | --- | --- | --- |
| Contact recorded, before geometry | 768/768/H | 1861/768/768 | 1861/768/H |
| Geometry complete; warp accepted | H/768/H | 1861/768/768 | 1861/768/H |
| Disappeared floor alignment/display copy | H/768/H | H/768/H | H/768/H |
| Raw copy and final capture | H/H/H | H/H/H | H/H/H |

The exact supplied JP lifecycle tests observe Area-2 movement from (0,5500,256) to (365.5927734375,5500,-1096.8026123046875). They grant pillar completion and patch the installation pose once. That demonstrates conditional payoff, not creation of the gap. No clean approach window has been established.

### What the proofs eliminate, and what they leave

The new real fallback proof preserves the Object pool and contact cache through the copy, actual floor retry and height store. Local signed-16 conversion does not write truncated coordinates back into M. Fallback returns to stored D, not automatically to a portal, platform or “main universe.” Arriving at the portal only because of fallback cannot invent a cached contact during that segment. An already cached contact is different; Original shows why that case matters.

A successful query alone does not prove warp acceptance. Contact eligibility, the actual handler, action guards and cleanup still matter. If a later fresh floor read remains null after interactions, the action suffix returns before dispatch. A live pending death/game-over request cannot be replaced by a completed object-warp request. But the earlier death installation and preservation through intervening calls are still separate connections.

Ordinary copies also have real exclusions. The completed raw copy cannot leave M and C vertically different under its receiver/storage conditions. The completed zero-particle callback tail preserves that equality. The actual caller-local particle mask must be zero; merely seeing a zero State particle field later is insufficient. These facts do not erase an arbitrary D gap.

For the producer hunt, the four concrete leads have different verdicts. Accepted ground alignment refreshes D to M. A stopped crawl can instead refresh D at an earlier height, then snap M to a lower remembered floor. That creates D−M equal to old movement height minus cached height—but the stopped query does not install that lower cache. Its provenance and the remaining matrix/action tail are open. Platform application is early enough, before collision; the full phase preserves C/D under ordinary storage conditions, while a specified nonrotating tail adds zero Y. Useful live rotation still needs its own owner/field history.

A fresh bounce changes M during interactions, after the warp's priority slot. There is no second warp check before the ordinary raw copy. Under the completed-copy conditions, its fresh M−C gap cannot wait for a later check. The real classifier-to-first-snap connection is now proved; that read match need not be assumed again. With the stated finite values and live height≤250, the new rise is at most 251 units. Explaining every earlier size/contact history, inherited gaps and later writers remains open.

Quicksand depth is Mario's stored sinking amount. Normally it lowers D; a negative value can turn that adjustment into an upward offset. Negative depth plus a stalled dialog can repeatedly raise D. The largest reviewed detected D−M is 1834 units after 3668 real sink calls from a supplied -0.5 seed. Among 68 supplied releases, 56 move actual Mario before display refresh, but every first query finds a floor and refreshes that update. That rejects those continuations, not all releases. The no-A seed argument is **already proved under its accepted writer, timer and first-action/input conditions**. It is not reopened here. Deriving those conditions for every live history remains separate; the quicksand-jump temporary negative is clamped before its helper checkpoint, whereas late common landing has no equivalent immediate clamp.

### What would settle Ink

We need the first useful split and floor/contact/timing combination from allowed gameplay, plus the same continuation through capture, retention and first Area-2 apply. A controller-only replay would settle a positive case. An exclusion must show that every relevant producer is too small or reaches its consumer too late, or that final selection/lifetime necessarily destroys its payoff. The existing low-final-C/high-floor clearing theorem is useful: it clears both platform references when final raw Y≤818 and the actual returned finite floor height≥1281. The successful controls avoid that premise by raising final C.

<details>
<summary>Ink evidence ledger, assumptions and corrected interpretations</summary>

| Claim | Proof or receipt at reviewed commit | Assumptions / status | Scope | Remaining limitation |
| --- | --- | --- | --- | --- |
| Copy/retry keeps contact and transfers D into M | [InkFallbackContact, taken retry](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/InkFallbackContact.v#L139); [source order/null suffix](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/InkFallbackSourceOrder.v#L354) | Selected symbols, canonical receiver, readable D XYZ, completed taken retry. Separation and callee frame derived. | Actual generated US/JP segment, all XYZ. | Cache is the copy-cut cache; earlier walls/support and later eligibility are not wholly framed. |
| Low final raw query clears both pointers | [Rank1PlatformQueryCompletion](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Rank1PlatformQueryCompletion.v#L34) | Valid pointer cells, actual receiver/call; finite raw Y≤818 and actual returned height≥1281. | Full real query call, including floor effects and frees. | Live bounds and final low C must be reached; later pointer replacement/lifetime still open. |
| Normal callback removes M−C | [InkMarioRawCopyCall](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/InkMarioRawCopyCall.v#L84); [zero-particle tail](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/InkMarioZeroParticleTail.v#L152) | Ordinary receiver/storage at copy cut; actual caller-local mask zero for return frame. Copy/tail effects derived. | Completed callback/copy cuts, including inner null-floor return. | Nonzero particle effects, later objects and next pre-action writers outside scope. |
| Stopped crawl can leave a D−M gap | [actual returned-result alignment](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/InkStoppedCrawlAlignment.v#L393) | Completed ground return, reached crawling path and actual cache reads. Speed guard/setter connection derived. | First remembered-height snap. | Earlier low cache, matrix/action tail, next contact and floor loss not derived. |
| Bounce new-rise≤251 | [real classifier through snap](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/InkBounceLiveReadBoundary.v#L15); [stock bounce receipt](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/instrumentation/bounce-collision-lifetime/expected-stock-receipt.json) | Finite/range conditions, live height≤250; classifier-to-snap continuity derived. Earlier actor history still required. | First new rise; 12 detected supplied bounces, 384 end checks with zero C gap. | Not flight maximum, universal size bound or measured subframe peak. |
| No-A useful negative seed excluded under accepted contract | [InkStockSeedConditional](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/InkStockSeedConditional.v#L131); [accepted conditions](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/docs/notes/conditional-stock-negative-seed.md); [course reset checkpoint](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/InkCourseEntryReset.v#L196) | Accepted classified completed writers, stock timers, legitimate first long-jump history and physical-A connection. Arithmetic implication derived. | Finite classified history from nonnegative depth. | Unrestricted action/writer coverage not discharged. Course reset is proved at its actual checkpoint, not arbitrary preservation afterward. |
| Supplied installers work; searches have not found a clean producer | [lifetime audit and exact cuts](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/docs/notes/ink-gap-lifetime-audit.md); [Original raw vertical receipt](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/instrumentation/jp-vertical-retry/expected-trace.txt); [ten-minute receipt](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/instrumentation/concrete-ink-backward/expected-contact-ten-minutes.json) | Initial pose/scene grants; one earliest patch in each specified continuation. | Three conditional JP controls; later sample 41,540 combinations, 20,770 earlier proposals, no passing extension. | The sample is not exhaustive; deepest chain remains one. Detailed Variant/Hybrid retail raw logs are retained locally under build, not all committed as immutable logs. |
| Already pending fatal warp cannot be replaced | [InkFailedRetryGuard](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/InkFailedRetryGuard.v#L156) | Actual complete trigger call and live nonzero pending-operation load. Guard effect derived. | That call, death18/game-over20 versus object-warp4. | Initial death installation, latch continuity and later transition not proved. |

**Superseded readings:** “the gap lasts one frame” is not a universal bound; zero end-gap does not rule out earlier usefulness. The 1170.864868-unit Original gap is not a universal installer threshold: Variant's 1093-unit split works. Retained-pointer polls do not count as gap-survival frames. The 146 failed parent comparisons were not a global exclusion; later diagnostics replayed actual unequal-parent suffixes and exposed premature warp acceptance.

The four-producer [boundary](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/InkConcreteProducerBoundary.v#L53) is a conjunction of separately checked cuts, not a proof that every producer history belongs to them. The [full lifetime audit](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/docs/notes/ink-gap-lifetime-audit.md) preserves exact source references, receipt locations and all phase conditions.

</details>

<a id="review-pole"></a>

## The pole issue: leaving the pole is not the whole problem

### What the route needs

The lower pyramid entrance leads to the second pole. The useful destination is the ring/aperture beyond it, not simply any state in which Mario lets go. The checked central pole-top seed is (0,4020,1331); the ring floor is Y=3942. The modeled aperture spans X=-101..102 and Z=1229..1434. Mario must get sideways far enough while still high enough, then continue toward the target star.

This explains the familiar A-button obstacle: the normal jump off supplies a useful departure. It does not prove every departure requires A. Z releases, bonks, damage and action changes deserve separate checks.

### What fails, and what really works locally

The normalized soft-bonk model starts at Y=4020 and loses height while gaining little radius. Before the eligible floor window closes, its radius is at most 82, short of the required 101. That is a real conditional exclusion of that envelope. It is not a theorem about every released pose. In the retail fixtures, timed Z release begins at 4070 while delayed release begins at 4020; both fail and return to the Y=3200 base. Those two trials are evidence about those releases.

Damage changes the story. The actual pole damage-selection fragment and falling initializer have checked local executions. Three staged JP contacts at Y=4194, 4020 and 4070 cross toward the ring and land on Y=3942 without a new A edge. The 174 extra handstand units can survive locally, but handstand is not required by this fixture: holding also works.

What was staged? Area loading, the pole pose and a Goomba's position. The supplied attack is a **payoff demonstration**. It says “if we arrange this contact, the departure can work.” It does not say the stock Goomba can arrive there, or that Mario can arrange that damage contact from the accepted start.

### The enemy problem and the other departures

The stock roster has six singleton regular Goombas and a triplet. Contact arithmetic is encouraging: a regular Goomba on the Y=3942 ring has top 4017, only three below holding Mario at 4020; one ordinary 21-unit rise brings it high enough. Its 108 radius plus Mario's 37 can cover the nearby horizontal distance. Those calculations remove a need for an enormous enemy; they do not deliver it.

The older finite terrain graph reports no reviewed path from the nine actors to the ring. Coq checks its encoded receipt lists. It does not prove that every actual Goomba trajectory fits its short walking/jump/pair-transfer edges. Long airborne transfers, hard-fall rebounds and repeated pushes are omitted. Treating that graph as a universal installer exclusion would be a mistake.

Two tempting alternatives have narrower failures. Collecting the no-exit coin star while still attached chooses a standing dance and snaps to the actual cached floor; it is not an automatic airborne launch. The checked Amp-shock composite zeroes horizontal motion, is vertically stationary only on the first update, then falls to the base on update 21 and fails its stock corridor/support cases. That failure must not be applied to ordinary Goomba knockback, whose staged payoff succeeds. Direct action-request censuses and local A tests close their listed requests, not all later collision and support histories.

The source model also protects the named private action tables. Hypothetical changed-table arithmetic is not a stock gameplay installer, and corruption is outside this review's allowed model. Protection of those tables does not close every ordinary contact or exported-state issue. The checked stock targets are also too far horizontally to touch while Mario remains inside the unchanged pole aperture; this prunes the direct across-barrier contact, not alternate target poses or an actual departure.

### What is still needed

For damage, the exact missing connection is a stock actor's legal approach to nonlethal contact while Mario remains in a useful pole state, followed continuously through the selected damage action, walls, ring landing and onward target contact. A clean replay would establish a positive route. A negative theorem needs live trajectory coverage of the omitted falls/rebounds/flights, or another invariant that bounds every useful enemy approach and departure.

The overall lower-cut theorem also requires that an actual target event has an earlier validated crossing and that the listed writer/support alternatives are excluded. Those are premises, not conclusions of the normalized bonk proof. A reconstructed one-A segment reaches the downstream Grindel neighborhood, but its receipt explicitly stops before Grindel landing, all five Puzzle triggers or a target save-bit update.

<details>
<summary>Pole evidence ledger and superseded claims</summary>

| Claim | Proof or receipt | Assumptions / status | Scope | Remaining limitation |
| --- | --- | --- | --- | --- |
| Normalized soft bonk cannot clear | [RouteEvidence](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/RouteEvidence.v#L93); [lower-cut application](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2LowerTargetCut.v#L593) | Accepted height/radius envelope; arithmetic bound derived. | Normalized Y4020 sample, radius≤82 before floor window. | Not every live release or animation-adjusted seed. |
| No-A direct requests and A gates checked | [PoleExitSplit](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2Rank11PoleExitSplit.v#L157); [LivePoleExit](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2Rank11LivePoleExit.v#L216); [two release receipt](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/instrumentation/jp-rank11-pole-release/verified-receipt.txt) | Actual receiver/input read; A mask clear at that cut. Source/request census derived. | Named fragments; two staged enemy-free JP releases. | Earlier physical input and later action/collision coverage open; fixture uses 23 pole writes. |
| Staged damage reaches ring | [HandstandDamage](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2Rank11HandstandDamage.v#L191); [real falling initializer](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2Rank11FallingInitializer.v#L259); [JP receipt](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/instrumentation/jp-rank11-handstand-damage/verified-receipt.json) | Reached action fragment; depth/squish/flag and writable-cell conditions. Selected initializer effects derived. | Three staged contacts, 23 pole +3 enemy fixture writes. | Actual stock installation, complete caller effects and star suffix not supplied. |
| Stock roster and reviewed transfer graph | [GoombaInstaller](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2Rank11GoombaInstaller.v#L61); [encoded receipt check](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2Rank11GoombaInstaller.v#L236) | Checked source roster; analyzer's limited transfer rules. | Nine actors and encoded reviewed reachability/no-path results. | No theorem mapping all live trajectories to those transfer rules. |
| Attached star and stock shock fail their payoff | [StarExecution](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2Rank9AStarExecution.v#L134); [ObjectImpulse](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2Rank12ObjectImpulse.v#L528) | Reached pole/action/cache; specified shock seed, walls and owner tracks. | Attached standing-dance branch and finite stock Amp composite. | Airborne star installation and other impulses remain separate. |
| No-A target event is excluded only with full coverage | [LowerTargetCut obligations](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2LowerTargetCut.v#L740); [conditional exclusion](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2LowerTargetCut.v#L866) | Same-frame event refinement and all named lower writer exclusions still required. | Conditional route theorem. | These premises cannot be supplied by the two failed releases. |
| One-A continuation has limited authenticated endpoint | [downstream pole receipt](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/instrumentation/jp-lower-one-a-route/verified-pole-receipt.txt) | Staged pole seed, one edge held across 34 samples. | Reaches Grindel neighborhood. | No completed reconstructed target-star suffix. |

**Superseded readings:** “only A can leave the pole” is false. Y4020 is not every release height. The transfer graph does not cover all airborne motion, and the separate 91-frame Goomba-raising bound belongs to its exterior top-window proposal, not every Area-2 enemy approach. A successful known one-A route cannot prove that an alternative needs A.

</details>

<a id="review-eyerok"></a>

## Eyerok: the hands are useful machinery, within limits

### Why investigate the boss hands?

Eyerok's ordinary reward is a different star: normal boss-star index 3, whereas the targets use indices 2 and 5. Beating the boss does not substitute for collecting either pyramid target. The idea is to use the hands as moving floors: board one, preserve speed while it rises or changes shape, reboard after an attack, or carry a platform reference through a warp.

That gives this category several related routes, not one “Eyerok exploit.” A ride needs a usable hand contact and enough height/speed for a departure. A stale-hand route needs an owner captured at the warp, surviving bytes or replacement motion, and useful target contact afterward. The sleeping-hand “Pedro” idea needs enough independently obtained speed to cross the wall band into its narrow floor/ceiling squeeze.

### What the ride proves

A staged US retail ride really performs idle → punching → jump-kick with a B edge and A already held. It catches a rising hand at a 49-unit gap, then rides its movements of 85, 70, 55, 40, 25 and 10 units to top Y=-943. Earlier claims that this local action predecessor had to be directly injected are superseded. The earlier travel, hand contact and boss schedule are still supplied.

The selected double-pound flight has stronger source evidence: actual US/JP Clight prefixes construct ten specified velocity/Y steps, six up and four down. The origin rises 285 units; the closed mesh offset is 306, giving the selected top ceiling -943. Those prefixes stop before the water-query tail. They do not yet connect the entire ten-update flight, impact, reset and next launch.

“Seed” in this argument means Mario's starting vertical speed, not quicksand depth. Within the ideal departure model, every integral seed through 31 misses the Y=-562 tunnel floor. Even granting a full 160-unit ledge check and the 78-unit floor allowance, seed 31 reaches a query ceiling of -569: seven units short. Seed 32 crosses the arithmetic threshold, but no stronger clean predecessor is established. A jump-kick replaces vertical speed with 20; it does not stack an extra arc on top of conserved speed.

The modeled six-effect schedule preserves the seed limit for any finite number of cycles. This is a real universal theorem **within that effect alphabet**. The advertised 181,944 combinations are arithmetic quotient tuples, not an exhaustive analog-input search. Classifying every live frame into the alphabet remains open.

### The other hand routes have their own boundaries

The broader two-hand envelope bounds the later hand surface at 1179. Granting Mario another 630 reaches 1809, below the 1889 query threshold for the Area-2 floor at Y=1967. This excludes that high-floor payoff within the envelope. It does not exclude the separate Y=1280 tier. The latter has its own archived wall/path exclusions under speed≤48 and travel/quarter-step budgets; those are not a blanket “cannot return to Area 2” theorem.

Attacking and reboarding is also not generally disproved. Standing on the hand's top is above the eye hitbox, so the simple standing-attack plan fails. But an injected long-jump fixture nonlethally reboards after the hand returns home. It does not ride the immediate hit impulse. Ordinary long-jump entry needs a fresh A edge; this fixture supplies no compatible no-new-A predecessor. Its useful later departure is also missing. Lethal direction/braking failures exclude those trials, not every analog schedule.

For sleeping-hand speed, the modeled entry needs speed over 400. Starting at a generous 110 and allowing 0.15 per air update for 400 updates reaches only 170. Named stock platform drops stay below the strict 100-unit off-floor requirement; the modeled preserving butt-slide bounce cannot repeat without normalization. An injected speed-424 landing demonstrates the payoff once speed is supplied. The stock-cycle exclusion still depends on actual owner tracks, action transitions, collision refresh and episode bounds obeying the model.

The JP stale-hand construction is retired within its audited stock classification: its modeled installation bands and later motion do not supply useful transport. The one modeled nonidentity replacement moves about eight down and 38 backward. That is not proof that every live hand pose and slot history satisfies the classification. There is no modeled Act-6 continuation for this construction. The wake-sandwich proposal's update-11 entry/update-12 closure also rules out a repeat-ground speed engine, while leaving a one-update cache installer open. Other seams and partial-update flag histories need their exact writers and transforms.

### What would settle an Eyerok route?

For the selected ride, connect the proven movement prefixes through real floor/contact work, the terminal clamp, impact/reset and every later launch. Then show that reboarding cannot escape the height/speed envelope—or exhibit the first legal step that does. For a positive route, the same controller history must establish the useful seed, boarding, departure, warp and target contact.

For a family-wide exclusion, live ownership, collision selection, actor lifetime and action/callback histories must justify the model classification. A theorem over the model cannot stand in for that connection. Archived hand results remain supporting evidence with their original premises; archive presence does not automatically make them part of the current capstone.

<details>
<summary>Eyerok evidence ledger, active versus archived work</summary>

| Claim | Proof or receipt | Assumptions / status | Scope | Remaining limitation |
| --- | --- | --- | --- | --- |
| Local B-edge held-A ride exists | [ControllerRide boundary](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/EyerokRank15ControllerRide.v#L195); [retail manifest](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/old-proofs/eyerok-manipulation/instrumentation/results/contact_manifest.md) | Hand/scene staged; A held from Area-3 entry. Source shapes and encoded ride values checked. | Local retail ride to -943. | No clean earlier hand contact, boss schedule or useful departure. |
| Double-pound steps construct actual Y writes | [PoundFlight](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/EyerokRank15PoundFlight.v#L441) | Actual object loads, supplied gravity/zero buoyancy, writable separated cells. Local execution derived. | Ten specified body prefixes and 285 rise. | Whole water/floor/impact/reset cycle not constructed. |
| Seed≤31 cannot reach selected tunnel | [VSC](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/EyerokRank15VSC.v#L300); [schedule induction](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/EyerokRank15ScheduleSearch.v#L368) | Hand-top bound and six modeled effects; local arithmetic derived. | Every finite classified effect sequence; seven-unit shortfall. | Every relevant live step's membership and stronger predecessors open. |
| Two-hand high-floor barrier | [DynamicSupport](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/EyerokRank15DynamicSupport.v#L647); [live projection](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/EyerokRank15LiveProjection.v#L603) | Connected memory-faithful chunks, owner/height envelopes and accepted live-run conditions required. | 1179+630=1809 below 1889 threshold. | Full accepted run not constructed; does not exclude Y1280. |
| Simple standing attack fails; staged reboard can work | [archived MarioHandContact](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/old-proofs/eyerok-manipulation/proofs/MarioHandContact.v#L119); [attack/reboard manifest](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/old-proofs/eyerok-manipulation/instrumentation/results/attack_reboard_manifest.md) | Checked standing pose or supplied long-jump fixture. | Exact eye/top geometry and selected finite suffixes. | Legal prior A/action history, steering, timing and final departure open. |
| Lower-tier departure classes excluded conditionally | [archived NoA1280Barrier](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/old-proofs/eyerok-manipulation/proofs/NoA1280Barrier.v#L259); [archived HeldA1280Barrier](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/old-proofs/eyerok-manipulation/proofs/HeldA1280Barrier.v#L320) | Granted start at Y=1179, speed≤48, 35 eligible quarter-steps, with maximum travel of 12/13 units per quarter-step. | Named B-only/already-held-A wall/path models toward Y1280. | Not every departure; archived theorem is not automatically imported. |
| Sleeping-hand repeat-speed model fails | [Preload](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/EyerokRank29Preload.v#L321); [CycleClosure](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/EyerokRank29CycleClosure.v#L376) | Specified speed/frame/gain caps and two named preserving-boundary cases. | Conditional stock-cycle model; 170 versus >400. | Live episode, action, owner and reset classification still required. |
| Stale-hand and normal reward exclusions have distinct scope | [Ordinary stale-hand certificate](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/JPEyerokStaleHandOrdinary.v#L298); [normal source-index theorem](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/SourceExhaustiveness.v#L184) | Stock pose/lifetime classification for stale hand; normal source provenance for reward. | Named stale-hand model; normal boss reward cannot alias target indices. | Stale-hand certificate is standalone support, not wholly consumed by Main; abnormal receivers/save writers outside normal-index kernel. |

**Superseded readings:** the old one-envelope-step-per-Clight-microstep projection was replaced by connected chunk requirements. The counterfactual “243 more units” is not a stackable jump-kick. A 46-unit eligibility gap is not a proved snap. Finite lethal failures do not disprove nonlethal reboarding. Nine unresolved native names in a call census are not nine demonstrated glitches.

[Current Eyerok atlas scope](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/docs/no-a-route-atlas.md#L1366) retains the wake installer, seams/partial updates, alternate speed predecessors and separate lower-tier cases. None is silently closed by the selected ride barrier.

</details>

<a id="review-elevator"></a>

## The elevator: enough height is not an entry method

### The cage, and the promising idea

Entering through the upper pyramid warp puts Mario on a descending elevator inside a shaft. The challenge is to escape its walls early enough to reach useful pyramid terrain. Ink would change that entry; this section asks what stock elevator gameplay can do without such an installer.

Ordinary rollout and an already-held-A jump-kick looked worth checking because they can move Mario upward without a fresh A edge. Their full arithmetic return envelopes peak at 227.5 and 135 relative units, below the checked strict 231-unit cutoff. The selected JP wall/floor/ceiling traces fail. Four representative held-A faces do not establish every continuous launch pose, but the full-return figures are stronger than the earlier partial-frame estimates. The actual rollout animation ending also keeps Mario in rollout; it does not supply a new freefall or ground-pound entry.

Ground pound has a different attraction. Its startup lifts Mario while the elevator descends. A granted 15-update scenario reaches relative height 260, above the cutoff. The startup's own lift is bounded by 110; the rest comes from descending support. **That is a conditional height window, not proof that Mario can enter ground pound.** Startup also stops horizontal speed, so useful height still needs a sideways departure.

### Can we make the elevator fall away?

One proposed producer holds Mario at his old Y while the elevator descends eleven times by ten units. That could create the off-floor difference needed to enter an airborne action.

The completed grounded-quarter proof now closes that named mechanism under its query contract. Every contracted descent realigns Mario to the current base. This works for any supplied finite number of such calls; eleven cannot retain the initial height. It does not assume alignment survives between calls: interludes preserve Mario's Y, and the next call derives alignment again.

What is the contract? A real nonnull floor at current base height, sufficiently high ceiling, the shell-riding bit clear, and proposed Y matching Mario's carried Y. The numerical base range and actual receiver/read/write conditions are also explicit. If these hold, repeatedly choosing blocked grounded steps cannot create the eleven-descent hold.

Several source and geometry results support the contract. The base covers its interior; positive-Y static support inside the checked rectangle is low; ordinary underside queries skip the base as a ceiling; no static triangle enters the proved shaft corridor. Time-stop loading skips do not themselves delete the existing surfaces. But full live loading, rounded plane heights, list membership and every wall-corrected query still need their connection. The first actual failure of one of those facts would be a concrete exception worth testing.

### What about a harder fall, enemy or coin?

The blanket claim “Mario is never more than 100 units from the floor” is false; grounded and airborne phases need different invariants. The ordinary slide-kick profile misses its freefall timeout gate: its timeout checks have gaps 142 and 206, below the required over-500 gap at a timer over 30. A supplied -75 impact rebounds at 37.5 and reaches gap 565 at update 31, passing that freefall gate in the arithmetic example. Ground-pound entry would then need a separate eligible Z transition. The actual initializer forces launch speed 12, so inheriting -75 before that initializer is excluded. Producing a harder fall afterward remains open.

Coins are not already sitting conveniently on the cage. The checked fixed layouts miss the enlarged base, and formation-offset exclusions have their own bounds. A coin arriving underneath can query and snap onto the bottom base in the supplied catcher example. That does not prove defeat, spawning, coin trajectory, lasting support or collection. A yellow coin alone does not unlock ground pound; a useful 100th coin also needs the star's placement and action timing. Directly touching the checked target stars or secret triggers from inside the unchanged elevator footprint is separately excluded by horizontal contact distance; that does not exclude a different target placement or an escape.

The Goomba geometry is close enough to be interesting. At a supplied west-wall contact, Goomba X=-551, Z=-187 with a sufficiently hard fall rebound can reach the vertical/horizontal allowances. Its actual floor is below the elevator, so merely walking or a normal low-ground jump is insufficient. Isolated stock-actor searches get some raised eastern Goombas into the low pit; none supplies elevator contact. Those trials do not cover all hard rebounds, roofs or airborne transfers. Reaching the bottom cage also does not skip the later second pole.

The distant fresh triplet is a separate, stronger exclusion. Its unloaded parent at stock X/Z has a calculated distance of at least 3882 from raw Mario in the full elevator base, versus a strict 3000 activation threshold, under the checked finite vertical-difference range. Coq carries nonspawning through any finite sequence of contracted checks. The parent fields, distance interval and Mario confinement are explicit. This closes fresh spawning under that confinement contract; it does not exclude children spawned earlier or the six singleton Goombas.

### What would settle elevator escape?

For ordinary grounded continuation, establish the live floor/query contract across the actual allowed inputs, or find its first legal violation. For the harder-fall branch, establish the post-initializer fall, airborne action/timer gate and a useful lateral exit. For an enemy/coin branch, connect an actual stock approach, defeat/contact and collectible trajectory while Mario remains confined, then the same action change and departure.

A continuous no-new-A replay would settle a positive case. A negative result must cover the still-live support/action/impulse alternatives, not just repeat the ordinary failed launches. Existing height and alignment proofs are finished at their stated boundaries; their application to every elevator history is the remaining gameplay question.

<details>
<summary>Elevator evidence ledger and the contracts that remain</summary>

| Claim | Proof or receipt | Assumptions / status | Scope | Remaining limitation |
| --- | --- | --- | --- | --- |
| Ordinary launches fail height envelope | [QuarterStepClosure](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/UpperElevatorQuarterStepClosure.v#L292); [live JP receipts](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/UpperElevatorLiveTraceReceipt.v#L412) | Checked launch, gravity and support conditions; completed return arithmetic derived. | 135 held-A /227.5 rollout peaks; selected complete JP traces and four faces. | Not every live X/Z pose or changed support. Pose-independence theorem uses a Y projection that ignores pose. |
| Ground-pound startup has a height window | [GroundPound](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2Rank10AGroundPound.v#L355) | Eligible startup supplied, stated finite range and headroom episode. Actual local stores derived. | Lift≤110; specified descending scenario reaches260. | No legal entry or lateral escape established. |
| Eleven-descent hold impossible under query contract | [GroundHold](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2Rank10AGroundHold.v#L241) | Nonnull current base, ceiling≥5222, shell bit clear, matching proposed/carried Y; interludes preserve Y. Alignment itself derived. | Any finite contracted sequence; named eleven-descents case. | Live surface/list/corrected-query and input conditions need whole-history justification. |
| Static geometry and distant targets narrow alternatives | [SupportChange](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2Rank10ASupportChange.v#L52); [StallSources](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2Rank10AStallSources.v#L38); [saved finite support results](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/instrumentation/rank10a-live-support/checked-results.json); [actual contact rejection](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2Rank12BContact.v#L528) | Specified rectangles/meshes, target XYZ/hitboxes, real arbitration/contact fragment or bounded supplied quarters. | Universal finite-mesh geometry and both gate-footprint contact rejection; 23,855,421 supplied quarters per version. | Live loading/list/target-position coverage not derived globally. There are 4,770 high-gap early stops; “no ceiling stops” is false. |
| Ordinary slide kick fails; hard landing can pass supplied gate | [SlideKickEnvelope](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2SlideKickEnvelope.v#L150); [initializer](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2SlideKickInitializer.v#L338) | Specific profile; supplied hard impact for positive case. Launch12 and initializer suffix derived. | 51 ordinary updates; -75→37.5 rebound and gap565 example. | Producing that later hard fall, actual collisions and useful departure open. |
| Fixed coins absent; catcher and dry-death helper scoped | [ElevatorCoins](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2ElevatorCoins.v#L27); [GoombaDeath](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2GoombaDeath.v#L148); [coin note](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/docs/notes/rank10a-elevator-coins.md) | Checked layouts/formation offset bounds; real helper flags or supplied catcher. | 41 diagnostic fixed actors miss; selected bottom snap; dry clear-bit automatic-death helper does not kill. | Enemy defeat, spawn/trajectory, live flags, tangibility, star and collection timing open. |
| West-wall enemy opportunity needs a fall | [GoombaApproach](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2GoombaApproach.v#L306); [timing/search limits](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/docs/notes/goomba-elevator-timing.md) | Chosen contact pose and -78 impact→39 rebound; real floor certificate. | Supplied local geometry, limited isolated actor trajectories. | Stock arrival and actual contact while Mario remains confined not constructed. |
| Fresh triplet cannot activate while contract holds | [TripletSpawner geometry](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2TripletSpawner.v#L330); [arbitrary finite checks](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2TripletChecks.v#L248); [bound distance execution](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2TripletBoundDistance.v#L89) | Unloaded stock parent; five-field interludes, confined raw Mario, finite ΔY range (±16384). Selected callback effects derived. | Any finite contracted check sequence, calculated distance≥3882 versus3000. | Full interludes/scheduler and runtime transport open; earlier children/singletons outside claim. |

The square-root issue is not simply “we do not know what sqrt does.” The [explicit bound runtime](https://github.com/tra38/sm64-wmotr-abc-proof/blob/5c06fff57155dc22d12f60c69f4c1c46d890e09a/SSL-Coq/less-than-one-a-press/proofs/Area2TripletBoundDistance.v#L102) constructs the generated distance call using the proved instruction binding and normal processor controls. That local connection is settled. The older arbitrary-check sequence still explicitly takes its named sqrt contract; transporting the surrounding gameplay into the bound runtime remains separate.

**Superseded readings:** old quarter/frame peaks are replaced by full-return 135/227.5. The eleven-descent alignment completion is no longer open inside its contract. A 260-unit granted startup does not prove entry, and the airborne counterexample prevents extending the grounded invariant to all actions.

</details>

<a id="review-other-platforms"></a>

## Other platform-displacement routes, other than Ink

Evidence for this added chapter: repository **cac0adb6b0a72667980df60859bbdb042af66b63**, inspected 6 October 2026. The original four chapters retain their earlier baseline.

### What would make this a different installer?

A platform installer must first make Mario remember a useful moving object, then keep that reference until the displacement helper consumes it. Relocating the warp or a standable top, preserving collision on a clone, and moving during a skipped-query interval are distinct proposals. Changing support on an Area-2 revisit is another access idea, although a changed floor address alone is not a displacement installer. Original, Variant and Hybrid stay in the [Ink chapter](#review-ink); they are controls for its position-split mechanism.

### What is actually excluded?

The relocation/clone census is backed by an authenticated zero-A JP four-pillar run: 2,462 frames, 2,353 top-collision loads, and three retired-slot reuses. The top and warp retain their canonical identities; each reuse clears collision before changing behavior. That rules out this construction in that run. The generated-source census and checked receipt counters do not classify every allowed spawn, alias or object lifetime.

The skipped-query result needs a sharper qualification. Its semantic step is an identity function, and its linked record retains explicit callback, lifetime, alias and external-effect premises. It proves preservation inside that model; it does not derive that every real skipped update leaves Mario still. A useful exception needs an earlier live pointer and real movement before a later platform query recomputes the pointer.

### Capabilities are not completed routes

The related State-first diagnostic supplies movement XYZ=(-1862,67314,-902), which narrows locally to query XYZ=(-1862,1778,-902), while collision remains at the portal. Its lookup/capture capability works without display fallback. This is another way to use an inherited split, not an independently reached platform installer. The stock-null chronology model blocks its specified payload under its conditions; the earlier owner, payload and legal pre-collision split are still missing.

Inside Area 2, the Amp-shock composite supplies a pole-centre start at Y=4020 with vertical speed zero and no horizontal motion. Its integer fall kernel lands on static Y=3200 at update 21, outside its checked moving-owner corridors. This is a finished source-pattern/arithmetic certificate, not execution of the complete linked shock/air-step/platform chain. A staged reload receipt changes the static floor address but prints zero displacement, null owners and a null platform; its clean-controller flag is false. Neither result proves useful transport. Ordinary Goomba pole damage remains in the [pole chapter](#review-pole).

### What would close the remaining routes?

For relocation or cloning, connect the reached spawn/collision writers and slot generations to the census. For skipped queries, derive actual callback targets and movement/pointer preservation across the entire interval. For Area-2 support changes, connect homes, axes, live floor lists, owners and entry/reload effects to the selected model, or supply a clean useful exception. Then apply the shared capture, pointer-lifetime and first-apply obligations in [Ink](#review-ink). Ranks 17/27 and 26A–E classify pointer/payload fate; they are not extra installer discoveries. No new runtime test was needed for this consolidation.

<details>
<summary>Other platform-displacement routes, other than Ink: evidence ledger and remaining connections</summary>

| Claim | Proof or receipt | Assumptions / status | Scope | Remaining limitation |
| --- | --- | --- | --- | --- |
| Relocated warp/top or collision-preserving clone | [Source census](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/Area1WarpTopCloneCensus.v#L166); [receipt boundary](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/Area1Rank4WarpTopTraceReceipt.v#L239); [authenticated run description](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/instrumentation/jp-rank4-warp-top/README.md#L10) | Generated syntax and recorded counters derived; all reached writer/lifetime coverage still required. | One zero-A JP run: 2,462 frames, 2,353 loads, three cleared reuses. | Does not exclude another legal spawn/alias/owner history. |
| Moving during a skipped query | [Identity model and linked premises](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/Area1MovingSkippedQueryClosure.v#L339); [temporal model](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/Area1InstallerTemporalClosure.v#L152) | Preserving step defined as identity; callback/lifetime/alias/external propositions remain supplied. | Completed model preservation and source reductions. | No linked all-history movement exclusion. |
| State-first lookup capability | [Supplied nonlocal endpoints](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/docs/notes/area1-nonlocal-endpoints.md#L40); [payload/setup boundary](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/docs/notes/area1-nonlocal-endpoints.md#L245); [framed classification](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/Area1PrecollisionWriterClosure.v#L534) | Unusual State/Object split and scene supplied; terrain/collision frames and platform refinement required. | Conditional engine capability and chronology model. | Earlier legal platform installation is not constructed. |
| Amp shock / moving support | [Fall kernel](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/Area2Rank12ObjectImpulse.v#L491); [composite certificate](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/Area2Rank12ObjectImpulse.v#L600) | Y4020/vy0, zero horizontal motion and specified stock corridors in an integer model. | Selected finite/source-model fall to Y3200 at update21. | Live shock, owners, list and collision chain not derived. |
| Reload changes support address | [Script/entry facts](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/Area2Rank12AReloadSupport.v#L187); [staged receipt witness](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/Area2Rank12AReloadSupport.v#L291); [raw JP trace](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/old-proofs/eyerok-manipulation/instrumentation/results/jp_platform_trace.txt#L1) | Staged receipt; clean-controller flag false; no useful platform retained. | One floor-address change with zero displacement. | Other useful reload/support histories remain open. |

</details>

<a id="review-target-credit"></a>

## Getting credit for the target without the expected route

Evidence for this added chapter: repository **cac0adb6b0a72667980df60859bbdb042af66b63**, inspected 6 October 2026. The original four chapters retain their earlier baseline.

### Collection, contact and crossing a gate are different jobs

The two rewards are Inside the Ancient Pyramid and Pyramid Puzzle. A valid route need not copy the familiar pole jump or elevator exit if another reachable history earns the correct contact and credit. Conversely, crossing a barrier does not prove pickup. Puzzle adds five distinct secret triggers before its reward. The collection must identify the correct target object and newly set the correct save bit in the same execution.

### The bookkeeping theorem—and its real-code links

Within CertifiedExecution, a new target bit requires a collection event with correct star origin and overlap. From CleanPyramidEntry, new Puzzle collection requires all five distinct consumption events. These are completed conditional bookkeeping proofs. Their event constructors already require provenance, overlap, counter changes and preservation by other events; mapping every actual game step into that account is still required. They do not prove a physical gate must be crossed.

Actual US/JP contact-consumer proofs narrow that connection. Successful secret and star searches read the requested/returned pointer and preserve memory; the star search checks its interaction type. A completed secret callback with a memory change or observable event must first have obtained a successful entry query. That does not identify the effect as credit or establish the contact list’s origin. Clearing, capacity, registration, later writes, object generations, geometric readbacks and helper effects still need their live connection to award/save execution.

### Revisits and the existing positive evidence

Puzzle initialization counts remaining secrets, restores progress from those missing, and can spawn the reward immediately when none remain. Normal removal/no-respawn records can preserve earned progress across visits. Therefore each credited missing original secret needs an earlier legitimate contact/removal/reload history; five fresh touches on the final visit cannot be assumed. An unexplained missing object is not free credit.

Published lower-entry runs visually finish both targets with one displayed A press at the second pole. An exact JP controller segment reproduces that edge and reaches the Grindel base. Injected JP suffixes separately show five secrets plus spawn, and a tuned pickup/save byte change 0x00→0x20 with zero A counters. They cannot be joined into one clean zero-A route. Rank 9 grants an airborne outside-elevator start and 99 coins; nine later pickup timings fail, and one stationary Act-3 sample misses by 75 units. Independent access and complete target pickup remain open.

### What would close credit without the expected route?

A positive case needs uninterrupted controller-reached access, actual contacts, dispatch, object lifetime, secret/revisit accounting and the correct new save bit. A negative case needs refinement of those real operations to the certified account and proof that allowed no-A histories cannot supply the necessary contact or legitimate earlier secret credit, not a decree that alternate credit is impossible. Three private action-table blocks are already protected through finite selected initialized Clight executions; that settled theorem does not protect all public reward state. Defined aliases/receiver/save effects remain Rank 31 obligations. Machine-only out-of-bounds overwrites, ACE, DMA and post-undefined-behavior continuations lie outside the current model. No new runtime check was run here.

<details>
<summary>Getting credit for the target without the expected route: evidence ledger and remaining connections</summary>

| Claim | Proof or receipt | Assumptions / status | Scope | Remaining limitation |
| --- | --- | --- | --- | --- |
| New target credit needs the specified collection | [CertifiedStep constructors](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/AreaTransitions.v#L167); [target-bit necessity](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/StarCollection.v#L70) | CertifiedExecution and newly_collected supply the theorem interface; its event rules require provenance, overlap, counters and preservation. | All histories in that certified account. | Whole-game step-to-account refinement not discharged. |
| Puzzle needs all five distinct consumptions | [HiddenStar necessity](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/HiddenStar.v#L314); [revisit source audit](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/docs/notes/ordinary-gameplay-route-coverage.md#L210) | CleanPyramidEntry and certified event history; ordinary removal/respawn mechanisms audited. | Completed bookkeeping; actual revisit source paths identified. | Earlier earned progress and live reload/removal histories need connection. |
| Successful queries and completed secret effects need contact reads | [Consumer execution](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/ContactConsumerExecution.v#L478); [secret callback](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/SecretContactExecution.v#L218); [geometric conditions](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/ObjectContactNecessity.v#L306) | Real successful calls, valid receivers and memory; geometric phase/readback conditions explicit. | Local actual US/JP execution; memory-preserving searches. | Credit identification, contact-list origin/lifetime and award calls remain. |
| Downstream collection can work from supplied access | [Distinct receipts](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/Area2DownstreamReceipts.v#L101); [continuation limits](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/docs/notes/area2-downstream-continuations.md#L277) | One-A visual runs or separate injected suffixes; Rank9 airborne/99-coin start granted. | Positive bounded receipts; no joined clean no-A run. | Authenticate version/inputs, clean access, full live pickup and save. |
| Private action tables are preserved | [Reached-execution closure](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/WritableActionTableReachedExecution.v#L459); [award/contact gaps](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/docs/notes/collection-backward-contact.md#L63) | Genuine selected initialized task start and stated private-block conditions. | All finite reached executions of the selected Clight runtime for three blocks. | Not public reward-state integrity or all defined receiver/save histories. |

</details>

<a id="review-goomba-pu"></a>

## Goomba raising and PU transport

Evidence for this added chapter: repository **cac0adb6b0a72667980df60859bbdb042af66b63**, inspected 6 October 2026. The original four chapters retain their earlier baseline.

### Raising an enemy is different from bouncing Mario

This proposal raises a Goomba by controlling when its movement runs, then transports or aligns it with Mario and the Spindel. It is not ordinary enemy damage at the second pole. A PU (parallel universe) is a distant coordinate region whose terrain queries can alias the main map because collision locally narrows coordinates to signed 16-bit values. That terrain alias does not itself teleport an object or make two distant actors collide.

### The finite height barrier is already proved

The proposed loop requires damaging contact, departure beyond the Goomba’s 4000-unit drawing distance, a FAR reset and a near return. The selected grounded priming branch arms the first rise; subsequent ready states use airborne action 2 with vertical speed 25. Gravity gives exact binary32 speed 21. The stored-height addition can still round: adding 21 at 2^29 stagnates. This example does not prove that the selected Y51 orbit reaches that value.

The conditional integer H/F/R mirror uses hit/depart, far-reset and near-rearm phases, with 21 units per modeled productive hit. The original post-collision schedule allows 31 rises in the supplied 91-update top window: Y=51 reaches 702. The revised raw-Object return-first schedule allows 45; the favorable departure-first phase allows 46. Its checked binary32 result is Y=1017, versus required Y=1791: 774 units short. The first crossing needs 83 rises and reaches 1794. These complete finite schedule classes fail even with favorable positioning within the model.

The timing window, Spindel contact band, event membership and H/F/R transitions remain audited/model inputs. The main source-event boundary combines US/JP source receipts and arithmetic; it explicitly does not link a Clight run to those event mirrors. This is a completed conditional obstruction for the named short-window setup, not a maximum over every earlier preparation or enemy history.

### Why terrain aliasing is not transport

Object distance uses full floating-point coordinates. A vertical difference alone can put the Goomba beyond the movement/load thresholds, regardless of X/Z aliasing. Given the audited Mario contact band [2036,2336], the integer hitbox model requires Goomba Y in [1961,2496]; live Spindel surface selection remains unproved. They do not construct physical singleton transport, a repeated raise/reset loop or a same-segment capture/handoff. A failed out-of-range coordinate conversion is not a usable continuation: its trap claim requires the specified invalid-conversion processor controls and their live binding.

### Runtime evidence and the exact open connection

The existing evidence includes source-event audits and exact binary32 schedule computations, not a controller-reached raise/PU-transfer/target replay. Ordinary Goomba approaches and pole-damage receipts belong to the [pole](#review-pole) and [elevator](#review-elevator) chapters and do not supply this setup. No new runtime search was run for this chapter. A supplied event schedule is an arithmetic certificate, not footage of the enemy executing it.

The archived PU certificate proves a compact bounded US transition system, with no exact recorded source pin. Companion countermodels expose PU entry through unclamped air velocity or platform displacement. The active project rechecks selected source facts without importing that archived namespace. The archived result therefore does not establish universal no-PU coverage.

To close the named top-window route in live gameplay, derive its timer/surface window, actual event sequence, collision and load tests from the generated execution. A longer-preparation survivor needs a legitimate repeatable raising cycle outside that window, followed by physical transport, maintained loading, the same live singleton throughout, real capture, useful handoff, every-update no-A coverage and target continuation. Either construct those in one uninterrupted allowed-input run or exclude the reached events/transport combination. Longer independent preparation is still open; the finite 46-rise bound does not rule it out.

<details>
<summary>Goomba raising and PU transport: evidence ledger and remaining connections</summary>

| Claim | Proof or receipt | Assumptions / status | Scope | Remaining limitation |
| --- | --- | --- | --- | --- |
| Short-window H/F/R height obstruction | [Conditional mirror definition](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/GoombaRaising.v#L45); [source-event boundary](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/MainTheorem.v#L1142) | 91-update window and event classification supplied; no linked H/F/R retail execution. | Named schedules only; 31/45/46 rises and checked binary32 heights. | Earlier preparation, repeated cycles and actual event membership remain open. |
| Terrain alias does not supply physical contact/transport | [Goomba raising audit](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/docs/notes/goomba-raising.md#L139); [Spindel contact band](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/GoombaRaising.v#L353); [binary32 rises](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/GoombaRaising.v#L675); [uninhabited transport/capture schemas](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/GoombaRaising.v#L1198) | Full-coordinate distance and the checked actor/Mario dimensions and thresholds. | Source/math kernels for the stated PU/contact geometry. | Live singleton motion, loading, capture and handoff not constructed. |
| Invalid coordinate conversion is not a continuing state | [Nonlocal cast model](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/proofs/Area1NonlocalCastSemantics.v#L176) | Invalid exception enabled and specified processor/cast binding; preservation still required. | Trap semantics under those controls. | Different controls or unbound live calls need their own result. |
| Archived PU barrier has bounded scope | [Archive transfer policy](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/docs/notes/archived-proof-evidence.md#L8); [bounded certificate](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/old-proofs/ssl-parallel-universe/proofs/NoAPressed.v#L510); [companion countermodels](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/old-proofs/ssl-parallel-universe/proofs/MovementSourceFacts.v#L75) | Compact US model; exact source pin not recorded; active namespace does not import archive. | Finished archived bounded model result, with broader movement counterexamples. | Actual unclamped velocity/platform sources and all reached PU-entry histories require coverage. |

</details>

<a id="review-eyerok-particles"></a>

## Eyerok particle displacement

Evidence for this added chapter: repository **cac0adb6b0a72667980df60859bbdb042af66b63**, inspected 6 October 2026. The original four chapters retain their earlier baseline.

### The idea: replace the hand, not ride it

A stale platform pointer is an old Object-pool address still remembered after its owner is removed. Particle displacement tries to allocate a moving fragment into that same slot before Mario consumes the pointer. Then the apply helper would read fragment motion rather than hand motion. This is distinct from ordinary hand rides and from JP cross-area stale-hand reuse in the [Eyerok chapter](#review-eyerok). It requires actual slot reuse in the narrow same-area window, not merely particles nearby.

### The archived result already blocks the named fragments

The audited explosion order is mist, 30 rotating triangles, deletion mark, coins, then end-of-update unload. Marking clears active flags; it does not put the hand slot on the free list. Therefore the dying hand’s own fragments allocate before its slot is available. That timing obstruction is already formalized; this review does not redo it.

The first dying hand retains the exclusive eye lock, keeping its sibling idle. Even allowing the sibling to be selected to open before unload, it still needs at least 30 opening updates plus 40 dying updates: at least 70, versus the one-active-update stale-pointer window. Time stop suppresses platform apply; the archived audited schedule does not turn the pause into extra active allocation opportunities. Neither hand can provide an Eyerok fragment in that model window.

### Exactly what model is proved?

EyerokParticleDisplacement.v uses an explicit finite lifecycle/event relation, with post-unload seeds restricted to an idle or newly selected opening sibling. Its no-replacement theorem and common fragment certificate apply to both checked versions under the audited timing. They are packaged with generated source-shape checks in the archived scenario verdict. They are not a linked refinement of every allocator, callback and platform-apply execution, and are not automatically active-spine coverage. Retired atlas R1 retains precisely that conditional verdict.

The archive also proves that its modeled displacement changes position/facing while preserving stored speeds. Its separate US area-load model clears the saved pointer; JP intentionally differs. Neither statement proves an Eyerok fragment ever occupies the slot. The JP cross-area manifest tests a different stale-slot construction and cannot be counted as a successful same-area Eyerok-particle witness. No dedicated controller-reached fragment installer was verified in this review, and no new runtime test was run.

### What would turn the conditional exclusion into a live one?

Connect every reached relevant allocator and callback to the real free-list/owner generations, the death/eye-lock progression and the first platform apply. Exclude an omitted eligible allocation before apply, and derive that the actual run enters one of the proved post-unload seeds. That would close the named two-hand fragment construction. Unrelated particles, other replacement objects and JP cross-area reuse need separate coverage; the existing 70-versus-one result does not exclude them. The missing step is execution coverage, not the local delay calculation.

<details>
<summary>Eyerok particle displacement: evidence ledger and remaining connections</summary>

| Claim | Proof or receipt | Assumptions / status | Scope | Remaining limitation |
| --- | --- | --- | --- | --- |
| Own fragments cannot take the hand slot | [Archived allocation-order lemmas](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/old-proofs/eyerok-manipulation/proofs/EyerokParticleDisplacement.v#L23); [pinned source audit](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/old-proofs/eyerok-manipulation/generated/source_audit.txt#L118) | Finite event ranking mirrors audited mist/triangle/mark/coins/unload ordering. | Own-hand fragments in the selected same-area explosion. | All reached allocator/callback effects and slot generations still need execution coverage. |
| Sibling fragments miss the reuse window | [70-update delay and window theorem](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/old-proofs/eyerok-manipulation/proofs/EyerokParticleDisplacement.v#L300); [no-replacement theorem](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/old-proofs/eyerok-manipulation/proofs/EyerokParticleDisplacement.v#L348) | Eye lock, 30+40 animation updates, idle/open-selected post-unload seed, one-active-update window. | Both hands in the explicit lifecycle model; no Eyerok-fragment replacement. | Actual seeds and complete live transition membership not derived. |
| Source-shape and model results are packaged | [Common archived scenario verdict](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/old-proofs/eyerok-manipulation/proofs/ExploitScenarioVerdict.v#L4); [archive scope](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/old-proofs/eyerok-manipulation/docs/claim.md#L46); [retired R1 verdict](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/less-than-one-a-press/docs/no-a-route-atlas.md#L1576) | Generated source shapes checked separately from the hand-written lifecycle relation. | Finished archived conditional scenario certificate. | Not an all-history theorem or automatically integrated active-spine proof. |
| Modeled displacement preserves speed; cross-area policy differs | [Displacement and US model](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/old-proofs/eyerok-manipulation/proofs/EyerokParticleDisplacement.v#L375); [JP cross-area manifest](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cac0adb6b0a72667980df60859bbdb042af66b63/SSL-Coq/old-proofs/eyerok-manipulation/instrumentation/results/jp_platform_manifest.md) | Explicit kinematics/area-load model; JP receipt supplied scenes. | Separate displacement semantics and versioned stale-slot evidence. | Does not establish same-area particle installation; unrelated allocation/reuse remains separate. |

</details>
