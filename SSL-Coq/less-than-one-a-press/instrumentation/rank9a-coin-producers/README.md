# Rank 9A ordinary-coin diagnostic

Run `node instrumentation/rank9a-coin-producers/check_producers.js` from the
active SSL project. It reads generated US/JP macro and sine-table initializers,
expands the four stock formation recipes and checks all 41 fixed coin actors
against the same generous shaft rectangle used in the Coq census. Ground-row
Y values are **before** their initial floor snap; the X/Z check does not depend
on that snap. Previously collected children can be absent.

It also checks the normal loot launch arithmetic for all 65,536 possible
16-bit random **return values**, then follows a Float32 toss from Y=0 through
16 gravity updates. This is not a sweep of RNG histories or controller inputs.
The two random draws and yaw cannot be treated as independently selectable.

This diagnostic has no walls, floors, water, moving supports, partial updates,
time stop, contact or object allocation. Its toss height is relative to Y=0;
rounding at another absolute Y need not be identical. It neither proves a
global 420-unit height bound nor supplies a clean installation. The Coq launch
proof independently checks the selected generated body and executes its
post-RNG load/store fragment; it does not trust this JavaScript as a theorem.

See [the proof notes](../../docs/notes/rank9a-ordinary-coin-producers.md).

The same checker now performs a separate elevator test. It decodes the
generated elevator spawn command and base vertices, checks all 41 fixed coin
positions against the full footprint enlarged by 150 per horizontal side,
and checks the 320-unit formation-offset bound used by `Area2ElevatorCoins.v`.
The closest fixed coins are 345 horizontal units from the full base. This
does not extend the fixed-position result to Goomba drops or prove that live
positions never change; see the [elevator follow-up](../../docs/notes/rank10a-elevator-coins.md).

## Finishing-attack and coin-flight diagnostic

Run `node instrumentation/rank9a-coin-producers/check_flight.js` for the
follow-up vertical test. It grants the full 30/50-speed knockback apex, a
78-unit loot-floor lift, all 65,536 coin random returns at each of five
starting heights, and 120 moving updates with continued same-floor bouncing.
It checks the conservative Coq ceilings, including the 2517-height Spindel
station case. These heights are test inputs, not reached controller poses;
this is not a complete collision simulation or clean-run receipt.

The separate Coq flight proof now handles rounding at nonzero Float32
positions, arbitrary pauses and explicitly checked lower-support resets.
Higher supports, Goomba re-jumps and other gameplay glitches remain open
unless a live trajectory is projected into those cases. See the
[flight audit](../../docs/notes/rank9a-goomba-coin-flight.md).
