# N64 dust addresses and the knockback continuation

Scope: the pinned `VERSION_US` and `VERSION_JP` programs. This pass proves the
local address-conversion and allocation-header bridge. It does not complete
accepted allocation, a preserving second Mario update, or the full RNG theorem.

## Address result

[`N64AddressRefinement.v`](../../proofs/N64AddressRefinement.v) executes the
**complete original generated** `segmented_to_virtual` function on a numeric
32-bit address. The execution reads the actual segment-table cell, has an empty
trace, and returns with all memory unchanged. No callee-execution premise is
needed for this function.

The three dust scripts occupy these same segmented addresses in both supported
retail images:

| Script | Segmented address | Bytes | Allocation list |
| --- | --- | ---: | ---: |
| `bhvMistParticleSpawner` | `0x130024AC` | 48 | 8 |
| `bhvWhitePuff1` | `0x130024DC` | 36 | 8 |
| `bhvWhitePuff2` | `0x13002500` | 40 | 12 |

The [read-only checker](../../pipeline/check-n64-dust-addresses.py) authenticates
the clean ROM SHA-256 hashes, matches every scalar initializer, and uses both
Mist child references to derive a common behavior-segment ROM base. That base
is `0x219E00` in US and `0x218130` in JP; these are ROM offsets, not runtime
RAM bases. The checker also verifies the pinned linker's segment-19 declaration.
The [finite receipt](../../inputs/n64-dust-addresses.json) contains the inputs
to the Coq transcription checks; the ROMs themselves are not committed.

[`N64DustImage.v`](../../proofs/N64DustImage.v) checks all six complete word lists
against the generated initializers, including the two child references and the
native callback relocation words. Authentication happens outside the proof
kernel. Recording a callback address does not prove its machine-code semantics.

The conversion proof establishes the following for every in-range byte offset:

1. The numeric segmented address selects entry 19, at byte 76 in the checked
   128-byte segment table.
2. With the stated physical-base bounds, addition cannot wrap and the returned
   KSEG0 address is `0x80000000 + base + script_offset + byte_offset`.
3. The three script ranges are disjoint. The bounded decoder returns precisely
   the original generated script's symbolic block and byte offset.
4. Reads through this decoder agree with reads from the unchanged symbolic
   memory. A separate standard `Mem.inject` theorem preserves scalar-word
   reads into a flat **CompCert** memory image. It does not reinterpret pointer
   fragments as integers or establish a complete raw N64 byte-memory model.

[`N64AllocationHeader.v`](../../proofs/N64AllocationHeader.v) connects that
numeric execution and explicit decoding step to the real first two statements
of `create_object`. Those statements read the behavior header and select lists
8, 8 and 12 respectively, with unchanged memory. The header can be obtained
from CompCert's global-initialization theorem; it is not an invented opcode.

The active particle frontier, and therefore the Pedro local-mechanism capstone,
consume these results. The earlier symbolic-pointer obstruction remains true:
an ordinary standard-Clight call with `Vptr` still cannot execute the numeric
shift. The new theorem explicitly encodes the argument, executes the original
numeric function, and decodes its result. It does **not** silently replace that
ordinary call with a different semantic rule.

## Remaining composition work

The former broad address obligation now has a proved local conversion and
header result, with concrete retail script placements. To execute the complete
allocator path, the proof still needs to:

- establish the loader's segment-table value, symbol bindings and continuing
  script-memory image in the chosen runtime state;
- carry the proved representation change through the actual caller/callee
  composition, including stored behavior pointers, relocation reads and native
  callbacks; a whole-program simulation between address representations has
  not been proved;
- execute allocation/free-list changes, object initialization and particle
  acceptance, then the remaining behavior/list updates and ordered RNG draws.

In particular, the existing positive `spawn_particle` theorem's ordinary
allocator premise has not become instantiable under the old symbolic callee
binding. This pass supplies the local bridge needed for a different, explicitly
refined composition. It does not claim a complete N64 semantics refinement.

## Does knockback retain the spot and build speed?

The conditional slide-kick result preserves Mario's position and stored floor
during reflection and the action change, and reverses his forward velocity.
Thus changing to knockback does not itself eject him. The next action update
still runs a ground step; whether its new movement attempts select a blocking
gap remains unproved. Preserving the action transition is not preserving that
whole following update.

The pinned US/JP `act_backward_ground_kb` calls
`common_ground_knockback_action` with animation cutoff 22. That helper first
clamps forward velocity to `[-32, 32]`. Before the cutoff it calls
`apply_landing_accel(m, 0.9f)`. On a flat stored floor, this multiplies forward
velocity by 0.9 and snaps sufficiently small speed to zero. At or after the
cutoff it sets forward velocity to `+0.1` or `-0.1`. This handler provides no
ordinary stick acceleration. Slopes can contribute acceleration before the
friction check, so the clamp is not a universal bound on the final speed after
all helpers. A default floor type also does not by itself prove the floor flat.

Therefore this transition loses the slide action and does not establish a
repeatable way to gather speed in the spot. On the flat-floor case, speed is
lost. Continued confinement and any later return to another action require
their own successive execution proofs. This answer follows the pinned source;
the full knockback execution is still open. Relevant generated functions are in
the [US moving-action unit](../../generated/us_mario_actions_moving.v) and
[JP moving-action unit](../../generated/jp_mario_actions_moving.v).

## Validation

The [validation receipt](../../inputs/n64-address-validation.json) records the
bounded Ubuntu proof build, authenticated ROM/Coq word checks, source coverage,
no-hole checks, capstone assumptions and separate repository discipline audit.
No new emulator execution, ROM edit or gameplay-memory edit is involved.
