# Can a backup save restore a target star that active data lacks?

Inspected on 7 October 2026 at proof-repository commit `cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59`. The C and SDK files discussed below are unchanged from the generated-source pin `9921382a68bb0c865e5e45eb594d9c64db59b1af`. The decisive generated save/load/copy bodies agree between US and JP. This is a source and existing-proof audit: no new gameplay, cartridge-interruption test or Coq theorem was run.

## The answer depends on how the backup got its credit

Normal saving can put a legitimately credited star into the backup. It does so by copying the active file, after that file already has the credit. We found no independent stock operation that awards an SSL target bit to backup first.

Starting with the relevant target absent from the permitted save inputs, this backup route cannot be the original source of that credit under the audited ordinary save operations. Reload can restore an earlier credit; it cannot explain the first credit. This does not settle a separate wrong-index collection or live-receiver question: such a producer would credit active first, after which normal saving would copy it.

There is a separate persistent-storage possibility. Startup accepts two individually valid save records without requiring their star bits to agree. An interrupted write could, under additional device conditions, leave a valid erased primary record beside an older valid credited backup. Reloading that backup would restore prior credit. That is not a demonstrated cartridge technique, an uninterrupted controller-only route, or a way to create a target that was never credited in the permitted history. The existing Coq reload exclusion assumes agreement and therefore does not exclude that supplied mismatch.

## Three places to keep separate

The active file is the RAM record gameplay normally reads and changes: `files[fileIndex][0]`. The backup is a second RAM record: `files[fileIndex][1]`. EEPROM is the cartridge's persistent storage; its two file records are read into RAM at startup. Game-over reload copies the RAM backup into RAM active. It does not perform a fresh EEPROM read.

A star bit is a yes/no collection record inside a course byte. The SSL targets use bits 2 and 5. Cannon unlocking uses another bit, and the general cap/key flags are a different field. Clearing those general flags does not clear the SSL target bits.

## What the stock operations do

| Operation | Active and backup effect | Actual source connection |
| --- | --- | --- |
| Collect a normal star | OR its bit into active; backup is unchanged. | [US collection body](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/generated/us_save_file.v#L1783), [US course setter](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/generated/us_save_file.v#L2271), [JP setter](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/generated/jp_save_file.v#L2271). |
| Save a modified file | Sign active, copy active into backup, then request an EEPROM write of both records. | [US save body](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/generated/us_save_file.v#L1192), [JP save body](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/generated/jp_save_file.v#L1192). |
| Erase a file | Clear active, then immediately call save, which clears backup too. | [Erase body](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/generated/us_save_file.v#L1267). |
| Copy a file | Copy the source file's active record into destination active, then immediately save destination. | [Copy body](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/generated/us_save_file.v#L1300); [stock empty-destination menu guard](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/menu/file_select.c#L803). |
| Game-over reload | Copy selected backup into active; leave backup unchanged. | [US reload](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/generated/us_save_file.v#L1529), [JP reload](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/generated/jp_save_file.v#L1529), [game-over scheduler call](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/generated/us_level_update.v#L6009). |
| Startup load and repair | Read EEPROM, check each signature separately; copy the valid record if exactly one is valid. Leave two valid records alone. | [US startup switch](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/generated/us_save_file.v#L1342), [JP startup switch](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/generated/jp_save_file.v#L1342), [repair copy](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/generated/us_save_file.v#L1126). |

The direct named-buffer census covers `src/`, `lib/`, `levels/` and `data/`. Buffer accesses are confined to `save_file.c` and declarations. The other ordinary save writers touch cap information, general flags, cannon status, coin scores or menu data, rather than independently setting an SSL target in backup. A named-field census is not a proof covering every reached alias or external memory effect.

The RAM backup is synchronized **before** the EEPROM write. Therefore a write error by itself does not leave a credited RAM backup beside a cleared RAM active record.

There is a literal temporary mismatch inside erase: an already credited backup remains set just after active is cleared. The same call then performs the mandatory active-to-backup copy before returning to ordinary menu/gameplay processing. The source provides no controller or game-over reload checkpoint between those statements. That internal interval is not a usable gameplay witness.

Similarly, equality is not a perpetual invariant: collecting a star without saving can leave active=1 and backup=0. A better bookkeeping condition at completed operations and reload checks is “if backup has this target, active already has it.” Establishing that condition for every reached actual execution is stronger than this audit.

## The persistent-storage case that remains separate

The loader's validity test checks each record's magic and checksum. Its switch handles no valid copies, primary only and backup only. There is no repair branch for two valid copies. Validity therefore does not imply agreement.

The pinned [SDK long-write loop](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/lib/src/osEepromLongWrite.c#L18) submits successive eight-byte blocks in increasing address order. The [file save routine](https://github.com/n64decomp/sm64/blob/9921382a68bb0c865e5e45eb594d9c64db59b1af/src/game/save_file.c#L252) writes the adjacent active and backup structures in that order.

This permits a conditional description, not a validated exploit: an earlier star is saved in both persisted records; an erase commits the complete valid blank primary record; a reset interrupts before the older credited backup is replaced; boot reads both valid records; and an actual reload consumes backup before another save replaces it. Starting the blank file does not itself force a save: the file-selection and initialization paths contain no mandatory file-save call. A continuous controller replay through the necessary deaths and game over, avoiding intervening save opportunities, has not been recorded. The actual reload branch also requires debug level select disabled, demo input absent and the pending game-over timer expired. With debug level select enabled, that game over redirects before reload; it is not automatically a consumer at the project's granted level-select boundary.

The source connections for those limits are the [new-file initializer](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/generated/us_level_update.v#L7708), [Mario initialization](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/generated/us_mario.v#L11207) and [game-over scheduler guards](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/generated/us_level_update.v#L5969). These are inspected source paths, not a proved whole controller execution.

These snapshots need not contain fabricated bytes or an out-of-bounds game write. But block durability, interruption/reset timing, readback and the consumer continuation have not been tested or connected to the game's Clight execution. The generated program treats the EEPROM routines as external calls. This audit neither assumes arbitrary external effects nor claims they satisfy a hardware contract.

A valid differing pair supplied at the starting boundary is therefore a **conditional reload input**, not evidence that ordinary gameplay produced it. It also fails the project's accepted clean target-save conditions. Prior credit in an old file is not a newly earned target from a history that begins with all permitted target credits absent.

## What Coq already says

| Existing result | What is established | Important premise or missing bridge |
| --- | --- | --- |
| [Clean-entry reload exclusion](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/proofs/CleanEntry.v#L83) | At a clean entry, both backup target bits are clear; copying backup cannot newly collect a target. | [The clean record](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/proofs/CleanEntry.v#L34) includes active bits clear and target-save agreement. It does not derive agreement from arbitrary persisted history. |
| [Certified reload preserves target bits](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/proofs/AreaTransitions.v#L290) | Copying an agreeing backup preserves those bits. | The [certified reload effect](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/proofs/AreaTransitions.v#L144) requires agreement before the event. This is not complete generated-program coverage. |
| [First target transition classification](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/proofs/SourceExhaustiveness.v#L517) | A modeled reload can first set a target only when backup was already set and active was clear. | The explicit incoherent-reload constructor retains this possibility rather than proving it unreachable. |
| [Modeled writers preserve backup](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/proofs/SourceExhaustiveness.v#L578) | The finite collection/reload writer model preserves backup. | That model does not include the stock active-to-backup save operation. It is not an exhaustive real backup-writer theorem. |
| [Reload source checks](https://github.com/tra38/sm64-wmotr-abc-proof/blob/cb99a401b91ecdb1fd54dd26aa4c3e98ac2e3d59/SSL-Coq/less-than-one-a-press/proofs/ClightFacts.v#L168) | Named calls and generated syntax are checked. | Live file index, storage identity and byte-copy effects still need the execution connection. |

No existing result should be reopened as though agreement had not been assumed; neither should that assumption be presented as a proof of every startup.

## What would settle the remaining questions?

For an uninterrupted ordinary-gameplay exclusion, connect the real star setter, save, erase, file copy, repair and reload to their live file/course indices and correctly separated storage. Derive the one-way backup condition at actual consumer checkpoints, including the completed-operation ordering; do not require equality after unsaved collection or at the internal erase clear.

For the separate interrupted-save idea, first choose whether reset and earlier credited cartridge history are in scope. A bounded device model or a non-destructive observation on a disposable save would need to establish the complete valid primary/old backup readback, followed by a save-free real reload. No such check was launched here.

**Current verdict:** ordinary backup bookkeeping supplies no independent first credit in the audited source. Reload from an already coherent clean target-clear state is already conditionally excluded in Coq. A two-valid-copy mismatch after an interrupted persistent write remains a specific untested possibility requiring earlier credit and a separate device/consumer history. No clean no-A target witness or universal live save-history theorem was added.
