# Supplemental stock runtime source

The US and JP `audio_external.v` files are generated from the complete, unmodified
`src/audio/external.c` at the same pinned revision as the gameplay units:
`9921382a68bb0c865e5e45eb594d9c64db59b1af`. They use the existing Clight generator,
flags, identifier normalization and CompCert 3.15 toolchain. Do not edit them.

Run `bash pipeline/generate-audio-clight.sh` to regenerate these units, or
`bash pipeline/check-audio-generated.sh` to check byte-for-byte reproduction.
The normal `generated` and `verify-generated` Make targets include both this
supplement and the existing gameplay generation/checks.

These files are not added silently to `selected_clight_target`. That target
still links its original 38 units and declares `play_sound` external. The
`StockSoundRequestFrame` proof executes the supplemental unit's actual
`f_play_sound`: only the request array and byte counter are written. The
callsite theorem explicitly requires resolution to that internal body. It
does not prove the old external oracle implements it, or establish a new
whole-game link/runtime refinement.

Generating the complete audio translation unit reports ignored `volatile`
qualifiers on bit-field accesses in other audio functions. `play_sound` has
no such accesses. This tranche makes no correctness claim about those other
functions or the full audio subsystem.
