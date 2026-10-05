# Conditional bounce/collision-copy diagnostic

This bounded observer tests the later collision copy; it is not a backward search or a reachable Ink claim. It uses the existing Windows Wafel 0.8.5 JP runtime and capture. It checks capture poll 500 after 499 controller updates, saves that full scene, then supplies synchronized Mario freefall poses above eight actual actors. Actor/RNG fields are not patched. Each of 16 trials runs 24 consecutive neutral A-released updates from one initial Mario patch.

Run from `SSL-Coq/less-than-one-a-press` in PowerShell:

```powershell
& './build/wafel-pilot/python/python.exe' -X utf8 instrumentation/bounce-collision-lifetime/observe.py --poll 500 --actors 8 --updates 24 --output build/bounce-collision/new/report.json
& './build/wafel-pilot/python/python.exe' -X utf8 instrumentation/bounce-collision-lifetime/receipt.py build/bounce-collision/new/report.json --output build/bounce-collision/new/receipt.json
& './build/wafel-pilot/python/python.exe' -X utf8 instrumentation/bounce-collision-lifetime/test_receipt.py
```

The declared runtime artifacts are located by the existing `wafel-jp-pilot/replay.py`. Do not substitute a different DLL/capture while treating the expected receipt as a matching oracle. Output directories are created by the observer. Limits are one to eight actors and one to 24 updates; the controller-prefix work is separate from those 384 trial updates.

`expected-stock-receipt.json` is the checked summary of `build/bounce-collision/20261004-stock-complete-patches/report.json`. Six Goomba and six Fly Guy poses bounce; Klepto is intangible at the selected scene, and Pokey takes a damage response. All 384 exact end-update Y words have movement=collision=display. All first-update observed MarioState particle-flag fields are zero. This end-update read does not independently observe the caller-local mask at the copy cut. A second run at `build/bounce-collision/20261004-stock-complete-repeat/report.json` matches actor, patch, initial observer, update and filtered action-log fields exactly; run time alone is excluded from this comparison.

The action-entry log records movement and velocity. It does not observe collision/display at that within-update cut, so no subframe collision peak is measured. The largest detected **end-update** collision gap is zero. Supplied Mario poses are conditional, although the surrounding scene follows the original controller trace. The suffix's absence of A presses does not make the patched starting pose a no-A gameplay witness.

Tests reject unsynchronized initial records, skipped update boundaries and A input, and check equal/unequal end-update gap accounting. Keep full reports, hashes and patch fields for a local audit. No stock actor position or dimension is inferred to be player-reachable from this diagnostic.
