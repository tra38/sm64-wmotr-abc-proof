# Late common-landing controller controls

These are finite Wafel JP controls, not a proof of no-A impossibility. Every branch starts at a state reached by the existing validated controller replay. The one-A control intentionally presses A and cannot be used as a no-A witness. The only non-controller setup write is the previously accepted pre-entry level-select flag in the reused adapter.

`wafel_control.py` verifies all 2,483 recorded Area-1 baseline snapshots against the pinned Wafel DLL before/while selecting twelve walking states, separated by at least 90 polls and with forward speed above 10. Each state is saved from that played prefix. Each branch lasts 90 updates: Z alone, or Z followed by one A press on the next update. Other than the controller-pad fields, the script does not write gameplay state. All nine landing action constants are read from the pinned stock header.

The checked receipt has six one-A branches with late long-jump landing samples, zero no-A branches with a late sample in any common-landing action, and no negative depth at the sampled update boundaries. The poll-907 one-A control reaches quicksand type 38 with timer/depth pairs (4, 21.100000381469727) and (5, 17.350000381469727). Late landing is therefore not the same observation as a negative seed.

The baseline input SHA256 and each full branch-input SHA256 are recorded in `expected-controls.json`. The original baseline replay has been compared with the emulator by the earlier pilot. These new branches have only been run in Wafel; their exact internal write checkpoints have not been independently observed in the emulator. The final twelve-state control set is a sample, not coverage of all supports, inputs, re-entry histories or earlier actions.

## Reproduce

Use the existing isolated Python 3.9 and Wafel 0.8.5 JP setup documented in [the pilot](../wafel-jp-pilot/README.md), then run from the Coq project:

```powershell
New-Item -ItemType Directory -Force -Path build/late-common-landing | Out-Null
& './build/wafel-pilot/python/python.exe' instrumentation/late-common-landing/wafel_control.py build/wafel-pilot/capture.bKv95w/inputs.jsonl --output build/late-common-landing/controls.json
```

The runner verifies the existing DLL hash through `create_game`. It also produces the complete controller schedules in the output directory. No ROM, DLL, savestate or private conversation export is published. Compare the JSON output with the committed expected receipt. Do not interpret absent after-update negatives as absence of temporary internal values.
