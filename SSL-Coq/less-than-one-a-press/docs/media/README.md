# Proof project videos

`ink-arrival-conditional.mp4` is the half-speed highlight from the
[conditional Ink arrival test](../notes/ink-area2-arrival-video.md).
It contains actual emulator-rendered frames with explanatory caption margins.
The supplied test setup is not a clean controller-play witness.

Reproduce it with `instrumentation/jp-lifecycle/run.sh` in recording mode,
then `instrumentation/jp-lifecycle/render-video.sh`. The full recordings,
screenshots and raw logs remain in the ignored build directory. ROMs are not
included.

`western-goomba-path-replay.mp4` reconstructs the exact 901-update
[western-Goomba diagnostic](../../instrumentation/western-goomba-rng/README.md)
from its matching US/JP position traces and generated collision mesh. It is
not emulator footage. The three-second pause at update 847 shows the outside
waypoint; the trace does not reach the rim. Other stock actors appear only as
context markers. The linked diagnostic documents reproduction and checks.
