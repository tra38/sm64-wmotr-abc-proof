# Ink installation: recorded Area-2 arrival

## Answer

**Yes: the known conditional Ink setup bypasses the elevator.** Mario is
displaced sideways before his ordinary entry descent, so he lands on an
upper walkway outside the elevator instead of becoming trapped inside it.
Reaching this setup through no-A gameplay remains open. That upstream
question must not be confused with whether the supplied setup works.

[Watch the half-speed recording](../media/ink-arrival-conditional.mp4)

The recording was made on 2026-09-08 with the authenticated original Japanese
ROM and the existing timer-131 mid-face fixture. The game footage is real;
the initial installation is supplied by the test. The banner states that
limitation throughout. No A input is supplied anywhere in the recorded run.

## Where Mario goes

| Moment in the same execution | Mario position `(X, Y, Z)` | Meaning |
| --- | --- | --- |
| Area-2 entry, before remembered movement, timer 515 | `(0, 5500, 256)` | The ordinary upper-entrance spawn. |
| Immediately after remembered movement, timer 515 | `(365.5927734375, 5500, -1096.8026123046875)` | Already outside the shaft, before the entry descent. |
| First Area-2 controller sample, timer 516 | Same displaced position | Mario's movement, collision and displayed positions now agree. |
| First walkway landing sample, timer 540 | `(337, 4429, -1075)` | A static upper walkway, not the moving elevator. |
| First Puzzle-secret credit, timer 595 | Approximately `(391.87, 3949, -588.82)` | The hidden counter changes from zero to one without A. |

The displacement is approximately `(+365.59, 0, -1352.80)`: it supplies
sideways movement, not additional height. The
[elevator's whole horizontal footprint](area2-elevator-cut.md#fixed-chamber-and-moving-bucket)
has Z between `-204` and `717`; Mario's arriving Z is about 893 units beyond
its nearer edge. The larger fixed entry chamber is also left behind. At the
walkway landing, the recorded floor is static and its height is `4429`.
Thus this is an entry bypass, not a jump out of the elevator bucket.

The ordinary camera briefly looks through nearby scenery during arrival.
The exact first position above is established by the trace, not by guessing
from those obscured frames. The later walkway landing is visible in the
video. This short controller demonstration goes on to one secret, then falls
to the bottom because it supplies no further steering; that is not a failure
to bypass the elevator or an optimized star continuation.

## What was supplied, and what the game did

The existing test supplies the four-pillar count so the top starts spinning.
At its timer 131, it supplies the known three-position boundary: movement
position `(-2200,768,-1024)`, collision position at the upper warp
`(-2048,768,-1024)`, and displayed position `(-1862,1778,-902)`. It also clears
the remembered platform. These preparations are not claimed to come from
controller play. The recording does not develop a way to make them through
memory corruption or code modification.

After that preparation, the game selects the top through the floor retry,
remembers it through the top's disappearance, performs the warp, and applies
its leftover movement on Area-2 entry. The test does not supply an Area-2
position, force an elevator escape, or alter the camera. It supplies stick
`(-127,-96)` for timers 516 through 575, then neutral input. All three existing
A counters finish at zero.

## Escape is established; clean installation is not

This run establishes the conditional elevator bypass and first-secret
continuation. The project also already has a
[separate conditional Act-6 collection receipt](area2-downstream-continuations.md#separate-conditional-act-6-collection-receipt)
from the same supplied boundary, using later ordinary B/Z movement. That
receipt includes the star's save bit changing, not just the five secrets.
It is not the continuation shown in this short recording. Act 3 still needs
its own successful continuation, and neither result supplies clean Ink
installation. Working backward should therefore concentrate on creating the
required earlier setup; the elevator bypass itself is not the missing link.

## Reproduction and evidence

Use the [recording commands](../../instrumentation/jp-lifecycle/README.md#record-the-conditional-ink-arrival).
The new capture's complete extracted trace is byte-for-byte identical to the
prior canonical lifecycle trace. The original endpoint checks, ordered
watched-write checks, first-apply checks and zero-A/secret checks all passed.
No new Coq theorem or clean-reachability claim is added by recording it.

The local capture directory is
`build/instrumentation/jp-lifecycle/video.12Cqks/`. It retains the full raw
17.37-second recording, a labeled normal-speed version, all 521 consecutive
640-by-480 game frames, raw logs and the extracted trace. The checked-in
highlight contains 131 consecutive frames at 15 fps, lasts 8.73 seconds,
and adds caption margins for a 640-by-624 image. Audio is intentionally absent
because this test uses the dummy audio plugin. No video frame is synthesized.

SHA-256 checks:

```text
Authenticated JP ROM (not included):
9cf7a80db321b07a8d461fe536c02c87b7412433953891cdec9191bfad2db317
Unchanged jp_lifecycle_probe.c:
96741d4b20583ac8835141fcad9858ebd7080a444aa510d9cb02314b1de2aea5
Both the new and prior complete extracted traces:
f8fa2be0cd2ed29d91a95c0b3f6287906b771c157b5c7224f3f6da0a43ff94fa
Raw normal-speed recording:
b5cd915cbaec234b3b2e8f6d8822f30f99bba3c6370aac25e991b0fe530bc746
Checked-in half-speed highlight:
d2a34aa347094febd151d8e02181f726d350caa37f48c33b1d38a5277fcd036b
```

[Return to the Ink approach](../no-a-route-atlas.md#route-rank-2)
