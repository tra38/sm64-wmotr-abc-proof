#!/usr/bin/env bash
set -euo pipefail

# Presentation only: reads an already checked capture, never runs or changes
# the game. The retained raw recording is the full, uncaptioned evidence.
capture_dir="${1:?usage: $0 CAPTURE_DIRECTORY (recorded with LIFECYCLE_CAPTURE_FROM=360)}"
trace="$capture_dir/jp-lifecycle.trace.txt"
font=/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf
test -f "$font"
test -f "$capture_dir/ink-arrival-raw.mp4"
test -f "$capture_dir/shots/super_mario_64-520.png"
grep -q '"nb_read_frames": "521"' "$capture_dir/video-info.json"
grep -q '^PROBE,version=JP,boundary=three-view,installTimer=131,.*graphics=(-1862,1778,-902)$' "$trace"
grep -q '^FIRST_AREA2_POLL,timer=516,area=2,.*marioBits=(43b6cbe0,45abe000,c48919af),' "$trace"
grep -q '^TRACE_A2,timer=540,.*mario=(337.000000,4429.000000,-1075.000000),' "$trace"
grep -q '^RESULT,armed=1,boundaryInstalled=1,explosionFree=1,area2=1,aPressedFrames=0,aDownFrames=0,controllerAFrames=0,triggerEverInactive=1,initialCounter=0,finalCounter=1,maxCounter=1,breakpointArmed=1,firstApplyEntry=1,firstApplyReturn=1$' "$trace"

for mode in full highlight; do
    if [ "$mode" = full ]; then
        first=0
        count=521
        fps=30
        speed='normal speed'
    else
        # Consecutive source render frames 480..610, including the supplied
        # boundary, warp, upper-walkway landing and first Puzzle secret.
        first=120
        count=131
        fps=15
        speed='half speed'
    fi
    filter="pad=iw:ih+144:0:72:black"
    filter+=",drawtext=fontfile=$font:text='INK INSTALLATION - CONDITIONAL TEST':fontsize=21:fontcolor=white:x=(w-tw)/2:y=9"
    filter+=",drawtext=fontfile=$font:text='Setup supplied | JP | $speed | No A presses':fontsize=18:fontcolor=white:x=(w-tw)/2:y=40"
    filter+=",drawtext=fontfile=$font:text='Recorded arrival (365.59, 5500, -1096.80)':fontsize=19:fontcolor=white:x=(w-tw)/2:y=h-59"
    filter+=",drawtext=fontfile=$font:text='Outside shaft - then lands on the upper walkway':fontsize=18:fontcolor=white:x=(w-tw)/2:y=h-29"
    ffmpeg -nostdin -hide_banner -loglevel warning -n \
        -framerate "$fps" -start_number "$first" \
        -i "$capture_dir/shots/super_mario_64-%03d.png" \
        -frames:v "$count" -vf "$filter" \
        -c:v libx264 -crf 18 -preset medium -pix_fmt yuv420p \
        -movflags +faststart "$capture_dir/ink-arrival-$mode.mp4"
done
