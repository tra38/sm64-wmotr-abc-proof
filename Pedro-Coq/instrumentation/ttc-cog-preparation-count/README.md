# Preparation-count audit

This is a read-only census of existing US/JP trace receipts plus exact integer
arithmetic for the supplied video's table at 4:00. It neither runs the game nor
constructs or modifies candidate states. It does not certify a state quotient,
reachability, Pedro preservation or an exhaustive preparation count.

Run from the proof repository with Python 3:

```text
python Pedro-Coq/instrumentation/ttc-cog-preparation-count/analyze.py
```

The analyzer authenticates the 11,625-boundary US survey and the 845-boundary
US/JP capture prefixes against the committed RANDOM-sweep receipt. Those
discovery traces remain under ignored `Pedro-Coq/build/cog-placement/`.
It checks contiguous boundaries, fixed neutral inputs, RANDOM mode, no time
stop, Mario's unchanged ledge position, all eight recorded cogs, distinct
global timers and the matching logical US/JP prefix. Pointer fields alone
are omitted for that prefix comparison; this is not whole-memory equality.

The pause filter is precisely `target == 0 && abs(speed) <= 50` on entry.
This selects zero-target approach-to-rest opportunities, not all possible
single stationary updates and not Pedro geometry or complete checkpoints.
The result records per-cog counts and the frame lists for lower/upper/either/
both of slots 29/32, and an example with equal seeds but different pause
eligibility. Overlapping boundaries are counted once in the union.

`VIDEO_ROWS` is a manual transcription of the local reviewed frame, whose hash
is recorded. Its domains are hypotheses of the video, not machine-checked
domains of the real scheduler. The RNG factor 65,114 is separated from the
non-seed product; projected times use the committed two-job RANDOM timing.

The output is metadata only:
`Pedro-Coq/docs/notes/ttc-cog-preparation-count-results.json`.
It includes input and script hashes, explicit limits and exact counts. No ROM,
RAM snapshot or video frame is copied into the output. See the
[findings](../../docs/notes/ttc-cog-preparation-count.md) for interpretation.
