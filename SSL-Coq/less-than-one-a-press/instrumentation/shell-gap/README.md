# Can the shell offset stack?

Run `bash instrumentation/shell-gap/run.sh` in the project's WSL environment.
The script extracts eight unchanged functions from pinned stock revision
`9921382a68bb0c865e5e45eb594d9c64db59b1af`, checks them against the pinned source
export, records hashes under ignored `build/instrumentation/shell-gap/`, and
compiles a native US and JP diagnostic. It does not modify a running game.

Both builds passed on 25 September 2026:

```text
shell_gap: outcome_sequences=7760, repeated_calls=7760, early_exits=2, max_gap=45
Scope: supplied helper outcomes; no live terrain, no clean route, no Coq promotion.
```

The actual shell action callers, complete ground/air step loops, ground tilt,
vector copy, angle setter and integer approach function are extracted. Four
ground outcomes and six air outcomes are enumerated in all four-quarter
sequences, at five supplied resulting heights (-8192, 0, 768, the target top
height, 8192). The incoming display starts at 10000. Each case runs twice with
the resulting display retained between calls. Every tested completed ground
call leaves a 45-unit gap; every tested air call leaves 42. A/Z early exits
leave the supplied 45-unit gap unchanged and perform no quarter step.

This deliberately supplies quarter-step outcomes, including sequences that
may never occur in terrain. Helper calls for sound, animation, speed, action
changes, gravity, wind and dismount/lava effects are test doubles with the
limited effects shown in `probe.c`. Therefore this checks the selected
callers' branch/copy behavior under those effects, **not** actual wall
geometry, live helper frames, reachable action histories, or an all-shell
impossibility theorem. The second call also resets its action explicitly;
it is a repetition test, not a claimed gameplay transition. Some enumerated
quarter outcomes terminate the loop, so trailing outcomes are not consumed.
The two compiler warnings about returning local addresses come from the
unchanged decompiled vector helpers; their return values are unused here.

No Wafel gameplay trial or emulator confirmation is claimed. No Coq module
changed and no new Coq audit is claimed. See
`docs/notes/shell-gap-investigation.md` for the source review and remaining
composition questions. The existing normal-copy and arithmetic proofs retain
their existing scope.
