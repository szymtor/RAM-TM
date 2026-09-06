# Lax51: migration to current Lax13

Validated locally on 2026-09-06: full concept/proof build, statement inspection,
and independent kernel replay all passed.

## What changed

Lax51 now uses Lax13 `92ae2d6275d09b856c02d6f851755590fdcb30ed`, the
cell-to-cell RAM also used by Lax58. The previous draft, commit
`4f6c21aae81fbe8d1233d3ae8358b82b110549b9`, used the accumulator model at
`d35ba57ad420ce6a6d3c763aa7f6a4a8be1d406d`. This is not a migration to Lax67.

The public theorem statements are unchanged. Their programs and executions
refer to current `Lax13.Ram`.

- The forward compiler's layout bound includes its two additional temporary
  cells.
- The reverse Turing simulator retains its verified arithmetic routines through
  proof-internal `Microcode`, extended with word complement.
- `CellToMicrocode.runsTo` translates every current RAM execution of `t` steps
  into exactly `3*t` microcode steps, at the same width and with the same input
  and output. No scratch memory is reserved. It covers all instructions,
  address aliasing, exhausted reads, missing instructions, and width zero.
- Both computability equivalences and both generic time-overhead theorems use
  the updated implementations. The reverse simulator no longer unnecessarily
  imports the forward simulator.

The microcode is an internal proof language, not a replacement public RAM model.
No new proof axioms or `sorry` were introduced. Lax58 and its arena interface
were left unchanged.

## Reproduce validation

From the repository root:

```sh
env LEAN_NUM_THREADS=2 lax build . --replay --no-color
(cd proofs && env LEAN_NUM_THREADS=2 lake env lean ../tests/CellToMicrocode.lean)
```

The full archive check passed for seven concepts and four proof conclusions.
Regression tests passed, and the translation's axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.

The remaining archive warnings are the existing proof-package dependency and
Lax13's supersession by Lax67.
