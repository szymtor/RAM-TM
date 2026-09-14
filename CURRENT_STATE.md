# Lean 4.33 draft migration

Original draft: lax-51. New local draft: lax-759944; branch lean-4.33.
Independent draft with an abstract link to the original, without supersedes.

The full concepts and proof package build passed under Lean 4.33 (3224 jobs).
The TuringRamEquivalence module, Turing-machine-to-RAM polynomial-time and
computability theorems, low-level RAM-to-TM arithmetic, lookup, operands,
and instruction proofs compile. FiniteSimulation and all assembly modules now pass.
Lax validation and kernel replay passed: 7 concepts, 4 annotated proofs,
all assumption lists empty. Total 8m01s, replay 7m49s.
The 1028 unused-helper warnings cover inherited API, historical simulation
implementations, and generated lemmas; these are intentionally retained
for compatibility and downstream reuse. The word-RAM proof dependency is intentional.

The existing tests/CellToMicrocode.lean regression passed: zero-width,
branches, exhausted input, missing instructions, address normalization,
and three axiom audits (standard background axioms only).
Compatibility edits restore elaboration transparency for generated finite
instances and dependent aliases, use simpa using! for old matching behavior,
and adjust proof tactics to changed simplification results. Concepts have
only a local elaboration-option change; mathematical statements are retained.

Logs: ../migration-tools/ram-proof-build.log, ram-compat-progress.log,
ram-regression.log. The compatibility build loop stops for unfamiliar errors.
Next: push and submit the validated new draft,
then pin its published commit in canonical-encodings-v4-33.
No archive submission or registration performed for this new draft yet.

## Historical record from the original (not validation of this port)

