# RAM model correction (validated, 2026-09-16)

Public concepts now use registered Lax808846 at
9394e531cc51cb67a0214bca3f9264dfe97ba5c7. Lax concept validation passed (55s).
The deleted Lax865980 archive dependency is replaced by proof-only internal
compiler support under Lax759944Proofs.Legacy; provenance is documented in
LEGACY_RAM_PROVENANCE.md. LegacyRamBridge and LegacyRamProjection are checked.

The direct evaluator handles all eighteen instructions and proves the new
RAM-computability-to-computability direction, with only background axioms.
The new generic virtual compiler and its instruction/termination regressions
pass. The buffered compiler's syntax and ten concrete end-to-end regressions
pass. The complete simulation proof is now checked: all current instructions,
time at most 18*t+6*input.length+26, width v+1, with measured initialization
and terminal cost. All four public endpoints are now checked, including
both generic-time directions and the computability/polynomial equivalences.
The retained legacy library also passes its complete build. The complete proof root passes (3,257 jobs), and all six regression/audit
files pass. Each public proof has only propext, Classical.choice and
Quot.sound as background axioms; the generic-time proof also matches the
exact public statement. Full Lax validation passed on 2026-09-16: seven
concepts, four annotated proofs, and independent kernel replay (23m48s;
24m28s total). The 1,655 unused-helper warnings concern retained internal
compiler APIs and generated lemmas. No proof or dependency errors remain.

This revision is ready to replace draft lax-759944. Downstream submissions
must pin the accepted source revision. Publication progress is recorded in
../RAM_808846_REBASE_STATUS.md; validation logs are in
../migration-tools/*-808846-*.log. Previous validation below concerns only the
earlier model. No registration is permitted.

## Validation commands

From this repository root, run `bash scripts/check-ram-rebase.sh` for the
complete proof-root build and six regression/audit files. Local integration
may set `LAKE_PACKAGES` to an explicit Lake override file; without that
variable the script uses the submission's generated pinned dependencies.
Run `env LEAN_NUM_THREADS=2 lax build . --replay --no-color` for archive
validation and independent kernel replay. Local override results do not
replace that release check.

## Earlier toolchain migration record

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
Published: https://laxarchive.org/lax-759944/ (issue 113), commit
13530db8ae9e82025c8874656ae54ccfcecba566. Archive rebuild passed in
17m13s, public record written in 34s.
Next: no further work required for this draft.
No registration requested or performed.

## Historical record from the original (not validation of this port)
