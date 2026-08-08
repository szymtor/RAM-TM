# Lax namespace inspection rejects imported and generated declarations

## Summary

`lax build` rejects the Lax20 proof package because its namespace check reports
declarations under `Lax13Proofs`, `Turing.TM2`, `Lax13.Ram`, and `Option` as
declarations of `Lax20Proofs`.

Some reported declarations are extension lemmas authored by Lax20 in an
upstream namespace. Those violations are technically consistent with the
current namespace rule, although repairing them requires a nontrivial API
refactor. Other reported declarations are Lean-generated `match_1.splitter`
declarations for imported definitions. Those have no declaration or name in
the Lax20 source that can be renamed.

The latter behavior appears inconsistent with the specification's statement
that realized lemmas for imported constants are internal details and are
dropped before applying the namespace check.

## Environment

- Lax CLI: `0.1.17`
- Submission: `Lax20`
- Submission toolchain: Lean `v4.30.0`
- Mathlib revision: `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- Upstream word-RAM revision: `8ffd2b0652bc969e0d674b6f6e5f0444f57799f4`

## Reproduction

From the submission root:

```text
lax build --only proofs .
```

The Lean package itself builds successfully, after which Lax reports 98
namespace violations.

Representative diagnostics:

```text
[namespace] proof declaration Turing.TM2.step.match_1.splitter does not carry the namespace prefix `Lax20Proofs`
[namespace] proof declaration Option.getD.match_1.splitter does not carry the namespace prefix `Lax20Proofs`
[namespace] proof declaration Lax13.Ram.Op.value.match_1.splitter does not carry the namespace prefix `Lax20Proofs`
[namespace] proof declaration Lax13Proofs.Imp.Expr.evalB_mono does not carry the namespace prefix `Lax20Proofs`
```

## Two distinct classes of diagnostics

### 1. Explicit extensions of an imported API

The files below deliberately add definitions and theorems to namespaces owned
by `Lax13Proofs`:

- `proofs/Lax20Proofs/TMToRam/CanonicalLayout.lean`
- `proofs/Lax20Proofs/TMToRam/BoundedSemantics.lean`
- `proofs/Lax20Proofs/TMToRam/ValueBounds.lean`

Examples include `Lax13Proofs.Imp.Expr.evalB_mono`,
`Lax13Proofs.Imp.Com.canonicalLayout`, and
`Lax13Proofs.Compile.Layout.bitOverhead`.

These can be moved into Lax20-owned namespaces, but simple substitution of the
enclosing namespace is insufficient. A declaration written as `Expr.foo`
resolves `Expr` to the imported `Lax13Proofs.Imp.Expr` namespace, so Lean still
creates the old fully qualified name. A workaround must:

1. give every extension declaration an explicitly Lax20-owned name;
2. replace dot/field notation such as `e.bitGrowth`, `c.canonicalLayout`, and
   `σ.BitBounded` throughout downstream files; and
3. open/import the new extension namespaces only after their defining modules.

This is a source-compatible API refactor, not a mechanical namespace-line
change.

### 2. Generated declarations for imported definitions

The following names do not occur in the Lax20 source:

- `Turing.TM2.step.match_1.splitter`
- `Option.getD.match_1.splitter`
- `Option.isSome.match_1.splitter`
- `Lax13.Ram.Op.value.match_1.splitter`
- `Lax13.Ram.Instr.effect.match_1.splitter`
- `Lax13.Ram.run.match_1.splitter`

They are generated when Lean realizes match/equation support for imported
definitions. There is no source-level name in Lax20 to substitute. These
diagnostics therefore cannot be repaired by renaming Lax20 declarations.

## Expected behavior

The namespace check should apply to user-level declarations genuinely authored
by the inspected package. Generated support declarations realized for imported
constants should either retain their upstream module ownership or be classified
as internal details and excluded.

This expectation follows the Lax specification's inspection discussion:

> realized lemmas for imported constants are internal details and drop out
> before the namespace test

## Observed behavior

The inspector/build pipeline classifies the generated splitter declarations as
proof-package declarations and then tests their imported namespaces against the
`Lax20Proofs` prefix. This makes a valid source-level rename impossible for
that class of violations.

## Suggested maintainer investigation

1. Inspect the module-of-origin and `Name.isInternalDetail` values reported for
   the generated `match_1.splitter` declarations.
2. Confirm whether Lean 4.30 changed the user/internal classification or module
   attribution of lazily realized matcher declarations.
3. Filter declarations whose user-facing root belongs to an imported package,
   when their realization was generated rather than explicitly declared by the
   submission.
4. Add a regression fixture importing and reducing `Turing.TM2.step` (or a
   small imported pattern-matching definition) without declaring anything
   outside the submission namespace.

## Other issues found and already repaired locally

- The polynomial-time equivalence theorem now has valid Lax `conclusion:`
  metadata and lives under `Lax20Proofs`.
- The corresponding concept claim is a Lax statement axiom.
- Uses of `native_decide` on the RAM-to-TM proof path were replaced by
  kernel-reducible `decide`, removing the associated private native-decide
  axioms.
- Root-module inventories were corrected.
- Scratch Lean files that were unintentionally included in the package
  inventory were removed.

## Separate submission-state warnings

These are independent of the namespace-inspection problem:

- the current folder is not recognized by Lax as being inside a Git repository;
- the required Lax13 record is currently reported as a draft, so registration
  of Lax20 will require Lax13 to be registered first.
