import Lax51Proofs.TMToRam.CanonicalLayout
import Lax13Proofs.Bounds

namespace Lax51Proofs.TMToRam

open Lax13Proofs.Imp

/-- A successful bounded expression evaluation remains successful when the
exclusive value bound is increased. -/
theorem exprEvalBMono {B C : ℕ} (hBC : B ≤ C) {e : Expr} {σ : Env} {v : ℕ}
    (h : e.evalB B σ = some v) : e.evalB C σ = some v := by
  induction e generalizing v with
  | lit n =>
      rw [Expr.evalB, fit_eq_some] at h ⊢
      obtain ⟨rfl, hn⟩ := h
      exact ⟨rfl, hn.trans_le hBC⟩
  | var x =>
      rw [Expr.evalB, fit_eq_some] at h ⊢
      obtain ⟨rfl, hn⟩ := h
      exact ⟨rfl, hn.trans_le hBC⟩
  | get a i ih =>
      rw [Expr.evalB, Option.bind_eq_some_iff] at h
      obtain ⟨k, hk, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨u, hu, hfit⟩ := h
      rw [fit_eq_some] at hfit
      have hfitC : fit C u = some v :=
        fit_eq_some.mpr ⟨hfit.1, hfit.2.trans_le hBC⟩
      simpa [Expr.evalB, ih hk, hu] using hfitC
  | bin op e f ihe ihf =>
      rw [Expr.evalB, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨n, hn, hfit⟩ := h
      rw [fit_eq_some] at hfit
      have hfitC : fit C (op.apply m n) = some v :=
        fit_eq_some.mpr ⟨hfit.1, hfit.2.trans_le hBC⟩
      simpa [Expr.evalB, ihe hm, ihf hn] using hfitC

/-- A successful bounded condition evaluation remains successful when the
exclusive value bound is increased. -/
theorem condEvalBMono {B C : ℕ} (hBC : B ≤ C) {b : Cond} {σ : Env}
    {r : Bool} (h : b.evalB B σ = some r) : b.evalB C σ = some r := by
  cases b with
  | eq e f =>
      rw [Cond.evalB, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n, hn, rfl⟩ := h
      simp [Cond.evalB, exprEvalBMono hBC hm, exprEvalBMono hBC hn]
  | lt e f =>
      rw [Cond.evalB, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n, hn, rfl⟩ := h
      simp [Cond.evalB, exprEvalBMono hBC hm, exprEvalBMono hBC hn]

/-- A bounded IMP+ derivation remains valid at every larger value bound. -/
theorem bigStepBMono {B C : ℕ} (hBC : B ≤ C) {c : Com} {σ σ' : Env} {k : ℕ}
    (h : BigStepB B c σ σ' k) : BigStepB C c σ σ' k := by
  induction h with
  | skip => exact .skip
  | assign he => exact .assign (exprEvalBMono hBC he)
  | store hi he hk =>
      exact .store (exprEvalBMono hBC hi) (exprEvalBMono hBC he) hk
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ite_true hb _ ih => exact .ite_true (condEvalBMono hBC hb) ih
  | ite_false hb _ ih => exact .ite_false (condEvalBMono hBC hb) ih
  | while_true hb _ _ ih₁ ih₂ =>
      exact .while_true (condEvalBMono hBC hb) ih₁ ih₂
  | while_false hb => exact .while_false (condEvalBMono hBC hb)
  | read hin => exact .read hin
  | write he => exact .write (exprEvalBMono hBC he)

/-- Every successful ordinary expression evaluation has some finite bound at
which it is also a bounded evaluation. -/
theorem exprExistsEvalB {e : Expr} {σ : Env} {v : ℕ}
    (h : e.eval σ = some v) : ∃ B, e.evalB B σ = some v := by
  induction e generalizing v with
  | lit n =>
      injection h with hv
      subst v
      exact ⟨n + 1, by simp [Expr.evalB, fit, Nat.lt_succ_self]⟩
  | var x =>
      injection h with hv
      subst v
      exact ⟨σ.vars x + 1, by simp [Expr.evalB, fit, Nat.lt_succ_self]⟩
  | get a i ih =>
      rw [Expr.eval, Option.bind_eq_some_iff] at h
      obtain ⟨k, hk, hv⟩ := h
      obtain ⟨B, hB⟩ := ih hk
      have hcell : (σ.arrs a)[k]? = some v := hv
      let C := max B (v + 1)
      refine ⟨C, ?_⟩
      have hBC : B ≤ C := le_max_left _ _
      have hvC : v < C := (Nat.lt_succ_self v).trans_le (le_max_right _ _)
      simp [Expr.evalB, exprEvalBMono hBC hB, hcell, fit, hvC]
  | bin op e f ihe ihf =>
      rw [Expr.eval, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n, hn, hv⟩ := h
      subst v
      obtain ⟨B, hB⟩ := ihe hm
      obtain ⟨C, hC⟩ := ihf hn
      let D := max (max B C) (op.apply m n + 1)
      refine ⟨D, ?_⟩
      have hBD : B ≤ D := (le_max_left B C).trans (le_max_left _ _)
      have hCD : C ≤ D := (le_max_right B C).trans (le_max_left _ _)
      have hvD : op.apply m n < D :=
        (Nat.lt_succ_self _).trans_le (le_max_right _ _)
      simp [Expr.evalB, exprEvalBMono hBD hB, exprEvalBMono hCD hC,
        fit, hvD]

/-- Every successful ordinary condition evaluation has some finite bound at
which it is also a bounded evaluation. -/
theorem condExistsEvalB {b : Cond} {σ : Env} {r : Bool}
    (h : b.eval σ = some r) : ∃ B, b.evalB B σ = some r := by
  cases b with
  | eq e f =>
      rw [Cond.eval, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n, hn, rfl⟩ := h
      obtain ⟨B, hB⟩ := exprExistsEvalB hm
      obtain ⟨C, hC⟩ := exprExistsEvalB hn
      refine ⟨max B C, ?_⟩
      simp [Cond.evalB, exprEvalBMono (le_max_left B C) hB,
        exprEvalBMono (le_max_right B C) hC]
  | lt e f =>
      rw [Cond.eval, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n, hn, rfl⟩ := h
      obtain ⟨B, hB⟩ := exprExistsEvalB hm
      obtain ⟨C, hC⟩ := exprExistsEvalB hn
      refine ⟨max B C, ?_⟩
      simp [Cond.evalB, exprEvalBMono (le_max_left B C) hB,
        exprEvalBMono (le_max_right B C) hC]

/-- Every finite ordinary IMP+ derivation admits one global finite value
bound.  This lemma is the qualitative bridge; simulation-specific estimates
later replace its existential bound by a uniform explicit one. -/
theorem bigStepExistsBigStepB {c : Com} {σ σ' : Env} {k : ℕ}
    (h : BigStep c σ σ' k) : ∃ B, BigStepB B c σ σ' k := by
  induction h with
  | skip => exact ⟨1, .skip⟩
  | assign he =>
      obtain ⟨B, hB⟩ := exprExistsEvalB he
      exact ⟨B, .assign hB⟩
  | store hi he hk =>
      obtain ⟨B, hB⟩ := exprExistsEvalB hi
      obtain ⟨C, hC⟩ := exprExistsEvalB he
      exact ⟨max B C, .store
        (exprEvalBMono (le_max_left B C) hB)
        (exprEvalBMono (le_max_right B C) hC) hk⟩
  | seq _ _ ih₁ ih₂ =>
      obtain ⟨B, hB⟩ := ih₁
      obtain ⟨C, hC⟩ := ih₂
      exact ⟨max B C, .seq
        (bigStepBMono (le_max_left B C) hB)
        (bigStepBMono (le_max_right B C) hC)⟩
  | ite_true hb _ ih =>
      obtain ⟨B, hB⟩ := condExistsEvalB hb
      obtain ⟨C, hC⟩ := ih
      exact ⟨max B C, .ite_true
        (condEvalBMono (le_max_left B C) hB)
        (bigStepBMono (le_max_right B C) hC)⟩
  | ite_false hb _ ih =>
      obtain ⟨B, hB⟩ := condExistsEvalB hb
      obtain ⟨C, hC⟩ := ih
      exact ⟨max B C, .ite_false
        (condEvalBMono (le_max_left B C) hB)
        (bigStepBMono (le_max_right B C) hC)⟩
  | while_true hb _ _ ih₁ ih₂ =>
      obtain ⟨A, hA⟩ := condExistsEvalB hb
      obtain ⟨B, hB⟩ := ih₁
      obtain ⟨C, hC⟩ := ih₂
      let D := max A (max B C)
      exact ⟨D, .while_true
        (condEvalBMono (le_max_left A (max B C)) hA)
        (bigStepBMono ((le_max_left B C).trans (le_max_right A (max B C))) hB)
        (bigStepBMono ((le_max_right B C).trans (le_max_right A (max B C))) hC)⟩
  | while_false hb =>
      obtain ⟨B, hB⟩ := condExistsEvalB hb
      exact ⟨B, .while_false hB⟩
  | read hin => exact ⟨1, .read hin⟩
  | write he =>
      obtain ⟨B, hB⟩ := exprExistsEvalB he
      exact ⟨B, .write hB⟩

end Lax51Proofs.TMToRam
