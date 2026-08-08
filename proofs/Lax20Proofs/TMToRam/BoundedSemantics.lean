import Lax20Proofs.TMToRam.CanonicalLayout
import Lax13Proofs.Bounds

namespace Lax13Proofs.Imp

/-- A successful bounded expression evaluation remains successful when the
exclusive value bound is increased. -/
theorem Expr.evalB_mono {B C : ℕ} (hBC : B ≤ C) {e : Expr} {σ : Env} {v : ℕ}
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
theorem Cond.evalB_mono {B C : ℕ} (hBC : B ≤ C) {b : Cond} {σ : Env}
    {r : Bool} (h : b.evalB B σ = some r) : b.evalB C σ = some r := by
  cases b with
  | eq e f =>
      rw [Cond.evalB, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n, hn, rfl⟩ := h
      simp [Cond.evalB, Expr.evalB_mono hBC hm, Expr.evalB_mono hBC hn]
  | lt e f =>
      rw [Cond.evalB, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n, hn, rfl⟩ := h
      simp [Cond.evalB, Expr.evalB_mono hBC hm, Expr.evalB_mono hBC hn]

/-- A bounded IMP+ derivation remains valid at every larger value bound. -/
theorem BigStepB.mono {B C : ℕ} (hBC : B ≤ C) {c : Com} {σ σ' : Env} {k : ℕ}
    (h : BigStepB B c σ σ' k) : BigStepB C c σ σ' k := by
  induction h with
  | skip => exact .skip
  | assign he => exact .assign (Expr.evalB_mono hBC he)
  | store hi he hk =>
      exact .store (Expr.evalB_mono hBC hi) (Expr.evalB_mono hBC he) hk
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ite_true hb _ ih => exact .ite_true (Cond.evalB_mono hBC hb) ih
  | ite_false hb _ ih => exact .ite_false (Cond.evalB_mono hBC hb) ih
  | while_true hb _ _ ih₁ ih₂ =>
      exact .while_true (Cond.evalB_mono hBC hb) ih₁ ih₂
  | while_false hb => exact .while_false (Cond.evalB_mono hBC hb)
  | read hin => exact .read hin
  | write he => exact .write (Expr.evalB_mono hBC he)

/-- Every successful ordinary expression evaluation has some finite bound at
which it is also a bounded evaluation. -/
theorem Expr.exists_evalB {e : Expr} {σ : Env} {v : ℕ}
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
      simp [Expr.evalB, Expr.evalB_mono hBC hB, hcell, fit, hvC]
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
      simp [Expr.evalB, Expr.evalB_mono hBD hB, Expr.evalB_mono hCD hC,
        fit, hvD]

/-- Every successful ordinary condition evaluation has some finite bound at
which it is also a bounded evaluation. -/
theorem Cond.exists_evalB {b : Cond} {σ : Env} {r : Bool}
    (h : b.eval σ = some r) : ∃ B, b.evalB B σ = some r := by
  cases b with
  | eq e f =>
      rw [Cond.eval, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n, hn, rfl⟩ := h
      obtain ⟨B, hB⟩ := Expr.exists_evalB hm
      obtain ⟨C, hC⟩ := Expr.exists_evalB hn
      refine ⟨max B C, ?_⟩
      simp [Cond.evalB, Expr.evalB_mono (le_max_left B C) hB,
        Expr.evalB_mono (le_max_right B C) hC]
  | lt e f =>
      rw [Cond.eval, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n, hn, rfl⟩ := h
      obtain ⟨B, hB⟩ := Expr.exists_evalB hm
      obtain ⟨C, hC⟩ := Expr.exists_evalB hn
      refine ⟨max B C, ?_⟩
      simp [Cond.evalB, Expr.evalB_mono (le_max_left B C) hB,
        Expr.evalB_mono (le_max_right B C) hC]

/-- Every finite ordinary IMP+ derivation admits one global finite value
bound.  This lemma is the qualitative bridge; simulation-specific estimates
later replace its existential bound by a uniform explicit one. -/
theorem BigStep.exists_bigStepB {c : Com} {σ σ' : Env} {k : ℕ}
    (h : BigStep c σ σ' k) : ∃ B, BigStepB B c σ σ' k := by
  induction h with
  | skip => exact ⟨1, .skip⟩
  | assign he =>
      obtain ⟨B, hB⟩ := Expr.exists_evalB he
      exact ⟨B, .assign hB⟩
  | store hi he hk =>
      obtain ⟨B, hB⟩ := Expr.exists_evalB hi
      obtain ⟨C, hC⟩ := Expr.exists_evalB he
      exact ⟨max B C, .store
        (Expr.evalB_mono (le_max_left B C) hB)
        (Expr.evalB_mono (le_max_right B C) hC) hk⟩
  | seq _ _ ih₁ ih₂ =>
      obtain ⟨B, hB⟩ := ih₁
      obtain ⟨C, hC⟩ := ih₂
      exact ⟨max B C, .seq
        (hB.mono (le_max_left B C)) (hC.mono (le_max_right B C))⟩
  | ite_true hb _ ih =>
      obtain ⟨B, hB⟩ := Cond.exists_evalB hb
      obtain ⟨C, hC⟩ := ih
      exact ⟨max B C, .ite_true
        (Cond.evalB_mono (le_max_left B C) hB)
        (hC.mono (le_max_right B C))⟩
  | ite_false hb _ ih =>
      obtain ⟨B, hB⟩ := Cond.exists_evalB hb
      obtain ⟨C, hC⟩ := ih
      exact ⟨max B C, .ite_false
        (Cond.evalB_mono (le_max_left B C) hB)
        (hC.mono (le_max_right B C))⟩
  | while_true hb _ _ ih₁ ih₂ =>
      obtain ⟨A, hA⟩ := Cond.exists_evalB hb
      obtain ⟨B, hB⟩ := ih₁
      obtain ⟨C, hC⟩ := ih₂
      let D := max A (max B C)
      exact ⟨D, .while_true
        (Cond.evalB_mono (le_max_left A (max B C)) hA)
        (hB.mono ((le_max_left B C).trans (le_max_right A (max B C))))
        (hC.mono ((le_max_right B C).trans (le_max_right A (max B C))))⟩
  | while_false hb =>
      obtain ⟨B, hB⟩ := Cond.exists_evalB hb
      exact ⟨B, .while_false hB⟩
  | read hin => exact ⟨1, .read hin⟩
  | write he =>
      obtain ⟨B, hB⟩ := Expr.exists_evalB he
      exact ⟨B, .write hB⟩

end Lax13Proofs.Imp
