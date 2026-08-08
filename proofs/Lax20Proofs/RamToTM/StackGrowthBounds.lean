import Lax20Proofs.RamToTM.CyclicEmbedding

namespace Lax20Proofs.RamToTM

open Turing TM2

def stmtPushCount {K Λ σ : Type} {Γ : K → Type} :
    TM2.Stmt Γ Λ σ → Nat
  | .push _ _ q => stmtPushCount q + 1
  | .peek _ _ q => stmtPushCount q
  | .pop _ _ q => stmtPushCount q
  | .load _ q => stmtPushCount q
  | .branch _ q₁ q₂ => max (stmtPushCount q₁) (stmtPushCount q₂)
  | .goto _ | .halt => 0

theorem stepAux_stack_length_le {K Λ σ : Type} {Γ : K → Type}
    [DecidableEq K] (q : TM2.Stmt Γ Λ σ) (state : σ)
    (tapes : ∀ k, List (Γ k)) (stack : K) :
    ((TM2.stepAux q state tapes).stk stack).length ≤
      (tapes stack).length + stmtPushCount q := by
  induction q generalizing state tapes with
  | push k f q ih =>
      simp only [TM2.stepAux, stmtPushCount]
      have h := ih state (Function.update tapes k (f state :: tapes k))
      by_cases hk : stack = k
      · subst k
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simp [hk] at h
        exact h.trans (by omega)
  | peek k f q ih =>
      simpa [stmtPushCount] using ih (f state (tapes k).head?) tapes
  | pop k f q ih =>
      simp only [TM2.stepAux, stmtPushCount]
      have h := ih (f state (tapes k).head?)
        (Function.update tapes k (tapes k).tail)
      by_cases hk : stack = k
      · subst k
        simp at h
        exact h.trans (by simp)
      · simpa [hk] using h
  | load f q ih => simpa [stmtPushCount] using ih (f state) tapes
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [TM2.stepAux, stmtPushCount]
      cases h : f state
      · exact (ih₂ state tapes).trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
      · exact (ih₁ state tapes).trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
  | goto f => simp [stmtPushCount]
  | halt => simp [stmtPushCount]

def programPushBound {K Λ σ : Type} {Γ : K → Type}
    [Fintype Λ] (program : Λ → TM2.Stmt Γ Λ σ) : Nat :=
  ∑ label : Λ, stmtPushCount (program label)

theorem stmtPushCount_le_programPushBound {K Λ σ : Type} {Γ : K → Type}
    [Fintype Λ] [DecidableEq Λ]
    (program : Λ → TM2.Stmt Γ Λ σ) (label : Λ) :
    stmtPushCount (program label) ≤ programPushBound program := by
  unfold programPushBound
  exact Finset.single_le_sum
    (f := fun label => stmtPushCount (program label))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ label)

theorem step_stack_length_le {K Λ σ : Type} {Γ : K → Type}
    [DecidableEq K] [Fintype Λ] [DecidableEq Λ]
    (program : Λ → TM2.Stmt Γ Λ σ) (c d : TM2.Cfg Γ Λ σ)
    (hstep : TM2.step program c = some d) (stack : K) :
    (d.stk stack).length ≤
      (c.stk stack).length + programPushBound program := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => simp [TM2.step] at hstep
  | some label =>
      simp only [TM2.step, Option.some.injEq] at hstep
      subst d
      exact (stepAux_stack_length_le (program label) state tapes stack).trans
        (Nat.add_le_add_left
          (stmtPushCount_le_programPushBound program label) _)

theorem iterate_stack_length_le {K Λ σ : Type} {Γ : K → Type}
    [DecidableEq K] [Fintype Λ] [DecidableEq Λ]
    (program : Λ → TM2.Stmt Γ Λ σ) (n : Nat)
    (c d : TM2.Cfg Γ Λ σ)
    (hrun : ((fun o => o.bind (TM2.step program))^[n]) (some c) = some d)
    (stack : K) :
    (d.stk stack).length ≤
      (c.stk stack).length + n * programPushBound program := by
  induction n generalizing c with
  | zero =>
      simp only [Function.iterate_zero_apply, Option.some.injEq] at hrun
      subst d
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun
      simp only [Option.bind_some] at hrun
      cases hs : TM2.step program c with
      | none =>
          simp only [hs, Option.bind_none] at hrun
          rw [iterate_optionBind_none] at hrun
          contradiction
      | some c' =>
          simp only [hs, Option.bind_some] at hrun
          have hfirst := step_stack_length_le program c c' hs stack
          have hrest := ih c' hrun
          calc
            (d.stk stack).length
                ≤ (c'.stk stack).length + n * programPushBound program := hrest
            _ ≤ ((c.stk stack).length + programPushBound program) +
                n * programPushBound program :=
              Nat.add_le_add_right hfirst _
            _ = (c.stk stack).length + Nat.succ n * programPushBound program := by
              simp [Nat.succ_eq_add_one, Nat.add_mul, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm]

end Lax20Proofs.RamToTM
