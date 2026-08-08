import Lax20Proofs.RamToTM.PhaseComposition

namespace Lax20Proofs.RamToTM

open Turing TM2

/-! A phase may have several halting exits.  This is needed for lookup:
`found` and `missing` are both genuine runtime outcomes of one finite
program. -/

def AvoidsHalts {K Λ σ : Type} {α : K → Type} [DecidableEq K]
    (program : Λ → TM2.Stmt α Λ σ) :
    ℕ → TM2.Cfg α Λ σ → Prop
  | 0, _ => True
  | n + 1, c =>
      (∀ l, c.l = some l → program l ≠ .halt) ∧
        match TM2.step program c with
        | none => True
        | some c' => AvoidsHalts program n c'

theorem avoidsHalts_of_reaches_labeled {K Λ σ : Type} {α : K → Type}
    [DecidableEq K] (program : Λ → TM2.Stmt α Λ σ)
    {n : ℕ} {c d : TM2.Cfg α Λ σ}
    (hrun : ((fun o => o.bind (TM2.step program))^[n]) (some c) = some d)
    (hd : d.l.isSome) : AvoidsHalts program n c := by
  induction n generalizing c with
  | zero => trivial
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun
      simp only [Option.bind_some] at hrun
      cases hstep : TM2.step program c with
      | none =>
          rw [hstep, iterate_optionBind_none] at hrun
          contradiction
      | some c' =>
          rw [hstep] at hrun
          constructor
          · intro l hlabel hhalt
            rcases c with ⟨label, state, tapes⟩
            simp only at hlabel
            subst label
            have hs := step_at_halt_label program l hhalt state tapes
            rw [hstep] at hs
            have hc' := Option.some.inj hs
            subst c'
            have hnone : TM2.step program
                ({ l := none, var := state, stk := tapes } :
                  TM2.Cfg α Λ σ) = none := rfl
            cases n with
            | zero =>
                simp only [Function.iterate_zero_apply] at hrun
                have heq := Option.some.inj hrun
                subst d
                simp at hd
            | succ n =>
                rw [Function.iterate_succ_apply] at hrun
                simp only [Option.bind_some, hnone]
                  at hrun
                rw [iterate_optionBind_none] at hrun
                contradiction
          · simpa [AvoidsHalts, hstep] using ih hrun

def lensMultiPhaseLeft {α K K' Λ R σ Ω : Type}
    [DecidableEq K] [DecidableEq K']
    (stackMap : StackRenaming K K') (lens : StateLens σ Ω)
    (program : Λ → TM2.Stmt (fun _ : K => α) Λ σ)
    (exit : Λ → Option R) (onExit : Λ → Ω → Ω) :
    Λ → TM2.Stmt (fun _ : K' => α) (Sum Λ R) Ω :=
  fun label => match exit label with
    | some next => .load (onExit label) <| .goto fun _ => .inr next
    | none => lensRenameStmt stackMap lens (program label)

def multiPhaseReturnCfg {α K K' Λ R σ Ω : Type}
    (stackMap : StackRenaming K K') (lens : StateLens σ Ω)
    (next : R) (onExit : Ω → Ω)
    (c : TM2.Cfg (fun _ : K => α) Λ σ) (ambientState : Ω)
    (ambientStacks : K' → List α) :
    TM2.Cfg (fun _ : K' => α) R Ω where
  l := some next
  var := onExit (lens.put ambientState c.var)
  stk := renamedStacks stackMap c.stk ambientStacks

theorem step_lensMultiPhase_nonexit {α K K' Λ R σ Ω : Type}
    [DecidableEq K] [DecidableEq K']
    (stackMap : StackRenaming K K') (lens : StateLens σ Ω)
    (program : Λ → TM2.Stmt (fun _ : K => α) Λ σ)
    (exit : Λ → Option R) (onExit : Λ → Ω → Ω)
    (right : R → TM2.Stmt (fun _ : K' => α) R Ω)
    (c : TM2.Cfg (fun _ : K => α) Λ σ)
    (ambientState : Ω) (ambientStacks : K' → List α)
    (hnone : ∀ l, c.l = some l → exit l = none) :
    TM2.step (liftRightProgram
        (lensMultiPhaseLeft stackMap lens program exit onExit) right)
        (lensRenamedCfg (Λx := R) stackMap lens c ambientState ambientStacks) =
      (TM2.step program c).map
        (fun c' => lensRenamedCfg stackMap lens c' ambientState ambientStacks) := by
  rcases c with ⟨label, localState, tapes⟩
  cases label with
  | none => rfl
  | some label =>
      have h := hnone label rfl
      simp [TM2.step, liftRightProgram, lensMultiPhaseLeft, h, lensRenamedCfg]
      rw [stepAux_lensRenameStmt]
      rfl

theorem iterate_lensMultiPhase {α K K' Λ R σ Ω : Type}
    [DecidableEq K] [DecidableEq K']
    (stackMap : StackRenaming K K') (lens : StateLens σ Ω)
    (program : Λ → TM2.Stmt (fun _ : K => α) Λ σ)
    (exit : Λ → Option R) (onExit : Λ → Ω → Ω)
    (hexitHalt : ∀ l, (exit l).isSome → program l = .halt)
    (right : R → TM2.Stmt (fun _ : K' => α) R Ω)
    (n : ℕ) (c : TM2.Cfg (fun _ : K => α) Λ σ)
    (ambientState : Ω) (ambientStacks : K' → List α)
    (havoid : AvoidsHalts program n c) :
    ((fun o => o.bind (TM2.step
      (liftRightProgram
        (lensMultiPhaseLeft stackMap lens program exit onExit) right)))^[n])
      (some (lensRenamedCfg stackMap lens c ambientState ambientStacks)) =
    lensRenamedOption stackMap lens
      (((fun o => o.bind (TM2.step program))^[n]) (some c))
      ambientState ambientStacks := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [Option.bind_some]
      have hnone : ∀ l, c.l = some l → exit l = none := by
        intro l hl
        cases he : exit l with
        | none => rfl
        | some r =>
            have hh := hexitHalt l (by simp [he])
            exact False.elim (havoid.1 l hl hh)
      rw [step_lensMultiPhase_nonexit stackMap lens program exit onExit right c
        ambientState ambientStacks hnone]
      cases hstep : TM2.step program c with
      | none =>
          simp only [hstep, Option.map_none, Option.bind_none]
          rw [iterate_optionBind_none, iterate_optionBind_none]
          rfl
      | some c' =>
          simp only [hstep, Option.map_some, Option.bind_some]
          apply ih c'
          simpa [AvoidsHalts, hstep] using havoid.2

theorem run_lensMultiPhase_to_right {α K K' Λ R σ Ω : Type}
    [DecidableEq K] [DecidableEq K']
    (stackMap : StackRenaming K K') (lens : StateLens σ Ω)
    (program : Λ → TM2.Stmt (fun _ : K => α) Λ σ)
    (exit : Λ → Option R) (onExit : Λ → Ω → Ω)
    (hexitHalt : ∀ l, (exit l).isSome → program l = .halt)
    (right : R → TM2.Stmt (fun _ : K' => α) R Ω)
    {n : ℕ} {c d : TM2.Cfg (fun _ : K => α) Λ σ}
    (hrun : ((fun o => o.bind (TM2.step program))^[n]) (some c) = some d)
    {done : Λ} {next : R} (hd : d.l = some done)
    (hexit : exit done = some next)
    (ambientState : Ω) (ambientStacks : K' → List α) :
    ((fun o => o.bind (TM2.step
      (liftRightProgram
        (lensMultiPhaseLeft stackMap lens program exit onExit) right)))^[n + 1])
      (some (lensRenamedCfg stackMap lens c ambientState ambientStacks)) =
    some (mapLabelCfg Sum.inr
      (multiPhaseReturnCfg stackMap lens next (onExit done) d
        ambientState ambientStacks)) := by
  have hAvoid := avoidsHalts_of_reaches_labeled program hrun (by simp [hd])
  have hiter := iterate_lensMultiPhase stackMap lens program exit onExit
    hexitHalt right n c ambientState ambientStacks hAvoid
  have hiter' :
      ((fun o => o.bind (TM2.step
        (liftRightProgram
          (lensMultiPhaseLeft stackMap lens program exit onExit) right)))^[n])
        (some (lensRenamedCfg stackMap lens c ambientState ambientStacks)) =
      some (lensRenamedCfg stackMap lens d ambientState ambientStacks) := by
    simpa [lensRenamedOption, hrun] using hiter
  rw [Nat.add_comm, Function.iterate_add_apply, hiter']
  rcases d with ⟨label, localState, tapes⟩
  simp only at hd
  subst label
  simp [TM2.step, liftRightProgram, lensMultiPhaseLeft, hexit,
    lensRenamedCfg, multiPhaseReturnCfg, mapLabelCfg]

end Lax20Proofs.RamToTM
