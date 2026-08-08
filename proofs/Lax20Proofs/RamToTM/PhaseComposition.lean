import Lax20Proofs.RamToTM.LabelEmbedding

namespace Lax20Proofs.RamToTM

open Turing TM2

def lensPhaseLeft {α K K' Λ R σ Ω : Type} [DecidableEq K]
    [DecidableEq K'] [DecidableEq Λ] (stackMap : StackRenaming K K')
    (lens : StateLens σ Ω)
    (program : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (entry : R) :
    Λ → TM2.Stmt (fun _ : K' => α) (Sum Λ R) Ω :=
  fun label => if label = done then .goto fun _ => .inr entry
    else lensRenameStmt stackMap lens (program label)

def phaseReturnCfg {α K K' Λ R σ Ω : Type}
    (stackMap : StackRenaming K K') (lens : StateLens σ Ω)
    (entry : R) (c : TM2.Cfg (fun _ : K => α) Λ σ)
    (ambientState : Ω) (ambientStacks : K' → List α) :
    TM2.Cfg (fun _ : K' => α) R Ω where
  l := some entry
  var := lens.put ambientState c.var
  stk := renamedStacks stackMap c.stk ambientStacks

theorem lensSplice_eq_liftRightProgram {α K K' Λ R σ Ω : Type}
    [DecidableEq K] [DecidableEq K'] [DecidableEq Λ]
    (stackMap : StackRenaming K K') (lens : StateLens σ Ω)
    (program : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (entry : R) (right : R → TM2.Stmt (fun _ : K' => α) R Ω) :
    lensSpliceProgram stackMap lens program done entry
        (fun label => mapLabelStmt Sum.inr (right label)) =
      liftRightProgram (lensPhaseLeft stackMap lens program done entry) right := by
  funext label
  cases label <;> rfl

theorem run_lensPhase_to_right {α K K' Λ R σ Ω : Type}
    [DecidableEq K] [DecidableEq K'] [DecidableEq Λ]
    (stackMap : StackRenaming K K') (lens : StateLens σ Ω)
    (program : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (hdone : program done = .halt) (entry : R)
    (right : R → TM2.Stmt (fun _ : K' => α) R Ω)
    {n : ℕ} {c d : TM2.Cfg (fun _ : K => α) Λ σ}
    (hrun : ((fun o => o.bind (TM2.step program))^[n]) (some c) = some d)
    (hd : d.l = some done) (ambientState : Ω)
    (ambientStacks : K' → List α) :
    ((fun o => o.bind (TM2.step
      (liftRightProgram (lensPhaseLeft stackMap lens program done entry) right)))^[n + 1])
      (some (lensRenamedCfg stackMap lens c ambientState ambientStacks)) =
      some (mapLabelCfg Sum.inr
        (phaseReturnCfg stackMap lens entry d ambientState ambientStacks)) := by
  rw [← lensSplice_eq_liftRightProgram stackMap lens program done entry right]
  have h := transport_lensHaltingMacro_and_return stackMap lens program done hdone
    entry (fun label => mapLabelStmt Sum.inr (right label)) hrun hd
    ambientState ambientStacks
  simpa [lensReturnCfg, phaseReturnCfg, mapLabelCfg, lensRenamedCfg] using h

end Lax20Proofs.RamToTM
