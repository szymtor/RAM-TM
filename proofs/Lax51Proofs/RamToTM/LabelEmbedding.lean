import Lax51Proofs.RamToTM.GlobalMacroExecutions

namespace Lax51Proofs.RamToTM

open Turing TM2

def mapLabelStmt {K Λ Λ' σ : Type} {α : K → Type} [DecidableEq K]
    (encode : Λ → Λ') :
    TM2.Stmt α Λ σ → TM2.Stmt α Λ' σ
  | .push k f q => .push k f (mapLabelStmt encode q)
  | .peek k f q => .peek k f (mapLabelStmt encode q)
  | .pop k f q => .pop k f (mapLabelStmt encode q)
  | .load f q => .load f (mapLabelStmt encode q)
  | .branch f q₁ q₂ => .branch f (mapLabelStmt encode q₁) (mapLabelStmt encode q₂)
  | .goto f => .goto fun s => encode (f s)
  | .halt => .halt

def mapLabelCfg {K Λ Λ' σ : Type} {α : K → Type} (encode : Λ → Λ')
    (c : TM2.Cfg α Λ σ) : TM2.Cfg α Λ' σ where
  l := c.l.map encode
  var := c.var
  stk := c.stk

@[simp] theorem mapLabelCfg_var {K Λ Λ' σ : Type} {α : K → Type}
    (encode : Λ → Λ') (c : TM2.Cfg α Λ σ) :
    (mapLabelCfg encode c).var = c.var := rfl

@[simp] theorem mapLabelCfg_stk {K Λ Λ' σ : Type} {α : K → Type}
    (encode : Λ → Λ') (c : TM2.Cfg α Λ σ) :
    (mapLabelCfg encode c).stk = c.stk := rfl

theorem stepAux_mapLabelStmt {K Λ Λ' σ : Type} {α : K → Type} [DecidableEq K]
    (encode : Λ → Λ') (q : TM2.Stmt α Λ σ)
    (state : σ) (tapes : (k : K) → List (α k)) :
    TM2.stepAux (mapLabelStmt encode q) state tapes =
      mapLabelCfg encode (TM2.stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f q ih => simp only [mapLabelStmt, TM2.stepAux]; exact ih _ _
  | peek k f q ih => simp only [mapLabelStmt, TM2.stepAux]; exact ih _ _
  | pop k f q ih => simp only [mapLabelStmt, TM2.stepAux]; exact ih _ _
  | load f q ih => simp only [mapLabelStmt, TM2.stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [mapLabelStmt, TM2.stepAux]
      cases h : f state <;> simp [h]
      · exact ih₂ _ _
      · exact ih₁ _ _
  | goto f => rfl
  | halt => rfl

def liftRightProgram {α K Λx Λ σ : Type} [DecidableEq K]
    (left : Λx → TM2.Stmt (fun _ : K => α) (Sum Λx Λ) σ)
    (right : Λ → TM2.Stmt (fun _ : K => α) Λ σ) :
    Sum Λx Λ → TM2.Stmt (fun _ : K => α) (Sum Λx Λ) σ
  | .inl l => left l
  | .inr l => mapLabelStmt Sum.inr (right l)

theorem step_liftRightProgram {α K Λx Λ σ : Type} [DecidableEq K]
    (left : Λx → TM2.Stmt (fun _ : K => α) (Sum Λx Λ) σ)
    (right : Λ → TM2.Stmt (fun _ : K => α) Λ σ)
    (c : TM2.Cfg (fun _ : K => α) Λ σ) :
    TM2.step (liftRightProgram left right) (mapLabelCfg Sum.inr c) =
      (TM2.step right c).map (mapLabelCfg Sum.inr) := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => rfl
  | some label =>
      simp only [mapLabelCfg, Option.map_some, TM2.step, liftRightProgram]
      rw [stepAux_mapLabelStmt]
      rfl

def mapLabelOption {α K Λ Λ' σ : Type} (encode : Λ → Λ')
    (c : Option (TM2.Cfg (fun _ : K => α) Λ σ)) :
    Option (TM2.Cfg (fun _ : K => α) Λ' σ) := c.map (mapLabelCfg encode)

theorem iterate_liftRightProgram {α K Λx Λ σ : Type} [DecidableEq K]
    (left : Λx → TM2.Stmt (fun _ : K => α) (Sum Λx Λ) σ)
    (right : Λ → TM2.Stmt (fun _ : K => α) Λ σ)
    (n : ℕ) (c : TM2.Cfg (fun _ : K => α) Λ σ) :
    ((fun o => o.bind (TM2.step (liftRightProgram left right)))^[n])
      (some (mapLabelCfg Sum.inr c)) =
      mapLabelOption Sum.inr
        (((fun o => o.bind (TM2.step right))^[n]) (some c)) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [Option.bind_some, step_liftRightProgram]
      cases hstep : TM2.step right c with
      | none =>
          simp only [Option.map_none, Option.bind_none]
          rw [iterate_optionBind_none, iterate_optionBind_none]
          rfl
      | some c' =>
          simp only [Option.map_some, Option.bind_some]
          exact ih c'

theorem transport_iterate_liftRightProgram {α K Λx Λ σ : Type}
    [DecidableEq K]
    (left : Λx → TM2.Stmt (fun _ : K => α) (Sum Λx Λ) σ)
    (right : Λ → TM2.Stmt (fun _ : K => α) Λ σ)
    {n : ℕ} {c d : TM2.Cfg (fun _ : K => α) Λ σ}
    (hrun : ((fun o => o.bind (TM2.step right))^[n]) (some c) = some d) :
    ((fun o => o.bind (TM2.step (liftRightProgram left right)))^[n])
      (some (mapLabelCfg Sum.inr c)) = some (mapLabelCfg Sum.inr d) := by
  rw [iterate_liftRightProgram]
  simp [mapLabelOption, hrun]

theorem chain_liftRightProgram {α K Λx Λ σ : Type} [DecidableEq K]
    (left : Λx → TM2.Stmt (fun _ : K => α) (Sum Λx Λ) σ)
    (right : Λ → TM2.Stmt (fun _ : K => α) Λ σ)
    {m n : ℕ} {a : TM2.Cfg (fun _ : K => α) (Sum Λx Λ) σ}
    {b c : TM2.Cfg (fun _ : K => α) Λ σ}
    (hfirst :
      ((fun o => o.bind (TM2.step (liftRightProgram left right)))^[m])
        (some a) = some (mapLabelCfg Sum.inr b))
    (hright : ((fun o => o.bind (TM2.step right))^[n]) (some b) = some c) :
    ((fun o => o.bind (TM2.step (liftRightProgram left right)))^[m + n])
      (some a) = some (mapLabelCfg Sum.inr c) := by
  have hlift := transport_iterate_liftRightProgram left right hright
  rw [Nat.add_comm, Function.iterate_add_apply, hfirst, hlift]

end Lax51Proofs.RamToTM
