import Lax20Proofs.RamToTM.CoreMoveMacro

namespace Lax20Proofs.RamToTM

open Turing TM2

structure StateLens (σ Ω : Type) where
  get : Ω → σ
  put : Ω → σ → Ω
  get_put : ∀ outer inner, get (put outer inner) = inner
  put_get : ∀ outer, put outer (get outer) = outer
  put_put : ∀ outer first second, put (put outer first) second = put outer second

def StateLens.first (σ τ : Type) : StateLens σ (σ × τ) where
  get := Prod.fst
  put := fun outer inner => (inner, outer.2)
  get_put := by intros; rfl
  put_get := by intro outer; cases outer; rfl
  put_put := by intros; rfl

def StateLens.second (σ τ : Type) : StateLens τ (σ × τ) where
  get := Prod.snd
  put := fun outer inner => (outer.1, inner)
  get_put := by intros; rfl
  put_get := by intro outer; cases outer; rfl
  put_put := by intros; rfl

def StateLens.comp {σ τ Ω : Type} (inner : StateLens σ τ)
    (outer : StateLens τ Ω) : StateLens σ Ω where
  get := fun state => inner.get (outer.get state)
  put := fun state value => outer.put state (inner.put (outer.get state) value)
  get_put := by
    intro state value
    rw [outer.get_put, inner.get_put]
  put_get := by
    intro state
    rw [inner.put_get, outer.put_get]
  put_put := by
    intro state first second
    rw [outer.put_put, outer.get_put, inner.put_put]

def lensRenameStmt {α K K' Λ Λx σ Ω : Type} [DecidableEq K]
    [DecidableEq K'] (stackMap : StackRenaming K K') (state : StateLens σ Ω) :
    TM2.Stmt (fun _ : K => α) Λ σ →
      TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) Ω
  | .push k f q => .push (stackMap.encode k) (fun s => f (state.get s))
      (lensRenameStmt stackMap state q)
  | .peek k f q => .peek (stackMap.encode k)
      (fun s a => state.put s (f (state.get s) a))
      (lensRenameStmt stackMap state q)
  | .pop k f q => .pop (stackMap.encode k)
      (fun s a => state.put s (f (state.get s) a))
      (lensRenameStmt stackMap state q)
  | .load f q => .load (fun s => state.put s (f (state.get s)))
      (lensRenameStmt stackMap state q)
  | .branch f q₁ q₂ => .branch (fun s => f (state.get s))
      (lensRenameStmt stackMap state q₁) (lensRenameStmt stackMap state q₂)
  | .goto f => .goto (fun s => .inl (f (state.get s)))
  | .halt => .halt

def lensRenamedCfg {α K K' Λ Λx σ Ω : Type}
    (stackMap : StackRenaming K K') (state : StateLens σ Ω)
    (c : TM2.Cfg (fun _ : K => α) Λ σ) (ambientState : Ω)
    (ambientStacks : K' → List α) :
    TM2.Cfg (fun _ : K' => α) (Sum Λ Λx) Ω where
  l := c.l.map Sum.inl
  var := state.put ambientState c.var
  stk := renamedStacks stackMap c.stk ambientStacks

theorem stepAux_lensRenameStmt {α K K' Λ Λx σ Ω : Type}
    [DecidableEq K] [DecidableEq K'] (stackMap : StackRenaming K K')
    (lens : StateLens σ Ω) (q : TM2.Stmt (fun _ : K => α) Λ σ)
    (localState : σ) (ambientState : Ω) (inner : K → List α)
    (ambientStacks : K' → List α) :
    TM2.stepAux (lensRenameStmt (Λx := Λx) stackMap lens q)
        (lens.put ambientState localState)
        (renamedStacks stackMap inner ambientStacks) =
      lensRenamedCfg stackMap lens (TM2.stepAux q localState inner)
        ambientState ambientStacks := by
  induction q generalizing localState inner with
  | push k f q ih =>
      simp only [lensRenameStmt, TM2.stepAux, lens.get_put, renamedStacks_encode]
      rw [update_renamedStacks]
      exact ih _ _
  | peek k f q ih =>
      simp only [lensRenameStmt, TM2.stepAux, lens.get_put, renamedStacks_encode,
        lens.put_put]
      exact ih _ _
  | pop k f q ih =>
      simp only [lensRenameStmt, TM2.stepAux, lens.get_put, renamedStacks_encode,
        lens.put_put]
      rw [update_renamedStacks]
      exact ih _ _
  | load f q ih =>
      simp only [lensRenameStmt, TM2.stepAux, lens.get_put, lens.put_put]
      exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [lensRenameStmt, TM2.stepAux, lens.get_put]
      cases h : f localState <;> simp [h]
      · exact ih₂ _ _
      · exact ih₁ _ _
  | goto f =>
      simp [lensRenameStmt, TM2.stepAux, lensRenamedCfg, lens.get_put]
  | halt =>
      simp [lensRenameStmt, TM2.stepAux, lensRenamedCfg]

def lensRenamedProgram {α K K' Λ Λx σ Ω : Type} [DecidableEq K]
    [DecidableEq K'] (stackMap : StackRenaming K K') (state : StateLens σ Ω)
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ)
    (right : Λx → TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) Ω) :
    Sum Λ Λx → TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) Ω
  | .inl l => lensRenameStmt stackMap state (left l)
  | .inr l => right l

theorem step_lensRenamedProgram {α K K' Λ Λx σ Ω : Type}
    [DecidableEq K] [DecidableEq K'] (stackMap : StackRenaming K K')
    (lens : StateLens σ Ω) (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ)
    (right : Λx → TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) Ω)
    (c : TM2.Cfg (fun _ : K => α) Λ σ) (ambientState : Ω)
    (ambientStacks : K' → List α) :
    TM2.step (lensRenamedProgram stackMap lens left right)
        (lensRenamedCfg stackMap lens c ambientState ambientStacks) =
      (TM2.step left c).map
        (fun c' => lensRenamedCfg stackMap lens c' ambientState ambientStacks) := by
  rcases c with ⟨label, localState, inner⟩
  cases label with
  | none => rfl
  | some label =>
      simp only [lensRenamedCfg, Option.map_some, TM2.step,
        lensRenamedProgram]
      rw [stepAux_lensRenameStmt]
      rfl

def lensSpliceProgram {α K K' Λ Λx σ Ω : Type} [DecidableEq K]
    [DecidableEq K'] [DecidableEq Λ] (stackMap : StackRenaming K K')
    (lens : StateLens σ Ω)
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) Ω) :
    Sum Λ Λx → TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) Ω
  | .inl l => if l = done then .goto fun _ => .inr returnLabel
      else lensRenameStmt stackMap lens (left l)
  | .inr l => right l

def lensReturnCfg {α K K' Λ Λx σ Ω : Type}
    (stackMap : StackRenaming K K') (lens : StateLens σ Ω)
    (returnLabel : Λx) (c : TM2.Cfg (fun _ : K => α) Λ σ)
    (ambientState : Ω) (ambientStacks : K' → List α) :
    TM2.Cfg (fun _ : K' => α) (Sum Λ Λx) Ω :=
  { lensRenamedCfg (Λx := Λx) stackMap lens c ambientState ambientStacks with
      l := some (.inr returnLabel) }

theorem step_lensSpliceProgram {α K K' Λ Λx σ Ω : Type}
    [DecidableEq K] [DecidableEq K'] [DecidableEq Λ]
    (stackMap : StackRenaming K K') (lens : StateLens σ Ω)
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) Ω)
    (c : TM2.Cfg (fun _ : K => α) Λ σ) (hc : c.l ≠ some done)
    (ambientState : Ω) (ambientStacks : K' → List α) :
    TM2.step (lensSpliceProgram stackMap lens left done returnLabel right)
        (lensRenamedCfg stackMap lens c ambientState ambientStacks) =
      (TM2.step left c).map
        (fun c' => lensRenamedCfg stackMap lens c' ambientState ambientStacks) := by
  rcases c with ⟨label, localState, inner⟩
  cases label with
  | none => rfl
  | some label =>
      have hlabel : label ≠ done := by
        intro h
        subst label
        exact hc rfl
      simp only [lensRenamedCfg, Option.map_some, TM2.step, lensSpliceProgram,
        hlabel, if_false]
      rw [stepAux_lensRenameStmt]
      rfl

theorem step_lensSpliceProgram_done {α K K' Λ Λx σ Ω : Type}
    [DecidableEq K] [DecidableEq K'] [DecidableEq Λ]
    (stackMap : StackRenaming K K') (lens : StateLens σ Ω)
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) Ω)
    (c : TM2.Cfg (fun _ : K => α) Λ σ) (hc : c.l = some done)
    (ambientState : Ω) (ambientStacks : K' → List α) :
    TM2.step (lensSpliceProgram stackMap lens left done returnLabel right)
        (lensRenamedCfg stackMap lens c ambientState ambientStacks) =
      some (lensReturnCfg stackMap lens returnLabel c ambientState ambientStacks) := by
  rcases c with ⟨label, localState, inner⟩
  simp only at hc
  subst label
  simp [TM2.step, lensSpliceProgram, lensRenamedCfg, lensReturnCfg]

def lensRenamedOption {α K K' Λ Λx σ Ω : Type}
    (stackMap : StackRenaming K K') (lens : StateLens σ Ω)
    (c : Option (TM2.Cfg (fun _ : K => α) Λ σ))
    (ambientState : Ω) (ambientStacks : K' → List α) :
    Option (TM2.Cfg (fun _ : K' => α) (Sum Λ Λx) Ω) :=
  c.map fun d => lensRenamedCfg stackMap lens d ambientState ambientStacks

theorem iterate_lensSpliceProgram {α K K' Λ Λx σ Ω : Type}
    [DecidableEq K] [DecidableEq K'] [DecidableEq Λ]
    (stackMap : StackRenaming K K') (lens : StateLens σ Ω)
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) Ω)
    (n : ℕ) (c : TM2.Cfg (fun _ : K => α) Λ σ)
    (ambientState : Ω) (ambientStacks : K' → List α)
    (havoid : AvoidsDone left done n c) :
    ((fun o => o.bind (TM2.step
      (lensSpliceProgram stackMap lens left done returnLabel right)))^[n])
        (some (lensRenamedCfg stackMap lens c ambientState ambientStacks)) =
      lensRenamedOption stackMap lens
        (((fun o => o.bind (TM2.step left))^[n]) (some c))
        ambientState ambientStacks := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [Option.bind_some]
      rw [step_lensSpliceProgram stackMap lens left done returnLabel right c
        havoid.1 ambientState ambientStacks]
      cases hstep : TM2.step left c with
      | none =>
          simp only [hstep, Option.map_none, Option.bind_none]
          rw [iterate_optionBind_none, iterate_optionBind_none]
          rfl
      | some c' =>
          simp only [hstep, Option.map_some, Option.bind_some]
          apply ih c'
          simpa [AvoidsDone, hstep] using havoid.2

theorem transport_lensHaltingMacro_and_return {α K K' Λ Λx σ Ω : Type}
    [DecidableEq K] [DecidableEq K'] [DecidableEq Λ]
    (stackMap : StackRenaming K K') (lens : StateLens σ Ω)
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (hdone : left done = .halt) (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) Ω)
    {n : ℕ} {c d : TM2.Cfg (fun _ : K => α) Λ σ}
    (hrun : ((fun o => o.bind (TM2.step left))^[n]) (some c) = some d)
    (hd : d.l = some done) (ambientState : Ω)
    (ambientStacks : K' → List α) :
    ((fun o => o.bind (TM2.step
      (lensSpliceProgram stackMap lens left done returnLabel right)))^[n + 1])
        (some (lensRenamedCfg stackMap lens c ambientState ambientStacks)) =
      some (lensReturnCfg stackMap lens returnLabel d ambientState ambientStacks) := by
  let stepO := fun o : Option
      (TM2.Cfg (fun _ : K' => α) (Sum Λ Λx) Ω) =>
    o.bind (TM2.step (lensSpliceProgram stackMap lens left done returnLabel right))
  have hAvoid := avoidsDone_of_reaches_done left done hdone hrun hd
  have hmacro := iterate_lensSpliceProgram stackMap lens left done returnLabel right
    n c ambientState ambientStacks hAvoid
  have hreturn := step_lensSpliceProgram_done stackMap lens left done returnLabel
    right d hd ambientState ambientStacks
  have hmacro' :
      ((fun o => o.bind (TM2.step
        (lensSpliceProgram stackMap lens left done returnLabel right)))^[n])
          (some (lensRenamedCfg stackMap lens c ambientState ambientStacks)) =
        some (lensRenamedCfg stackMap lens d ambientState ambientStacks) := by
    rw [hmacro]
    simp [lensRenamedOption, hrun]
  change (stepO^[n + 1])
    (some (lensRenamedCfg stackMap lens c ambientState ambientStacks)) = _
  rw [Nat.add_comm, Function.iterate_add_apply, hmacro']
  simpa [stepO] using hreturn

end Lax20Proofs.RamToTM
