import Lax20Proofs.RamToTM.MacroSpliceInstances

namespace Lax20Proofs.RamToTM

open Turing TM2

/-! A finite local macro may reuse selected stacks of a larger interpreter.
The partial inverse makes this renaming executable and gives the exact update
law needed by the step simulation proof. -/

structure StackRenaming (K K' : Type) where
  encode : K → K'
  decode : K' → Option K
  decode_encode : ∀ k, decode (encode k) = some k
  encode_decode : ∀ {k' k}, decode k' = some k → encode k = k'

theorem StackRenaming.encode_injective {K K' : Type} (e : StackRenaming K K') :
    Function.Injective e.encode := by
  intro a b h
  have := congrArg e.decode h
  simpa [e.decode_encode] using this

def renamedStacks {α K K' : Type} (e : StackRenaming K K')
    (inner : K → List α) (ambient : K' → List α) : K' → List α :=
  fun k' => match e.decode k' with
    | some k => inner k
    | none => ambient k'

@[simp] theorem renamedStacks_encode {α K K' : Type} (e : StackRenaming K K')
    (inner : K → List α) (ambient : K' → List α) (k : K) :
    renamedStacks e inner ambient (e.encode k) = inner k := by
  simp [renamedStacks, e.decode_encode]

theorem update_renamedStacks {α K K' : Type} [DecidableEq K]
    [DecidableEq K'] (e : StackRenaming K K')
    (inner : K → List α) (ambient : K' → List α) (k : K) (xs : List α) :
    Function.update (renamedStacks e inner ambient) (e.encode k) xs =
      renamedStacks e (Function.update inner k xs) ambient := by
  funext j
  cases hdecode : e.decode j with
  | none =>
      have hne : j ≠ e.encode k := by
        intro h
        subst j
        rw [e.decode_encode] at hdecode
        contradiction
      simp [renamedStacks, hdecode, hne]
  | some jlocal =>
      have hj : e.encode jlocal = j := e.encode_decode hdecode
      by_cases h : jlocal = k
      · subst jlocal
        subst j
        simp [renamedStacks, e.decode_encode]
      · have hne : j ≠ e.encode k := by
          intro heq
          rw [← hj] at heq
          exact h (e.encode_injective heq)
        simp [renamedStacks, hdecode, h, hne]

def renameLeftStmt {α K K' Λ Λx σ τ : Type} [DecidableEq K]
    [DecidableEq K'] (e : StackRenaming K K') :
    TM2.Stmt (fun _ : K => α) Λ σ →
      TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) (σ × τ)
  | .push k f q => .push (e.encode k) (fun s => f s.1) (renameLeftStmt e q)
  | .peek k f q => .peek (e.encode k)
      (fun s a => (f s.1 a, s.2)) (renameLeftStmt e q)
  | .pop k f q => .pop (e.encode k)
      (fun s a => (f s.1 a, s.2)) (renameLeftStmt e q)
  | .load f q => .load (fun s => (f s.1, s.2)) (renameLeftStmt e q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1)
      (renameLeftStmt e q₁) (renameLeftStmt e q₂)
  | .goto f => .goto (fun s => .inl (f s.1))
  | .halt => .halt

def renamedCfg {α K K' Λ Λx σ τ : Type} (e : StackRenaming K K')
    (c : TM2.Cfg (fun _ : K => α) Λ σ) (ambientState : τ)
    (ambientStacks : K' → List α) :
    TM2.Cfg (fun _ : K' => α) (Sum Λ Λx) (σ × τ) where
  l := c.l.map Sum.inl
  var := (c.var, ambientState)
  stk := renamedStacks e c.stk ambientStacks

theorem stepAux_renameLeftStmt {α K K' Λ Λx σ τ : Type}
    [DecidableEq K] [DecidableEq K'] (e : StackRenaming K K')
    (q : TM2.Stmt (fun _ : K => α) Λ σ) (state : σ) (ambientState : τ)
    (inner : K → List α) (ambient : K' → List α) :
    TM2.stepAux (renameLeftStmt (Λx := Λx) (τ := τ) e q)
        (state, ambientState) (renamedStacks e inner ambient) =
      renamedCfg e (TM2.stepAux q state inner) ambientState ambient := by
  induction q generalizing state inner with
  | push k f q ih =>
      simp only [renameLeftStmt, TM2.stepAux, renamedStacks_encode]
      rw [update_renamedStacks]
      exact ih _ _
  | peek k f q ih =>
      simp only [renameLeftStmt, TM2.stepAux, renamedStacks_encode]
      exact ih _ _
  | pop k f q ih =>
      simp only [renameLeftStmt, TM2.stepAux, renamedStacks_encode]
      rw [update_renamedStacks]
      exact ih _ _
  | load f q ih =>
      simp only [renameLeftStmt, TM2.stepAux]
      exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [renameLeftStmt, TM2.stepAux]
      cases h : f state <;> simp [h]
      · exact ih₂ _ _
      · exact ih₁ _ _
  | goto f => rfl
  | halt => rfl

def renamedLeftProgram {α K K' Λ Λx σ τ : Type} [DecidableEq K]
    [DecidableEq K'] (e : StackRenaming K K')
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ)
    (right : Λx → TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) (σ × τ)) :
    Sum Λ Λx → TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) (σ × τ)
  | .inl l => renameLeftStmt e (left l)
  | .inr l => right l

theorem step_renamedLeftProgram {α K K' Λ Λx σ τ : Type}
    [DecidableEq K] [DecidableEq K'] (e : StackRenaming K K')
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ)
    (right : Λx → TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) (σ × τ))
    (c : TM2.Cfg (fun _ : K => α) Λ σ) (ambientState : τ)
    (ambientStacks : K' → List α) :
    TM2.step (renamedLeftProgram e left right)
        (renamedCfg e c ambientState ambientStacks) =
      (TM2.step left c).map
        (fun c' => renamedCfg e c' ambientState ambientStacks) := by
  rcases c with ⟨label, state, inner⟩
  cases label with
  | none => rfl
  | some label =>
      simp only [renamedCfg, Option.map_some, TM2.step, renamedLeftProgram]
      rw [stepAux_renameLeftStmt]
      rfl

def renamedSpliceProgram {α K K' Λ Λx σ τ : Type} [DecidableEq K]
    [DecidableEq K'] [DecidableEq Λ] (e : StackRenaming K K')
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) (σ × τ)) :
    Sum Λ Λx → TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) (σ × τ)
  | .inl l => if l = done then .goto fun _ => .inr returnLabel
      else renameLeftStmt e (left l)
  | .inr l => right l

def renamedReturnCfg {α K K' Λ Λx σ τ : Type} (e : StackRenaming K K')
    (returnLabel : Λx) (c : TM2.Cfg (fun _ : K => α) Λ σ)
    (ambientState : τ) (ambientStacks : K' → List α) :
    TM2.Cfg (fun _ : K' => α) (Sum Λ Λx) (σ × τ) :=
  { renamedCfg (Λx := Λx) e c ambientState ambientStacks with
      l := some (.inr returnLabel) }

theorem step_renamedSpliceProgram {α K K' Λ Λx σ τ : Type}
    [DecidableEq K] [DecidableEq K'] [DecidableEq Λ]
    (e : StackRenaming K K')
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) (σ × τ))
    (c : TM2.Cfg (fun _ : K => α) Λ σ) (hc : c.l ≠ some done)
    (ambientState : τ) (ambientStacks : K' → List α) :
    TM2.step (renamedSpliceProgram e left done returnLabel right)
        (renamedCfg e c ambientState ambientStacks) =
      (TM2.step left c).map
        (fun c' => renamedCfg e c' ambientState ambientStacks) := by
  rcases c with ⟨label, state, inner⟩
  cases label with
  | none => rfl
  | some label =>
      have hlabel : label ≠ done := by
        intro h
        subst label
        exact hc rfl
      simp only [renamedCfg, Option.map_some, TM2.step, renamedSpliceProgram,
        hlabel, if_false]
      rw [stepAux_renameLeftStmt]
      rfl

theorem step_renamedSpliceProgram_done {α K K' Λ Λx σ τ : Type}
    [DecidableEq K] [DecidableEq K'] [DecidableEq Λ]
    (e : StackRenaming K K')
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) (σ × τ))
    (c : TM2.Cfg (fun _ : K => α) Λ σ) (hc : c.l = some done)
    (ambientState : τ) (ambientStacks : K' → List α) :
    TM2.step (renamedSpliceProgram e left done returnLabel right)
        (renamedCfg e c ambientState ambientStacks) =
      some (renamedReturnCfg e returnLabel c ambientState ambientStacks) := by
  rcases c with ⟨label, state, inner⟩
  simp only at hc
  subst label
  simp [TM2.step, renamedSpliceProgram, renamedCfg, renamedReturnCfg]

def renamedOption {α K K' Λ Λx σ τ : Type} (e : StackRenaming K K')
    (c : Option (TM2.Cfg (fun _ : K => α) Λ σ))
    (ambientState : τ) (ambientStacks : K' → List α) :
    Option (TM2.Cfg (fun _ : K' => α) (Sum Λ Λx) (σ × τ)) :=
  c.map fun d => renamedCfg e d ambientState ambientStacks

theorem iterate_renamedSpliceProgram {α K K' Λ Λx σ τ : Type}
    [DecidableEq K] [DecidableEq K'] [DecidableEq Λ]
    (e : StackRenaming K K')
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) (σ × τ))
    (n : ℕ) (c : TM2.Cfg (fun _ : K => α) Λ σ)
    (ambientState : τ) (ambientStacks : K' → List α)
    (havoid : AvoidsDone left done n c) :
    ((fun o => o.bind (TM2.step
      (renamedSpliceProgram e left done returnLabel right)))^[n])
        (some (renamedCfg e c ambientState ambientStacks)) =
      renamedOption e
        (((fun o => o.bind (TM2.step left))^[n]) (some c))
        ambientState ambientStacks := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [Option.bind_some]
      rw [step_renamedSpliceProgram e left done returnLabel right c havoid.1
        ambientState ambientStacks]
      cases hstep : TM2.step left c with
      | none =>
          simp only [hstep, Option.map_none, Option.bind_none]
          rw [iterate_optionBind_none, iterate_optionBind_none]
          rfl
      | some c' =>
          simp only [hstep, Option.map_some, Option.bind_some]
          apply ih c'
          simpa [AvoidsDone, hstep] using havoid.2

theorem transport_renamedHaltingMacro_and_return {α K K' Λ Λx σ τ : Type}
    [DecidableEq K] [DecidableEq K'] [DecidableEq Λ]
    (e : StackRenaming K K')
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (hdone : left done = .halt) (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) (σ × τ))
    {n : ℕ} {c d : TM2.Cfg (fun _ : K => α) Λ σ}
    (hrun : ((fun o => o.bind (TM2.step left))^[n]) (some c) = some d)
    (hd : d.l = some done) (ambientState : τ)
    (ambientStacks : K' → List α) :
    ((fun o => o.bind (TM2.step
      (renamedSpliceProgram e left done returnLabel right)))^[n + 1])
        (some (renamedCfg e c ambientState ambientStacks)) =
      some (renamedReturnCfg e returnLabel d ambientState ambientStacks) := by
  let stepO := fun o : Option
      (TM2.Cfg (fun _ : K' => α) (Sum Λ Λx) (σ × τ)) =>
    o.bind (TM2.step (renamedSpliceProgram e left done returnLabel right))
  have hAvoid := avoidsDone_of_reaches_done left done hdone hrun hd
  have hmacro := iterate_renamedSpliceProgram e left done returnLabel right n c
    ambientState ambientStacks hAvoid
  have hreturn := step_renamedSpliceProgram_done e left done returnLabel right d hd
    ambientState ambientStacks
  have hmacro' :
      ((fun o => o.bind (TM2.step
        (renamedSpliceProgram e left done returnLabel right)))^[n])
          (some (renamedCfg e c ambientState ambientStacks)) =
        some (renamedCfg e d ambientState ambientStacks) := by
    rw [hmacro]
    simp [renamedOption, hrun]
  change (stepO^[n + 1]) (some (renamedCfg e c ambientState ambientStacks)) = _
  rw [Nat.add_comm, Function.iterate_add_apply, hmacro']
  simpa [stepO] using hreturn

end Lax20Proofs.RamToTM
