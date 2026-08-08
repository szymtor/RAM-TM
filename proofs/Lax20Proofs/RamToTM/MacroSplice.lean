import Lax20Proofs.RamToTM.ControlDispatcherMachine

namespace Lax20Proofs.RamToTM

open Turing TM2

/-! A verified macro can be spliced into a larger finite-stack machine.  Its
ordinary labels execute exactly the original program; its distinguished done
label performs one return step into the ambient controller. -/

def spliceLeftProgram {α K Kx Λ Λx σ τ : Type} [DecidableEq K]
    [DecidableEq Λ] [DecidableEq (Sum K Kx)]
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : Sum K Kx => α) (Sum Λ Λx) (σ × τ)) :
    Sum Λ Λx → TM2.Stmt (fun _ : Sum K Kx => α) (Sum Λ Λx) (σ × τ)
  | .inl l =>
      if l = done then .goto fun _ => .inr returnLabel
      else liftLeftStmt (Kx := Kx) (Λx := Λx) (τ := τ) (left l)
  | .inr l => right l

theorem step_spliceLeftProgram_embed {α K Kx Λ Λx σ τ : Type}
    [DecidableEq K] [DecidableEq Λ] [DecidableEq (Sum K Kx)]
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : Sum K Kx => α) (Sum Λ Λx) (σ × τ))
    (c : TM2.Cfg (fun _ : K => α) Λ σ) (ambient : τ)
    (rightStacks : Kx → List α) (h : c.l ≠ some done) :
    TM2.step (spliceLeftProgram left done returnLabel right)
        (embedLeftCfg c ambient rightStacks) =
      (TM2.step left c).map
        (fun c' => embedLeftCfg c' ambient rightStacks) := by
  cases c with
  | mk label state stk =>
      cases label with
      | none => rfl
      | some label =>
          have hlabel : label ≠ done := by
            intro heq
            subst label
            exact h rfl
          simp only [embedLeftCfg, Option.map_some, TM2.step,
            spliceLeftProgram, hlabel, if_false]
          rw [stepAux_liftLeftStmt]
          rfl

def AvoidsDone {α K Λ σ : Type} [DecidableEq K]
    (program : Λ → TM2.Stmt (fun _ : K => α) Λ σ)
    (done : Λ) : ℕ → TM2.Cfg (fun _ : K => α) Λ σ → Prop
  | 0, _ => True
  | n + 1, c => c.l ≠ some done ∧
      match TM2.step program c with
      | none => True
      | some c' => AvoidsDone program done n c'

theorem step_at_halt_label {K Λ σ : Type} {α : K → Type} [DecidableEq K]
    (program : Λ → TM2.Stmt α Λ σ) (done : Λ)
    (hdone : program done = .halt)
    (state : σ) (stk : (k : K) → List (α k)) :
    TM2.step program
      ({ l := some done, var := state, stk := stk } :
        TM2.Cfg α Λ σ) =
      some { l := none, var := state, stk := stk } := by
  simp [TM2.step, hdone]

theorem avoidsDone_of_reaches_done {α K Λ σ : Type} [DecidableEq K]
    (program : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (hdone : program done = .halt) {n : ℕ}
    {c d : TM2.Cfg (fun _ : K => α) Λ σ}
    (hrun : ((fun o => o.bind (TM2.step program))^[n]) (some c) = some d)
    (hd : d.l = some done) : AvoidsDone program done n c := by
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
          have hc : c.l ≠ some done := by
            intro hcDone
            rcases c with ⟨label, state, stk⟩
            simp only at hcDone
            subst label
            have hs := step_at_halt_label program done hdone state stk
            rw [hstep] at hs
            have hc'eq := Option.some.inj hs
            subst c'
            cases n with
            | zero =>
                simp only [Function.iterate_zero_apply] at hrun
                have heq := Option.some.inj hrun
                rw [← heq] at hd
                simp at hd
            | succ n =>
                rw [Function.iterate_succ_apply] at hrun
                simp only [Option.bind_some] at hrun
                change ((fun o => o.bind (TM2.step program))^[n + 1]) none =
                  some d at hrun
                rw [iterate_optionBind_none] at hrun
                contradiction
          refine ⟨hc, ?_⟩
          simpa [AvoidsDone, hstep] using ih hrun

theorem iterate_spliceLeftProgram_embed {α K Kx Λ Λx σ τ : Type}
    [DecidableEq K] [DecidableEq Λ] [DecidableEq (Sum K Kx)]
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : Sum K Kx => α) (Sum Λ Λx) (σ × τ))
    (n : ℕ) (c : TM2.Cfg (fun _ : K => α) Λ σ) (ambient : τ)
    (rightStacks : Kx → List α) (havoid : AvoidsDone left done n c) :
    ((fun o => o.bind (TM2.step (spliceLeftProgram left done returnLabel right)))^[n])
        (some (embedLeftCfg c ambient rightStacks)) =
      embedLeftOption
        (((fun o => o.bind (TM2.step left))^[n]) (some c))
        ambient rightStacks := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [Option.bind_some]
      rw [step_spliceLeftProgram_embed left done returnLabel right c ambient
        rightStacks havoid.1]
      cases hstep : TM2.step left c with
      | none =>
          simp only [hstep, Option.map_none, Option.bind_none]
          rw [iterate_optionBind_none, iterate_optionBind_none]
          rfl
      | some c' =>
          simp only [hstep, Option.map_some, Option.bind_some]
          apply ih c'
          simpa [AvoidsDone, hstep] using havoid.2

theorem transport_iterate_spliceLeftProgram {α K Kx Λ Λx σ τ : Type}
    [DecidableEq K] [DecidableEq Λ] [DecidableEq (Sum K Kx)]
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : Sum K Kx => α) (Sum Λ Λx) (σ × τ))
    {n : ℕ} {c d : TM2.Cfg (fun _ : K => α) Λ σ}
    (hrun : ((fun o => o.bind (TM2.step left))^[n]) (some c) = some d)
    (havoid : AvoidsDone left done n c) (ambient : τ)
    (rightStacks : Kx → List α) :
    ((fun o => o.bind (TM2.step (spliceLeftProgram left done returnLabel right)))^[n])
        (some (embedLeftCfg c ambient rightStacks)) =
      some (embedLeftCfg d ambient rightStacks) := by
  rw [iterate_spliceLeftProgram_embed left done returnLabel right n c ambient
    rightStacks havoid]
  simp [hrun, embedLeftOption]

def spliceReturnCfg {α K Kx Λ Λx σ τ : Type}
    (returnLabel : Λx) (c : TM2.Cfg (fun _ : K => α) Λ σ)
    (ambient : τ) (rightStacks : Kx → List α) :
    TM2.Cfg (fun _ : Sum K Kx => α) (Sum Λ Λx) (σ × τ) :=
  { embedLeftCfg (Λx := Λx) c ambient rightStacks with
      l := some (.inr returnLabel) }

@[simp] theorem step_spliceLeftProgram_done {α K Kx Λ Λx σ τ : Type}
    [DecidableEq K] [DecidableEq Λ] [DecidableEq (Sum K Kx)]
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : Sum K Kx => α) (Sum Λ Λx) (σ × τ))
    (state : σ) (stk : K → List α) (ambient : τ)
    (rightStacks : Kx → List α) :
    TM2.step (spliceLeftProgram left done returnLabel right)
      (embedLeftCfg
        ({ l := some done, var := state, stk := stk } :
          TM2.Cfg (fun _ : K => α) Λ σ)
        ambient rightStacks) =
      some (spliceReturnCfg returnLabel
        ({ l := some done, var := state, stk := stk } :
          TM2.Cfg (fun _ : K => α) Λ σ)
        ambient rightStacks) := by
  simp [TM2.step, spliceLeftProgram, spliceReturnCfg, embedLeftCfg]

theorem step_spliceLeftProgram_done_cfg {α K Kx Λ Λx σ τ : Type}
    [DecidableEq K] [DecidableEq Λ] [DecidableEq (Sum K Kx)]
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : Sum K Kx => α) (Sum Λ Λx) (σ × τ))
    (c : TM2.Cfg (fun _ : K => α) Λ σ) (hc : c.l = some done)
    (ambient : τ) (rightStacks : Kx → List α) :
    TM2.step (spliceLeftProgram left done returnLabel right)
        (embedLeftCfg c ambient rightStacks) =
      some (spliceReturnCfg returnLabel c ambient rightStacks) := by
  rcases c with ⟨label, state, stk⟩
  simp only at hc
  subst label
  exact step_spliceLeftProgram_done left done returnLabel right state stk ambient
    rightStacks

theorem transport_spliceLeftProgram_and_return {α K Kx Λ Λx σ τ : Type}
    [DecidableEq K] [DecidableEq Λ] [DecidableEq (Sum K Kx)]
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : Sum K Kx => α) (Sum Λ Λx) (σ × τ))
    {n : ℕ} {c : TM2.Cfg (fun _ : K => α) Λ σ} {state : σ}
    {stk : K → List α}
    (hrun : ((fun o => o.bind (TM2.step left))^[n]) (some c) =
      some ({ l := some done, var := state, stk := stk } :
        TM2.Cfg (fun _ : K => α) Λ σ))
    (havoid : AvoidsDone left done n c) (ambient : τ)
    (rightStacks : Kx → List α) :
    ((fun o => o.bind (TM2.step (spliceLeftProgram left done returnLabel right)))^[n + 1])
        (some (embedLeftCfg c ambient rightStacks)) =
      some (spliceReturnCfg returnLabel
        ({ l := some done, var := state, stk := stk } :
          TM2.Cfg (fun _ : K => α) Λ σ)
        ambient rightStacks) := by
  let stepO := fun o : Option
      (TM2.Cfg (fun _ : Sum K Kx => α) (Sum Λ Λx) (σ × τ)) =>
    o.bind (TM2.step (spliceLeftProgram left done returnLabel right))
  have hmacro := transport_iterate_spliceLeftProgram left done returnLabel right
    hrun havoid ambient rightStacks
  have hreturn := step_spliceLeftProgram_done left done returnLabel right state stk
    ambient rightStacks
  change (stepO^[n + 1]) (some (embedLeftCfg c ambient rightStacks)) = _
  rw [Nat.add_comm, Function.iterate_add_apply, hmacro]
  simpa [stepO] using hreturn

theorem transport_haltingMacro_and_return {α K Kx Λ Λx σ τ : Type}
    [DecidableEq K] [DecidableEq Λ] [DecidableEq (Sum K Kx)]
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (hdone : left done = .halt) (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : Sum K Kx => α) (Sum Λ Λx) (σ × τ))
    {n : ℕ} {c : TM2.Cfg (fun _ : K => α) Λ σ} {state : σ}
    {stk : K → List α}
    (hrun : ((fun o => o.bind (TM2.step left))^[n]) (some c) =
      some ({ l := some done, var := state, stk := stk } :
        TM2.Cfg (fun _ : K => α) Λ σ))
    (ambient : τ) (rightStacks : Kx → List α) :
    ((fun o => o.bind (TM2.step (spliceLeftProgram left done returnLabel right)))^[n + 1])
        (some (embedLeftCfg c ambient rightStacks)) =
      some (spliceReturnCfg returnLabel
        ({ l := some done, var := state, stk := stk } :
          TM2.Cfg (fun _ : K => α) Λ σ)
        ambient rightStacks) := by
  apply transport_spliceLeftProgram_and_return left done returnLabel right hrun
  exact avoidsDone_of_reaches_done left done hdone hrun rfl

theorem transport_haltingMacroCfg_and_return {α K Kx Λ Λx σ τ : Type}
    [DecidableEq K] [DecidableEq Λ] [DecidableEq (Sum K Kx)]
    (left : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (hdone : left done = .halt) (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : Sum K Kx => α) (Sum Λ Λx) (σ × τ))
    {n : ℕ} {c d : TM2.Cfg (fun _ : K => α) Λ σ}
    (hrun : ((fun o => o.bind (TM2.step left))^[n]) (some c) = some d)
    (hd : d.l = some done) (ambient : τ) (rightStacks : Kx → List α) :
    ((fun o => o.bind (TM2.step (spliceLeftProgram left done returnLabel right)))^[n + 1])
        (some (embedLeftCfg c ambient rightStacks)) =
      some (spliceReturnCfg returnLabel d ambient rightStacks) := by
  let stepO := fun o : Option
      (TM2.Cfg (fun _ : Sum K Kx => α) (Sum Λ Λx) (σ × τ)) =>
    o.bind (TM2.step (spliceLeftProgram left done returnLabel right))
  have hAvoid := avoidsDone_of_reaches_done left done hdone hrun hd
  have hmacro := transport_iterate_spliceLeftProgram left done returnLabel right
    hrun hAvoid ambient rightStacks
  have hreturn := step_spliceLeftProgram_done_cfg left done returnLabel right d hd
    ambient rightStacks
  change (stepO^[n + 1]) (some (embedLeftCfg c ambient rightStacks)) = _
  rw [Nat.add_comm, Function.iterate_add_apply, hmacro]
  simpa [stepO] using hreturn

end Lax20Proofs.RamToTM
