import Lax20Proofs.RamToTM.FiniteSimulation

namespace Lax20Proofs.RamToTM

open Turing TM2
open Lax20.BinaryWordEncoding

noncomputable section

inductive WrapperStack
  | input
  | output
  | core (stack : CoreStack)
  deriving DecidableEq, Fintype, Inhabited

def WrapperAlphabet : WrapperStack -> Type
  | .input | .output => Symbol
  | .core _ => SparseSymbol

instance (k : WrapperStack) : DecidableEq (WrapperAlphabet k) := by
  cases k <;> simp [WrapperAlphabet] <;> infer_instance

instance (k : WrapperStack) : Fintype (WrapperAlphabet k) := by
  cases k <;> simp [WrapperAlphabet] <;> infer_instance

instance (k : WrapperStack) : Inhabited (WrapperAlphabet k) := by
  cases k <;> simp [WrapperAlphabet] <;> infer_instance

structure WrapperState (N : Nat) where
  core : FullInterpreterState N := default
  heldInput : Option Symbol := none
  heldSparse : Option SparseSymbol := none
  flag : Bool := false
  active : Bool := false
  deriving DecidableEq, Fintype, Inhabited

def WrapperState.coreLens {N : Nat} :
    StateLens (FullInterpreterState N) (WrapperState N) where
  get := WrapperState.core
  put := fun s core => {s with core}
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def wrapperCoreStacks (inner : CoreStack -> List SparseSymbol)
    (externalInput externalOutput : List Symbol) :
    (k : WrapperStack) -> List (WrapperAlphabet k)
  | .input => externalInput
  | .output => externalOutput
  | .core k => inner k

theorem update_wrapperCoreStacks (inner : CoreStack → List SparseSymbol)
    (externalInput externalOutput : List Symbol) (k : CoreStack)
    (xs : List SparseSymbol) :
    Function.update (wrapperCoreStacks inner externalInput externalOutput)
        (.core k) xs =
      wrapperCoreStacks (Function.update inner k xs)
        externalInput externalOutput := by
  funext stack
  cases stack with
  | input | output => simp [wrapperCoreStacks, Function.update]
  | core stack =>
      by_cases h : stack = k
      · subst stack
        simp [wrapperCoreStacks, Function.update]
      · simp [wrapperCoreStacks, Function.update, h]

def liftCoreStmt {N : Nat} {L X : Type}
    (stmt : TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N)) :
    TM2.Stmt WrapperAlphabet (Sum L X) (WrapperState N) :=
  match stmt with
  | .push k f q => .push (.core k) (fun s => f s.core) (liftCoreStmt q)
  | .peek k f q => .peek (.core k)
      (fun s a => WrapperState.coreLens.put s (f s.core a)) (liftCoreStmt q)
  | .pop k f q => .pop (.core k)
      (fun s a => WrapperState.coreLens.put s (f s.core a)) (liftCoreStmt q)
  | .load f q => .load
      (fun s => WrapperState.coreLens.put s (f s.core)) (liftCoreStmt q)
  | .branch f q₁ q₂ => .branch (fun s => f s.core)
      (liftCoreStmt q₁) (liftCoreStmt q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.core))
  | .halt => .halt

def liftCoreCfg {N : Nat} {L X : Type}
    (c : TM2.Cfg (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (ambient : WrapperState N) (externalInput externalOutput : List Symbol) :
    TM2.Cfg WrapperAlphabet (Sum L X) (WrapperState N) where
  l := c.l.map Sum.inl
  var := WrapperState.coreLens.put ambient c.var
  stk := wrapperCoreStacks c.stk externalInput externalOutput

theorem stepAux_liftCoreStmt {N : Nat} {L X : Type}
    (stmt : TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (core : FullInterpreterState N) (inner : CoreStack -> List SparseSymbol)
    (ambient : WrapperState N) (externalInput externalOutput : List Symbol) :
    TM2.stepAux (liftCoreStmt (X := X) stmt)
        (WrapperState.coreLens.put ambient core)
        (wrapperCoreStacks inner externalInput externalOutput) =
      liftCoreCfg (X := X) (TM2.stepAux stmt core inner)
        ambient externalInput externalOutput := by
  induction stmt generalizing core inner with
  | push k f q ih =>
      simp only [liftCoreStmt, TM2.stepAux, WrapperState.coreLens]
      simpa only [update_wrapperCoreStacks] using ih _ _
  | peek k f q ih =>
      simp only [liftCoreStmt, TM2.stepAux, WrapperState.coreLens]
      simpa only [wrapperCoreStacks] using ih _ _
  | pop k f q ih =>
      simp only [liftCoreStmt, TM2.stepAux, WrapperState.coreLens]
      simpa only [wrapperCoreStacks, update_wrapperCoreStacks] using ih _ _
  | load f q ih =>
      simp only [liftCoreStmt, TM2.stepAux, WrapperState.coreLens]
      exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [liftCoreStmt, TM2.stepAux, WrapperState.coreLens]
      cases h : f core <;> simp [h]
      · exact ih₂ _ _
      · exact ih₁ _ _
  | goto f =>
      simp [liftCoreStmt, TM2.stepAux, liftCoreCfg, WrapperState.coreLens]
  | halt =>
      simp [liftCoreStmt, TM2.stepAux, liftCoreCfg, WrapperState.coreLens]

def liftCoreProgram {N : Nat} {L X : Type}
    (coreProgram : L -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (adapterProgram : X -> TM2.Stmt WrapperAlphabet (Sum L X)
      (WrapperState N)) :
    Sum L X -> TM2.Stmt WrapperAlphabet (Sum L X) (WrapperState N)
  | .inl label => liftCoreStmt (coreProgram label)
  | .inr label => adapterProgram label

theorem step_liftCoreProgram {N : Nat} {L X : Type}
    (coreProgram : L -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (adapterProgram : X -> TM2.Stmt WrapperAlphabet (Sum L X)
      (WrapperState N))
    (c : TM2.Cfg (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (ambient : WrapperState N) (externalInput externalOutput : List Symbol) :
    TM2.step (liftCoreProgram coreProgram adapterProgram)
      (liftCoreCfg (X := X) c ambient externalInput externalOutput) =
    (TM2.step coreProgram c).map
      (fun d => liftCoreCfg (X := X) d ambient externalInput externalOutput) := by
  rcases c with ⟨label, core, inner⟩
  cases label with
  | none => rfl
  | some label =>
      simp only [liftCoreCfg, Option.map_some, TM2.step, liftCoreProgram]
      rw [stepAux_liftCoreStmt]
      rfl

theorem iterate_liftCoreProgram {N n : Nat} {L X : Type}
    (coreProgram : L -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (adapterProgram : X -> TM2.Stmt WrapperAlphabet (Sum L X)
      (WrapperState N))
    (c d : TM2.Cfg (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (ambient : WrapperState N) (externalInput externalOutput : List Symbol)
    (hrun : ((fun x => x.bind (TM2.step coreProgram))^[n]) (some c) = some d) :
    ((fun x => x.bind (TM2.step
      (liftCoreProgram coreProgram adapterProgram)))^[n])
      (some (liftCoreCfg (X := X) c ambient externalInput externalOutput)) =
    some (liftCoreCfg (X := X) d ambient externalInput externalOutput) := by
  induction n generalizing c with
  | zero =>
      simp only [Function.iterate_zero_apply, Option.some.injEq] at hrun ⊢
      subst d
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun ⊢
      simp only [Option.bind_some]
      rw [step_liftCoreProgram]
      cases hs : TM2.step coreProgram c with
      | none =>
          change ((fun x => x.bind (TM2.step coreProgram))^[n])
            (TM2.step coreProgram c) = some d at hrun
          rw [hs] at hrun
          rw [iterate_optionBind_none] at hrun
          contradiction
      | some c' =>
          simp only [hs, Option.map_some, Option.bind_some] at hrun ⊢
          exact ih c' hrun

end

end Lax20Proofs.RamToTM
