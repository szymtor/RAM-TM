import Lax20Proofs.RamToTM.BoundedLiteralWordMacro
import Lax20Proofs.RamToTM.InterpreterMacroState
import Lax20Proofs.RamToTM.WordCountdownMacro

namespace Lax20Proofs.RamToTM

structure FullInterpreterState (N : ℕ) where
  macros : InterpreterMacroState := default
  /-- Dispatcher control is kept outside the resettable arithmetic macro
  bundle, so instruction-local cleanup cannot overwrite the global control
  invariant. -/
  dispatch : DispatchControl := default
  literal : BoundedLiteralControl N := ⟨none, 0⟩
  lookupFound : Bool := false
  subtractForceZero : Bool := false
  countdown : CountdownControl := default
  deriving DecidableEq, Fintype, Inhabited

def FullInterpreterState.macroLens {N : ℕ} :
    StateLens InterpreterMacroState (FullInterpreterState N) where
  get := FullInterpreterState.macros
  put := fun s v => { s with macros := v }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def FullInterpreterState.literalLens {N : ℕ} :
    StateLens (BoundedLiteralControl N) (FullInterpreterState N) where
  get := FullInterpreterState.literal
  put := fun s v => { s with literal := v }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def FullInterpreterState.countdownLens {N : ℕ} :
    StateLens CountdownControl (FullInterpreterState N) where
  get := FullInterpreterState.countdown
  put := fun s v => { s with countdown := v }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def FullInterpreterState.lookupLens {N : ℕ} :
    StateLens LookupCellControl (FullInterpreterState N) :=
  InterpreterMacroState.lookupLens.comp FullInterpreterState.macroLens

def FullInterpreterState.dispatchLens {N : ℕ} :
    StateLens DispatchControl (FullInterpreterState N) where
  get := FullInterpreterState.dispatch
  put := fun s v => { s with dispatch := v }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def FullInterpreterState.zeroLens {N : ℕ} :
    StateLens ZeroWordControl (FullInterpreterState N) :=
  InterpreterMacroState.zeroLens.comp FullInterpreterState.macroLens

def FullInterpreterState.moveLens {N : ℕ} :
    StateLens SymbolMoveControl (FullInterpreterState N) :=
  InterpreterMacroState.moveLens.comp FullInterpreterState.macroLens

def FullInterpreterState.prependLens {N : ℕ} :
    StateLens PrependCellControl (FullInterpreterState N) :=
  InterpreterMacroState.prependLens.comp FullInterpreterState.macroLens

def FullInterpreterState.shiftLens {N : ℕ} :
    StateLens MoveControl (FullInterpreterState N) :=
  InterpreterMacroState.shiftLens.comp FullInterpreterState.macroLens

def FullInterpreterState.compareLens {N : ℕ} :
    StateLens CompareControl (FullInterpreterState N) :=
  InterpreterMacroState.compareLens.comp FullInterpreterState.macroLens

def FullInterpreterState.subLens {N : ℕ} :
    StateLens SubControl (FullInterpreterState N) :=
  InterpreterMacroState.subLens.comp FullInterpreterState.macroLens

def FullInterpreterState.divLens {N : ℕ} :
    StateLens DivControl (FullInterpreterState N) :=
  InterpreterMacroState.divLens.comp FullInterpreterState.macroLens

def coreIdentityRenaming : StackRenaming CoreStack CoreStack where
  encode := id
  decode := some
  decode_encode := by intro k; rfl
  encode_decode := by
    intro k' k h
    simpa using h.symm

@[simp] theorem renamedStacks_coreIdentity
    (inner ambient : CoreStack → List SparseSymbol) :
    renamedStacks coreIdentityRenaming inner ambient = inner := by
  funext k
  rfl

end Lax20Proofs.RamToTM
