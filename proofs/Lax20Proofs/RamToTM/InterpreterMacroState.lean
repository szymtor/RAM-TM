import Lax20Proofs.RamToTM.StateLensEmbedding

namespace Lax20Proofs.RamToTM

set_option maxRecDepth 10000
set_option maxSynthPendingDepth 10000

/-! The monolithic interpreter carries every fixed-size macro controller.
Each phase accesses only its field through a lawful lens. -/

structure InterpreterMacroStateA where
  dispatch : DispatchControl := default
  lookup : LookupCellControl := default
  add : AddControl := default
  zip : ZipControl := default
  deriving DecidableEq, Fintype, Inhabited

structure InterpreterMacroStateB where
  sub : SubControl := default
  mul : MulControl := default
  div : DivControl := default
  move : SymbolMoveControl := default
  deriving DecidableEq, Fintype, Inhabited

structure InterpreterMacroStateC where
  prepend : PrependCellControl := default
  shift : MoveControl := default
  compare : CompareControl := default
  zero : ZeroWordControl := default
  transfer : WordTransferControl := default
  deriving DecidableEq, Fintype, Inhabited

structure InterpreterMacroState where
  a : InterpreterMacroStateA := default
  b : InterpreterMacroStateB := default
  c : InterpreterMacroStateC := default
  deriving DecidableEq, Fintype, Inhabited

def InterpreterMacroState.dispatchLens :
    StateLens DispatchControl InterpreterMacroState where
  get := fun s => s.a.dispatch
  put := fun s v => { s with a := { s.a with dispatch := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.lookupLens :
    StateLens LookupCellControl InterpreterMacroState where
  get := fun s => s.a.lookup
  put := fun s v => { s with a := { s.a with lookup := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.addLens : StateLens AddControl InterpreterMacroState where
  get := fun s => s.a.add
  put := fun s v => { s with a := { s.a with add := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.zipLens : StateLens ZipControl InterpreterMacroState where
  get := fun s => s.a.zip
  put := fun s v => { s with a := { s.a with zip := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.subLens : StateLens SubControl InterpreterMacroState where
  get := fun s => s.b.sub
  put := fun s v => { s with b := { s.b with sub := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.mulLens : StateLens MulControl InterpreterMacroState where
  get := fun s => s.b.mul
  put := fun s v => { s with b := { s.b with mul := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.divLens : StateLens DivControl InterpreterMacroState where
  get := fun s => s.b.div
  put := fun s v => { s with b := { s.b with div := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.moveLens :
    StateLens SymbolMoveControl InterpreterMacroState where
  get := fun s => s.b.move
  put := fun s v => { s with b := { s.b with move := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.prependLens :
    StateLens PrependCellControl InterpreterMacroState where
  get := fun s => s.c.prepend
  put := fun s v => { s with c := { s.c with prepend := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.shiftLens : StateLens MoveControl InterpreterMacroState where
  get := fun s => s.c.shift
  put := fun s v => { s with c := { s.c with shift := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.compareLens :
    StateLens CompareControl InterpreterMacroState where
  get := fun s => s.c.compare
  put := fun s v => { s with c := { s.c with compare := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.zeroLens :
    StateLens ZeroWordControl InterpreterMacroState where
  get := fun s => s.c.zero
  put := fun s v => { s with c := { s.c with zero := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.transferLens :
    StateLens WordTransferControl InterpreterMacroState where
  get := fun s => s.c.transfer
  put := fun s v => { s with c := { s.c with transfer := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

end Lax20Proofs.RamToTM
