import Lax20Proofs.RamToTM.PhysicalRawAssembly

namespace Lax20Proofs.RamToTM

open Turing TM2

inductive FinalizeInputStack | source | input
  deriving DecidableEq, Fintype, Inhabited

inductive FinalizeInputLabel | mark | move | done
  deriving DecidableEq, Fintype, Inhabited

def finalizeInputProgram : FinalizeInputLabel →
    TM2.Stmt (fun _ : FinalizeInputStack => SparseSymbol)
      FinalizeInputLabel SymbolMoveControl
  | .mark =>
      .push .source (fun _ => .inputEnd) <|
      .goto fun _ => .move
  | .move => symbolMoveIteration .source .input .move .done
  | .done => .halt

def finalizeInputStacks (source input : List SparseSymbol) :
    FinalizeInputStack → List SparseSymbol
  | .source => source
  | .input => input

def finalizeInputCfg (label : FinalizeInputLabel)
    (source input : List SparseSymbol) :
    TM2.Cfg (fun _ : FinalizeInputStack => SparseSymbol)
      FinalizeInputLabel SymbolMoveControl :=
  ⟨some label, default, finalizeInputStacks source input⟩

theorem finalizeInput_move (source input : List SparseSymbol) :
    ((fun o => o.bind (TM2.step finalizeInputProgram))^[source.length + 1])
      (some (finalizeInputCfg .move source input)) =
    some (finalizeInputCfg .done [] (source.reverse ++ input)) := by
  induction source generalizing input with
  | nil =>
      simp [finalizeInputProgram, finalizeInputCfg, finalizeInputStacks,
        symbolMoveIteration, TM2.step]
      decide
  | cons a source ih =>
      have hs : TM2.step finalizeInputProgram
          (finalizeInputCfg .move (a :: source) input) =
          some (finalizeInputCfg .move source (a :: input)) := by
        simp [finalizeInputProgram, finalizeInputCfg, finalizeInputStacks,
          symbolMoveIteration, TM2.step, Function.update]
        funext k
        cases k <;> rfl
      have hs' : ((fun o => o.bind (TM2.step finalizeInputProgram))^[1])
          (some (finalizeInputCfg .move (a :: source) input)) =
          some (finalizeInputCfg .move source (a :: input)) := by simpa using hs
      have h := chain_iterations _ hs' (ih (a :: input))
      rw [List.length_cons,
        show source.length + 1 + 1 = 1 + (source.length + 1) by omega]
      simpa [List.reverse_cons, List.append_assoc] using h

theorem finalizeInput_correct (payload : List SparseSymbol) :
    ((fun o => o.bind (TM2.step finalizeInputProgram))^[payload.length + 3])
      (some (finalizeInputCfg .mark payload [])) =
    some (finalizeInputCfg .done [] (payload.reverse ++ [.inputEnd])) := by
  have hmark :
      TM2.step finalizeInputProgram (finalizeInputCfg .mark payload []) =
        some (finalizeInputCfg .move (.inputEnd :: payload) []) := by
    simp [finalizeInputProgram, finalizeInputCfg, finalizeInputStacks, TM2.step]
    funext k
    cases k <;> rfl
  have hmark' : ((fun o => o.bind (TM2.step finalizeInputProgram))^[1])
      (some (finalizeInputCfg .mark payload [])) =
      some (finalizeInputCfg .move (.inputEnd :: payload) []) := by
    simpa using hmark
  have hmove := finalizeInput_move (.inputEnd :: payload) []
  have h := chain_iterations _ hmark' hmove
  have hsteps : 1 + ((.inputEnd :: payload).length + 1) =
      payload.length + 3 := by simp; omega
  rw [hsteps] at h
  simpa [List.reverse_cons, List.append_assoc] using h

theorem finalizeInput_encoded (w : Nat) (xs : List Nat) :
    ((fun o => o.bind (TM2.step finalizeInputProgram))^[
        (encodeWordList w xs).length + 3])
      (some (finalizeInputCfg .mark (encodeWordList w xs).reverse [])) =
    some (finalizeInputCfg .done [] (encodeInputStack w xs)) := by
  simpa [encodeInputStack] using finalizeInput_correct (encodeWordList w xs).reverse

end Lax20Proofs.RamToTM
