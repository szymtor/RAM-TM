import Lax51Proofs.RamToTM.CanonicalPaddingMacro

namespace Lax51Proofs.RamToTM

open Turing TM2
open Lax51.BinaryWordEncoding Lax51.RamPolytime

inductive PhysicalRawStack | saved | raw | length | temp
  deriving DecidableEq, Fintype, Inhabited

inductive PhysicalRawLabel | reverseSaved | reverseLength | prependLength | finish | done
  deriving DecidableEq, Fintype, Inhabited

def physicalRawProgram : PhysicalRawLabel →
    TM2.Stmt (fun _ : PhysicalRawStack => SparseSymbol)
      PhysicalRawLabel SymbolMoveControl
  | .reverseSaved => symbolMoveIteration .saved .raw .reverseSaved .reverseLength
  | .reverseLength => symbolMoveIteration .length .temp .reverseLength .prependLength
  | .prependLength => symbolMoveIteration .temp .raw .prependLength .finish
  | .finish =>
      .push .raw (fun _ => .wordEnd) <|
      .goto fun _ => .done
  | .done => .halt

def physicalRawStacks (saved raw length temp : List SparseSymbol) :
    PhysicalRawStack → List SparseSymbol
  | .saved => saved
  | .raw => raw
  | .length => length
  | .temp => temp

def physicalRawCfg (label : PhysicalRawLabel)
    (saved raw length temp : List SparseSymbol) :
    TM2.Cfg (fun _ : PhysicalRawStack => SparseSymbol)
      PhysicalRawLabel SymbolMoveControl :=
  ⟨some label, default, physicalRawStacks saved raw length temp⟩

theorem physicalRaw_reverseSaved (saved raw length : List SparseSymbol) :
    ((fun o => o.bind (TM2.step physicalRawProgram))^[saved.length + 1])
      (some (physicalRawCfg .reverseSaved saved raw length [])) =
    some (physicalRawCfg .reverseLength [] (saved.reverse ++ raw) length []) := by
  induction saved generalizing raw with
  | nil =>
      simp [physicalRawProgram, physicalRawCfg, physicalRawStacks,
        symbolMoveIteration, TM2.step]
      decide
  | cons a saved ih =>
      have hs : TM2.step physicalRawProgram
          (physicalRawCfg .reverseSaved (a :: saved) raw length []) =
          some (physicalRawCfg .reverseSaved saved (a :: raw) length []) := by
        simp [physicalRawProgram, physicalRawCfg, physicalRawStacks,
          symbolMoveIteration, TM2.step, Function.update]
        funext k
        cases k <;> rfl
      have hs' : ((fun o => o.bind (TM2.step physicalRawProgram))^[1])
          (some (physicalRawCfg .reverseSaved (a :: saved) raw length [])) =
          some (physicalRawCfg .reverseSaved saved (a :: raw) length []) := by simpa using hs
      have h := chain_iterations _ hs' (ih (a :: raw))
      rw [List.length_cons,
        show saved.length + 1 + 1 = 1 + (saved.length + 1) by omega]
      simpa [List.reverse_cons, List.append_assoc] using h

theorem physicalRaw_reverseLength_from (raw length temp : List SparseSymbol) :
    ((fun o => o.bind (TM2.step physicalRawProgram))^[length.length + 1])
      (some (physicalRawCfg .reverseLength [] raw length temp)) =
    some (physicalRawCfg .prependLength [] raw [] (length.reverse ++ temp)) := by
  induction length generalizing temp with
  | nil =>
      simp [physicalRawProgram, physicalRawCfg, physicalRawStacks,
        symbolMoveIteration, TM2.step]
      decide
  | cons a length ih =>
      have hs : TM2.step physicalRawProgram
          (physicalRawCfg .reverseLength [] raw (a :: length) temp) =
          some (physicalRawCfg .reverseLength [] raw length (a :: temp)) := by
        simp [physicalRawProgram, physicalRawCfg, physicalRawStacks,
          symbolMoveIteration, TM2.step, Function.update]
        funext k
        cases k <;> rfl
      have hs' : ((fun o => o.bind (TM2.step physicalRawProgram))^[1])
          (some (physicalRawCfg .reverseLength [] raw (a :: length) temp)) =
          some (physicalRawCfg .reverseLength [] raw length (a :: temp)) := by simpa using hs
      have h := chain_iterations _ hs' (ih (a :: temp))
      rw [List.length_cons,
        show length.length + 1 + 1 = 1 + (length.length + 1) by omega]
      simpa [List.reverse_cons, List.append_assoc] using h

theorem physicalRaw_reverseLength (raw length : List SparseSymbol) :
    ((fun o => o.bind (TM2.step physicalRawProgram))^[length.length + 1])
      (some (physicalRawCfg .reverseLength [] raw length [])) =
    some (physicalRawCfg .prependLength [] raw [] length.reverse) := by
  simpa using physicalRaw_reverseLength_from raw length []

theorem physicalRaw_prependLength (raw temp : List SparseSymbol) :
    ((fun o => o.bind (TM2.step physicalRawProgram))^[temp.length + 1])
      (some (physicalRawCfg .prependLength [] raw [] temp)) =
    some (physicalRawCfg .finish [] (temp.reverse ++ raw) [] []) := by
  induction temp generalizing raw with
  | nil =>
      simp [physicalRawProgram, physicalRawCfg, physicalRawStacks,
        symbolMoveIteration, TM2.step]
      decide
  | cons a temp ih =>
      have hs : TM2.step physicalRawProgram
          (physicalRawCfg .prependLength [] raw [] (a :: temp)) =
          some (physicalRawCfg .prependLength [] (a :: raw) [] temp) := by
        simp [physicalRawProgram, physicalRawCfg, physicalRawStacks,
          symbolMoveIteration, TM2.step, Function.update]
        funext k
        cases k <;> rfl
      have hs' : ((fun o => o.bind (TM2.step physicalRawProgram))^[1])
          (some (physicalRawCfg .prependLength [] raw [] (a :: temp))) =
          some (physicalRawCfg .prependLength [] (a :: raw) [] temp) := by simpa using hs
      have h := chain_iterations _ hs' (ih (a :: raw))
      rw [List.length_cons,
        show temp.length + 1 + 1 = 1 + (temp.length + 1) by omega]
      simpa [List.reverse_cons, List.append_assoc] using h

theorem physicalRaw_finish (raw : List SparseSymbol) :
    TM2.step physicalRawProgram (physicalRawCfg .finish [] raw [] []) =
      some (physicalRawCfg .done [] (.wordEnd :: raw) [] []) := by
  simp [physicalRawProgram, physicalRawCfg, physicalRawStacks, TM2.step,
    Function.update]
  funext k
  cases k <;> rfl

theorem physicalRaw_correct (saved length : List SparseSymbol) :
    ((fun o => o.bind (TM2.step physicalRawProgram))^[
        saved.length + 2 * length.length + 4])
      (some (physicalRawCfg .reverseSaved saved [] length [])) =
    some (physicalRawCfg .done []
      (.wordEnd :: length ++ saved.reverse) [] []) := by
  have h₁ := physicalRaw_reverseSaved saved [] length
  rw [List.append_nil] at h₁
  have h₂ := physicalRaw_reverseLength saved.reverse length
  have h₃ := physicalRaw_prependLength saved.reverse length.reverse
  rw [List.reverse_reverse] at h₃
  have h₄ :
      ((fun o => o.bind (TM2.step physicalRawProgram))^[1])
        (some (physicalRawCfg .finish [] (length ++ saved.reverse) [] [])) =
      some (physicalRawCfg .done []
        (.wordEnd :: length ++ saved.reverse) [] []) := by
    simpa using physicalRaw_finish (length ++ saved.reverse)
  have h := chain_iterations _ (chain_iterations _
    (chain_iterations _ h₁ h₂) h₃) h₄
  rw [List.length_reverse] at h
  have hsteps :
      saved.length + 1 + (length.length + 1) + (length.length + 1) + 1 =
        saved.length + 2 * length.length + 4 := by omega
  rw [hsteps] at h
  exact h

theorem physicalRaw_input_correct (w : Nat) (x : List Nat) :
    ((fun o => o.bind (TM2.step physicalRawProgram))^[
        bitSize x + 2 * w + 4])
      (some (physicalRawCfg .reverseSaved
        ((encode x).reverse.map sparseOfInputSymbol) []
        ((fixedBits w x.length).map SparseSymbol.bit) [])) =
    some (physicalRawCfg .done [] (physicalPaddingRaw w x) [] []) := by
  simpa [physicalPaddingRaw, canonicalPaddingRaw_eq, bitSize,
    List.length_map, List.length_reverse, List.map_reverse] using
    physicalRaw_correct ((encode x).reverse.map sparseOfInputSymbol)
      ((fixedBits w x.length).map SparseSymbol.bit)

end Lax51Proofs.RamToTM
