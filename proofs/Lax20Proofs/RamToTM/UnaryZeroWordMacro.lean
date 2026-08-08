import Lax20Proofs.RamToTM.UnaryCountIncrementMacro

namespace Lax20Proofs.RamToTM

open Turing TM2

inductive UnaryZeroStack | width | word | backup
  deriving DecidableEq, Fintype, Inhabited

inductive UnaryZeroLabel | copy | restore | done
  deriving DecidableEq, Fintype, Inhabited

def unaryZeroProgram : UnaryZeroLabel →
    TM2.Stmt (fun _ : UnaryZeroStack => SparseSymbol)
      UnaryZeroLabel SymbolMoveControl
  | .copy =>
      .pop .width (fun _ a => ⟨a⟩) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .restore)
        (.push .word (fun _ => .bit false) <|
          .push .backup (fun s => s.held.getD default) <|
          .load (fun _ => default) <| .goto fun _ => .copy)
  | .restore =>
      .pop .backup (fun _ a => ⟨a⟩) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .done)
        (.push .width (fun s => s.held.getD default) <|
          .load (fun _ => default) <| .goto fun _ => .restore)
  | .done => .halt

def unaryZeroStacks (width word backup : List SparseSymbol) :
    UnaryZeroStack → List SparseSymbol
  | .width => width
  | .word => word
  | .backup => backup

def unaryZeroCfg (label : UnaryZeroLabel)
    (width word backup : List SparseSymbol) :
    TM2.Cfg (fun _ : UnaryZeroStack => SparseSymbol)
      UnaryZeroLabel SymbolMoveControl :=
  ⟨some label, default, unaryZeroStacks width word backup⟩

theorem unaryZero_copy_from (width word backup : List SparseSymbol) :
    ((fun o => o.bind (TM2.step unaryZeroProgram))^[width.length + 1])
      (some (unaryZeroCfg .copy width word backup)) =
    some (unaryZeroCfg .restore []
      (List.replicate width.length (.bit false) ++ word)
      (width.reverse ++ backup)) := by
  induction width generalizing word backup with
  | nil => simp [unaryZeroProgram, unaryZeroCfg, unaryZeroStacks, TM2.step]
  | cons a width ih =>
      have hs : TM2.step unaryZeroProgram
          (unaryZeroCfg .copy (a :: width) word backup) =
          some (unaryZeroCfg .copy width (.bit false :: word)
            (a :: backup)) := by
        simp [unaryZeroProgram, unaryZeroCfg, unaryZeroStacks, TM2.step,
          Function.update]
        funext k
        cases k <;> rfl
      have hs' : ((fun o => o.bind (TM2.step unaryZeroProgram))^[1])
          (some (unaryZeroCfg .copy (a :: width) word backup)) =
          some (unaryZeroCfg .copy width (.bit false :: word)
            (a :: backup)) := by simpa using hs
      have h := chain_iterations _ hs'
        (ih (.bit false :: word) (a :: backup))
      rw [show List.replicate width.length (.bit false) ++
          .bit false :: word =
          List.replicate (width.length + 1) (.bit false) ++ word by
        simp [List.replicate_add, List.append_assoc]] at h
      rw [List.length_cons,
        show width.length + 1 + 1 = 1 + (width.length + 1) by omega]
      simpa [List.replicate_succ, List.reverse_cons,
        List.append_assoc] using h

theorem unaryZero_copy (width : List SparseSymbol) :
    ((fun o => o.bind (TM2.step unaryZeroProgram))^[width.length + 1])
      (some (unaryZeroCfg .copy width [] [])) =
    some (unaryZeroCfg .restore []
      (List.replicate width.length (.bit false)) width.reverse) := by
  simpa using unaryZero_copy_from width [] []

theorem unaryZero_restore_from (source target word : List SparseSymbol) :
    ((fun o => o.bind (TM2.step unaryZeroProgram))^[source.length + 1])
      (some (unaryZeroCfg .restore target word source)) =
    some (unaryZeroCfg .done (source.reverse ++ target) word []) := by
  induction source generalizing target with
  | nil => simp [unaryZeroProgram, unaryZeroCfg, unaryZeroStacks, TM2.step]
  | cons a source ih =>
      have hs : TM2.step unaryZeroProgram
          (unaryZeroCfg .restore target word (a :: source)) =
          some (unaryZeroCfg .restore (a :: target) word source) := by
        simp [unaryZeroProgram, unaryZeroCfg, unaryZeroStacks, TM2.step,
          Function.update]
        funext k
        cases k <;> rfl
      have hs' : ((fun o => o.bind (TM2.step unaryZeroProgram))^[1])
          (some (unaryZeroCfg .restore target word (a :: source))) =
          some (unaryZeroCfg .restore (a :: target) word source) := by
        simpa using hs
      have h := chain_iterations _ hs' (ih (a :: target))
      rw [List.length_cons,
        show source.length + 1 + 1 = 1 + (source.length + 1) by omega]
      simpa [List.reverse_cons, List.append_assoc] using h

theorem unaryZero_restore (width word : List SparseSymbol) :
    ((fun o => o.bind (TM2.step unaryZeroProgram))^[width.length + 1])
      (some (unaryZeroCfg .restore [] word width.reverse)) =
    some (unaryZeroCfg .done width word []) := by
  simpa using unaryZero_restore_from width.reverse [] word

theorem unaryZero_correct (w : Nat) :
    ((fun o => o.bind (TM2.step unaryZeroProgram))^[2 * w + 2])
      (some (unaryZeroCfg .copy (unaryMarkers w) [] [])) =
    some (unaryZeroCfg .done (unaryMarkers w)
      ((fixedBits w 0).map SparseSymbol.bit) []) := by
  have hc := unaryZero_copy (unaryMarkers w)
  have hr := unaryZero_restore (unaryMarkers w)
    (List.replicate w (.bit false))
  simp only [unaryMarkers, List.length_replicate] at hc hr
  have h := chain_iterations _ hc hr
  rw [show (w + 1) + (w + 1) = 2 * w + 2 by omega] at h
  simpa [unaryMarkers, fixedBits_zero] using h

end Lax20Proofs.RamToTM
