import Lax51Proofs.RamToTM.InputPreprocessorEmbedding

namespace Lax51Proofs.RamToTM

open Turing TM2

inductive CoreInitLabel | zeroCopy | zeroRestore | clearMultiplier | clearWidth | finish | done
  deriving DecidableEq, Fintype, Inhabited

def coreInitProgram {N : Nat} : CoreInitLabel →
    TM2.Stmt WrapperAlphabet CoreInitLabel (WrapperState N)
  | .zeroCopy =>
      .pop (.core .work3) (fun s a => {s with heldSparse := a}) <|
      .branch (fun s => s.heldSparse.isNone)
        (.load (fun s => {s with heldSparse := none}) <|
          .goto fun _ => .zeroRestore)
        (.push (.core .accumulator) (fun _ => .bit false) <|
          .push (.core .work7) (fun s => s.heldSparse.getD default) <|
          .load (fun s => {s with heldSparse := none}) <|
          .goto fun _ => .zeroCopy)
  | .zeroRestore =>
      .pop (.core .work7) (fun s a => {s with heldSparse := a}) <|
      .branch (fun s => s.heldSparse.isNone)
        (.load (fun s => {s with heldSparse := none}) <|
          .goto fun _ => .clearMultiplier)
        (.push (.core .work3) (fun s => s.heldSparse.getD default) <|
          .load (fun s => {s with heldSparse := none}) <|
          .goto fun _ => .zeroRestore)
  | .clearMultiplier =>
      .pop (.core .work1) (fun s a => {s with heldSparse := a}) <|
      .branch (fun s => s.heldSparse.isNone)
        (.load (fun s => {s with heldSparse := none}) <|
          .goto fun _ => .clearWidth)
        (.load (fun s => {s with heldSparse := none}) <|
          .goto fun _ => .clearMultiplier)
  | .clearWidth =>
      .pop (.core .work3) (fun s a => {s with heldSparse := a}) <|
      .branch (fun s => s.heldSparse.isNone)
        (.load (fun s => {s with heldSparse := none}) <|
          .goto fun _ => .finish)
        (.load (fun s => {s with heldSparse := none}) <|
          .goto fun _ => .clearWidth)
  | .finish =>
      .push (.core .memory) (fun _ => .memoryEnd) <|
      .push (.core .output) (fun _ => .outputEnd) <|
      .load (fun _ => default) <|
      .goto fun _ => .done
  | .done => .halt

def coreInitCfg {N : Nat} (label : CoreInitLabel) (state : WrapperState N)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    TM2.Cfg WrapperAlphabet CoreInitLabel (WrapperState N) :=
  ⟨some label, state, tapes⟩

theorem coreInit_zero_copy_from {N : Nat} (markers acc backup : List SparseSymbol)
    (state : WrapperState N)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    ((fun o => o.bind (TM2.step coreInitProgram))^[markers.length + 1])
      (some (coreInitCfg .zeroCopy state
        (Function.update
          (Function.update
            (Function.update tapes (.core .work3) markers)
            (.core .accumulator) acc)
          (.core .work7) backup))) =
    some (coreInitCfg .zeroRestore {state with heldSparse := none}
      (Function.update
        (Function.update
          (Function.update tapes (.core .work3) [])
          (.core .accumulator)
            (List.replicate markers.length (.bit false) ++ acc))
        (.core .work7) (markers.reverse ++ backup))) := by
  induction markers generalizing state acc backup with
  | nil =>
      simp [coreInitProgram, coreInitCfg, TM2.step, List.head?, List.tail,
        Option.isNone, Function.update]
      funext k
      cases k with
      | input | output => rfl
      | core k => cases k <;> rfl
  | cons marker markers ih =>
      have hs : TM2.step coreInitProgram
          (coreInitCfg .zeroCopy state
            (Function.update
              (Function.update
                (Function.update tapes (.core .work3) (marker :: markers))
                (.core .accumulator) acc)
              (.core .work7) backup)) =
          some (coreInitCfg .zeroCopy {state with heldSparse := none}
            (Function.update
              (Function.update
                (Function.update tapes (.core .work3) markers)
                (.core .accumulator) (.bit false :: acc))
              (.core .work7) (marker :: backup))) := by
        simp [coreInitProgram, coreInitCfg, TM2.step, Option.isNone,
          Option.getD, Function.update]
        funext k
        cases k with
        | input | output => rfl
        | core k => cases k <;> simp [Function.update]
      have hs' : ((fun o => o.bind (TM2.step coreInitProgram))^[1])
          (some (coreInitCfg .zeroCopy state
            (Function.update
              (Function.update
                (Function.update tapes (.core .work3) (marker :: markers))
                (.core .accumulator) acc)
              (.core .work7) backup))) =
          some (coreInitCfg .zeroCopy {state with heldSparse := none}
            (Function.update
              (Function.update
                (Function.update tapes (.core .work3) markers)
                (.core .accumulator) (.bit false :: acc))
              (.core .work7) (marker :: backup))) := by simpa using hs
      have hi := ih (.bit false :: acc) (marker :: backup)
        {state with heldSparse := none}
      have h := chain_iterations _ hs' hi
      rw [show 1 + (markers.length + 1) = markers.length + 1 + 1 by omega] at h
      have hout :
          coreInitCfg .zeroRestore {state with heldSparse := none}
            (Function.update
              (Function.update
                (Function.update tapes (.core .work3) [])
                (.core .accumulator)
                  (List.replicate markers.length (.bit false) ++
                    .bit false :: acc))
              (.core .work7) (markers.reverse ++ marker :: backup)) =
          coreInitCfg .zeroRestore {state with heldSparse := none}
            (Function.update
              (Function.update
                (Function.update tapes (.core .work3) [])
              (.core .accumulator)
                  (List.replicate (marker :: markers).length (.bit false) ++ acc))
              (.core .work7) ((marker :: markers).reverse ++ backup)) := by
        have hrep :
            List.replicate markers.length (.bit false) ++ .bit false :: acc =
              List.replicate (marker :: markers).length (.bit false) ++ acc := by
          change List.replicate markers.length (.bit false) ++
              ([.bit false] ++ acc) =
            List.replicate (markers.length + 1) (.bit false) ++ acc
          calc
            _ = (List.replicate markers.length (.bit false) ++
                [.bit false]) ++ acc := (List.append_assoc _ _ _).symm
            _ = _ := by
              rw [show [SparseSymbol.bit false] =
                List.replicate 1 (SparseSymbol.bit false) by rfl,
                List.replicate_append_replicate]
        apply congrArg (fun updated =>
          coreInitCfg .zeroRestore {state with heldSparse := none} updated)
        funext k
        cases k with
        | input | output => rfl
        | core k =>
            cases k <;>
              simp [List.reverse_cons, List.append_assoc, Function.update]
            case accumulator => simpa only [List.length_cons] using hrep
      rw [hout] at h
      exact h

theorem coreInit_zero_copy {N w : Nat} (state : WrapperState N)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k))
    (hacc : tapes (.core .accumulator) = [])
    (hbackup : tapes (.core .work7) = []) :
    ((fun o => o.bind (TM2.step coreInitProgram))^[w + 1])
      (some (coreInitCfg .zeroCopy state
        (Function.update tapes (.core .work3) (unaryMarkers w)))) =
    some (coreInitCfg .zeroRestore {state with heldSparse := none}
      (Function.update
        (Function.update
          (Function.update tapes (.core .work3) [])
          (.core .accumulator) ((fixedBits w 0).map SparseSymbol.bit).reverse)
        (.core .work7) (unaryMarkers w).reverse)) := by
  have h := coreInit_zero_copy_from (N := N) (unaryMarkers w) [] [] state tapes
  rw [show (unaryMarkers w).length = w by simp [unaryMarkers]] at h
  have hstart :
      coreInitCfg .zeroCopy state
          (Function.update
            (Function.update
              (Function.update tapes (.core .work3) (unaryMarkers w))
              (.core .accumulator) [])
            (.core .work7) []) =
        coreInitCfg .zeroCopy state
          (Function.update tapes (.core .work3) (unaryMarkers w)) := by
    apply congrArg (fun updated => coreInitCfg .zeroCopy state updated)
    funext k
    cases k with
    | input | output => rfl
    | core k => cases k <;> simp [hacc, hbackup, Function.update]
  have hfinal :
      coreInitCfg .zeroRestore {state with heldSparse := none}
          (Function.update
            (Function.update
              (Function.update tapes (.core .work3) [])
              (.core .accumulator)
                (List.replicate w (.bit false) ++ []))
            (.core .work7) ((unaryMarkers w).reverse ++ [])) =
        coreInitCfg .zeroRestore {state with heldSparse := none}
          (Function.update
            (Function.update
              (Function.update tapes (.core .work3) [])
              (.core .accumulator)
                ((fixedBits w 0).map SparseSymbol.bit).reverse)
            (.core .work7) (unaryMarkers w).reverse) := by
    apply congrArg (fun updated =>
      coreInitCfg .zeroRestore {state with heldSparse := none} updated)
    funext k
    cases k with
    | input | output => rfl
    | core k =>
        cases k <;>
          simp [fixedBits_zero, List.reverse_replicate, Function.update]
        case accumulator => rfl
        case work7 => exact List.append_nil _
  have hin := congrArg
    (fun cfg => ((fun o => o.bind (TM2.step coreInitProgram))^[w + 1]) cfg)
    (congrArg some hstart).symm
  exact hin.trans (h.trans (congrArg some hfinal))

theorem coreInit_zero_restore_from {N : Nat}
    (saved width : List SparseSymbol) (state : WrapperState N)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    ((fun o => o.bind (TM2.step coreInitProgram))^[saved.length + 1])
      (some (coreInitCfg .zeroRestore state
        (Function.update
          (Function.update tapes (.core .work3) width)
          (.core .work7) saved))) =
    some (coreInitCfg .clearMultiplier {state with heldSparse := none}
      (Function.update
        (Function.update tapes (.core .work3) (saved.reverse ++ width))
        (.core .work7) [])) := by
  induction saved generalizing state width with
  | nil =>
      simp [coreInitProgram, coreInitCfg, TM2.step, List.head?, List.tail,
        Option.isNone, Function.update]
  | cons marker saved ih =>
      have hs : TM2.step coreInitProgram
          (coreInitCfg .zeroRestore state
            (Function.update
              (Function.update tapes (.core .work3) width)
              (.core .work7) (marker :: saved))) =
          some (coreInitCfg .zeroRestore {state with heldSparse := none}
            (Function.update
              (Function.update tapes (.core .work3) (marker :: width))
              (.core .work7) saved)) := by
        simp [coreInitProgram, coreInitCfg, TM2.step, Option.isNone,
          Option.getD, Function.update]
        funext k
        cases k with
        | input | output => rfl
        | core k => cases k <;> simp [Function.update]
      have hs' : ((fun o => o.bind (TM2.step coreInitProgram))^[1])
          (some (coreInitCfg .zeroRestore state
            (Function.update
              (Function.update tapes (.core .work3) width)
              (.core .work7) (marker :: saved)))) =
          some (coreInitCfg .zeroRestore {state with heldSparse := none}
            (Function.update
              (Function.update tapes (.core .work3) (marker :: width))
              (.core .work7) saved)) := by simpa using hs
      have hi := ih (marker :: width) {state with heldSparse := none}
      have h := chain_iterations _ hs' hi
      rw [show 1 + (saved.length + 1) = saved.length + 1 + 1 by omega] at h
      simpa [List.reverse_cons, List.append_assoc] using h

theorem coreInit_zero_restore {N w : Nat} (state : WrapperState N)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    ((fun o => o.bind (TM2.step coreInitProgram))^[w + 1])
      (some (coreInitCfg .zeroRestore state
        (Function.update
          (Function.update tapes (.core .work3) [])
          (.core .work7) (unaryMarkers w).reverse))) =
    some (coreInitCfg .clearMultiplier {state with heldSparse := none}
      (Function.update
        (Function.update tapes (.core .work3) (unaryMarkers w))
        (.core .work7) [])) := by
  have h := coreInit_zero_restore_from (N := N)
    (unaryMarkers w).reverse [] state tapes
  rw [show (unaryMarkers w).reverse.length = w by simp [unaryMarkers]] at h
  simpa using h

theorem coreInit_clearMultiplier {N : Nat} (state : WrapperState N)
    (xs : List SparseSymbol)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    ((fun o => o.bind (TM2.step coreInitProgram))^[xs.length + 1])
      (some (coreInitCfg .clearMultiplier state
        (Function.update tapes (.core .work1) xs))) =
    some (coreInitCfg .clearWidth {state with heldSparse := none}
      (Function.update tapes (.core .work1) [])) := by
  induction xs generalizing state with
  | nil =>
      simp [coreInitProgram, coreInitCfg, TM2.step, List.head?, List.tail,
        Option.isNone, Function.update]
  | cons x xs ih =>
      have hs : TM2.step coreInitProgram
          (coreInitCfg .clearMultiplier state
            (Function.update tapes (.core .work1) (x :: xs))) =
          some (coreInitCfg .clearMultiplier {state with heldSparse := none}
            (Function.update tapes (.core .work1) xs)) := by
        simp [coreInitProgram, coreInitCfg, TM2.step, Option.isNone,
          Function.update]
      have hs' : ((fun o => o.bind (TM2.step coreInitProgram))^[1])
          (some (coreInitCfg .clearMultiplier state
            (Function.update tapes (.core .work1) (x :: xs)))) =
          some (coreInitCfg .clearMultiplier {state with heldSparse := none}
            (Function.update tapes (.core .work1) xs)) := by simpa using hs
      have h := chain_iterations _ hs' (ih {state with heldSparse := none})
      rw [show 1 + (xs.length + 1) = xs.length + 1 + 1 by omega] at h
      exact h

theorem coreInit_clearWidth {N w : Nat} (state : WrapperState N)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    ((fun o => o.bind (TM2.step coreInitProgram))^[w + 1])
      (some (coreInitCfg .clearWidth state
        (Function.update tapes (.core .work3) (unaryMarkers w)))) =
    some (coreInitCfg .finish {state with heldSparse := none}
      (Function.update tapes (.core .work3) [])) := by
  induction w generalizing state with
  | zero =>
      simp [unaryMarkers, coreInitProgram, coreInitCfg, TM2.step, List.head?,
        List.tail, Option.isNone, Function.update]
  | succ w ih =>
      have hs : TM2.step coreInitProgram
          (coreInitCfg .clearWidth state
            (Function.update tapes (.core .work3) (unaryMarkers (w + 1)))) =
          some (coreInitCfg .clearWidth {state with heldSparse := none}
            (Function.update tapes (.core .work3) (unaryMarkers w))) := by
        simp [unaryMarkers, List.replicate_succ, coreInitProgram, coreInitCfg,
          TM2.step, List.head?, List.tail, Option.isNone, Function.update]
      have hs' : ((fun o => o.bind (TM2.step coreInitProgram))^[1])
          (some (coreInitCfg .clearWidth state
            (Function.update tapes (.core .work3) (unaryMarkers (w + 1))))) =
          some (coreInitCfg .clearWidth {state with heldSparse := none}
            (Function.update tapes (.core .work3) (unaryMarkers w))) := by
        simpa using hs
      have h := chain_iterations _ hs' (ih {state with heldSparse := none})
      rw [show 1 + (w + 1) = w + 1 + 1 by omega] at h
      exact h

theorem coreInit_finish {N : Nat} (state : WrapperState N)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    TM2.step coreInitProgram (coreInitCfg .finish state tapes) =
    some (coreInitCfg .done default
      (Function.update
        (Function.update tapes (.core .memory)
          (.memoryEnd :: tapes (.core .memory)))
        (.core .output) (.outputEnd :: tapes (.core .output)))) := by
  simp [coreInitProgram, coreInitCfg, TM2.step]

def coreInitFinalStacks (w : Nat)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    (k : WrapperStack) → List (WrapperAlphabet k) :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update tapes (.core .accumulator)
              ((fixedBits w 0).map SparseSymbol.bit))
            (.core .work1) [])
          (.core .work3) [])
        (.core .work7) [])
      (.core .memory) [.memoryEnd])
    (.core .output) [.outputEnd]

theorem coreInit_correct {N w : Nat} (state : WrapperState N)
    (multiplier : List SparseSymbol)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k))
    (hacc : tapes (.core .accumulator) = [])
    (hbackup : tapes (.core .work7) = [])
    (hmemory : tapes (.core .memory) = [])
    (houtput : tapes (.core .output) = []) :
    ((fun o => o.bind (TM2.step coreInitProgram))^[
        3 * w + multiplier.length + 5])
      (some (coreInitCfg .zeroCopy state
        (Function.update
          (Function.update tapes (.core .work1) multiplier)
          (.core .work3) (unaryMarkers w)))) =
    some (coreInitCfg .done default (coreInitFinalStacks w tapes)) := by
  let startStacks := Function.update tapes (.core .work1) multiplier
  have hcopy := coreInit_zero_copy (N := N) (w := w) state startStacks
    (by simp [startStacks, hacc]) (by simp [startStacks, hbackup])
  have hrestore := coreInit_zero_restore (N := N) (w := w)
    {state with heldSparse := none}
    (Function.update startStacks (.core .accumulator)
      ((fixedBits w 0).map SparseSymbol.bit).reverse)
  have hclear1 := coreInit_clearMultiplier (N := N)
    {state with heldSparse := none} multiplier
    (Function.update
      (Function.update startStacks (.core .accumulator)
        ((fixedBits w 0).map SparseSymbol.bit).reverse)
      (.core .work3) (unaryMarkers w))
  have hclear3 := coreInit_clearWidth (N := N) (w := w)
    {state with heldSparse := none}
    (Function.update
      (Function.update
        (Function.update startStacks (.core .accumulator)
          ((fixedBits w 0).map SparseSymbol.bit).reverse)
        (.core .work1) [])
      (.core .work7) [])
  have hfinish := coreInit_finish (N := N)
    {state with heldSparse := none}
    (Function.update
      (Function.update
        (Function.update
          (Function.update startStacks (.core .accumulator)
            ((fixedBits w 0).map SparseSymbol.bit).reverse)
          (.core .work1) [])
        (.core .work7) [])
      (.core .work3) [])
  have htapes₁ :
      Function.update
          (Function.update
            (Function.update startStacks (.core .work3) [])
            (.core .accumulator) ((fixedBits w 0).map SparseSymbol.bit).reverse)
          (.core .work7) (unaryMarkers w).reverse =
        Function.update
          (Function.update
            (Function.update startStacks (.core .accumulator)
              ((fixedBits w 0).map SparseSymbol.bit).reverse)
            (.core .work3) [])
          (.core .work7) (unaryMarkers w).reverse := by
    funext k
    cases k with
    | input | output => rfl
    | core k => cases k <;> simp [Function.update]
  rw [← htapes₁] at hrestore
  have htapes₂ :
      Function.update
          (Function.update
            (Function.update startStacks (.core .accumulator)
              ((fixedBits w 0).map SparseSymbol.bit).reverse)
            (.core .work3) (unaryMarkers w))
          (.core .work7) [] =
        Function.update
          (Function.update
            (Function.update startStacks (.core .accumulator)
              ((fixedBits w 0).map SparseSymbol.bit).reverse)
            (.core .work3) (unaryMarkers w))
          (.core .work1) multiplier := by
    funext k
    cases k with
    | input | output => rfl
    | core k => cases k <;> simp [startStacks, hbackup, Function.update]
  rw [← htapes₂] at hclear1
  have htapes₃ :
      Function.update
          (Function.update
            (Function.update startStacks (.core .accumulator)
              ((fixedBits w 0).map SparseSymbol.bit).reverse)
            (.core .work3) (unaryMarkers w))
          (.core .work1) [] =
        Function.update
          (Function.update
            (Function.update
              (Function.update startStacks (.core .accumulator)
                ((fixedBits w 0).map SparseSymbol.bit).reverse)
              (.core .work1) [])
            (.core .work7) [])
          (.core .work3) (unaryMarkers w) := by
    funext k
    cases k with
    | input | output => rfl
    | core k => cases k <;> simp [startStacks, hbackup, Function.update]
  rw [← htapes₃] at hclear3
  have hfinish' :
      ((fun o => o.bind (TM2.step coreInitProgram))^[1])
        (some (coreInitCfg .finish {state with heldSparse := none}
          (Function.update
            (Function.update
              (Function.update
                (Function.update startStacks (.core .accumulator)
                  ((fixedBits w 0).map SparseSymbol.bit).reverse)
                (.core .work1) [])
              (.core .work7) [])
            (.core .work3) []))) =
      some (coreInitCfg .done default
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update startStacks (.core .accumulator)
                    ((fixedBits w 0).map SparseSymbol.bit).reverse)
                  (.core .work1) [])
                (.core .work7) [])
              (.core .work3) [])
            (.core .memory) (.memoryEnd ::
              (Function.update
                (Function.update
                  (Function.update
                    (Function.update startStacks (.core .accumulator)
                      ((fixedBits w 0).map SparseSymbol.bit).reverse)
                    (.core .work1) [])
                  (.core .work7) [])
                (.core .work3) []) (.core .memory)))
          (.core .output) (.outputEnd ::
            (Function.update
              (Function.update
                (Function.update
                  (Function.update startStacks (.core .accumulator)
                    ((fixedBits w 0).map SparseSymbol.bit).reverse)
                  (.core .work1) [])
                (.core .work7) [])
              (.core .work3) []) (.core .output)))) := by
    simpa using hfinish
  have h := chain_iterations _ (chain_iterations _ (chain_iterations _
    (chain_iterations _ hcopy hrestore) hclear1) hclear3) hfinish'
  simp [startStacks, coreInitFinalStacks, fixedBits_zero,
    List.reverse_replicate, hmemory, houtput, Nat.add_assoc] at h
  have hsteps :
      w + (1 + (w + (1 + (multiplier.length + (1 + (w + 2)))))) =
        3 * w + multiplier.length + 5 := by omega
  rw [hsteps] at h
  have htapesFinal :
      Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update
                    (Function.update tapes (.core .work1) multiplier)
                    (.core .accumulator)
                      (List.replicate w (.bit false)))
                  (.core .work1) [])
                (.core .work7) [])
              (.core .work3) [])
            (.core .memory) [.memoryEnd])
          (.core .output) [.outputEnd] =
        coreInitFinalStacks w tapes := by
    funext k
    cases k with
    | input | output => rfl
    | core k => cases k <;>
        simp [coreInitFinalStacks, fixedBits_zero, List.reverse_replicate,
          hacc, hbackup, hmemory, houtput, Function.update]
  exact h.trans (congrArg some
    (congrArg (fun updated => coreInitCfg .done default updated) htapesFinal))

end Lax51Proofs.RamToTM
