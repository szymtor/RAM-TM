import Lax51Proofs.RamToTM.FullPrependMacro

namespace Lax51Proofs.RamToTM

open Turing TM2

inductive StorePrependResetLabel
  | reset
  deriving DecidableEq, Fintype, Inhabited

abbrev StorePrependTailLabel (R : Type) :=
  Sum StorePrependResetLabel (FullPrependLabel R)

abbrev FullStoreLabel (R : Type) :=
  FullCopyLabel (StorePrependTailLabel R)

def storePrependResetProgram {N : Nat} {R : Type} :
    StorePrependResetLabel -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (StorePrependTailLabel R)
      (FullInterpreterState N)
  | .reset =>
      .load (fun s => FullInterpreterState.prependLens.put s default) <|
      .goto fun _ => Sum.inr (Sum.inl PrependCellLabel.cellEnd)

def storePrependTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    StorePrependTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (StorePrependTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram storePrependResetProgram
    (fullPrependProgram returnLabel right)

def fullStoreProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullStoreLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullStoreLabel R)
      (FullInterpreterState N) :=
  fullCopyProgram (Sum.inl StorePrependResetLabel.reset)
    (storePrependTailProgram returnLabel right)

def storePreparedStacks (w address accumulator : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) : CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .work0 => (fixedBits w address).reverse.map SparseSymbol.bit
  | .work1 => (fixedBits w accumulator).reverse.map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .input => base .input
  | .output => base .output
  | _ => []

theorem copyAccumulatorStacks_operandResult (w address accumulator : Nat)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    copyAccumulatorStacks
      ((fixedBits w accumulator).map SparseSymbol.bit)
      (operandResultBase w accumulator address m base) =
    storePreparedStacks w address accumulator m base := by
  funext k
  cases k <;> simp [copyAccumulatorStacks, operandResultBase,
    storePreparedStacks, List.map_reverse]

theorem prependResultStacks_storePrepared (w address accumulator : Nat)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    prependResultStacks w address accumulator m
      (storePreparedStacks w address accumulator m base) =
    operandBoundaryBase w accumulator (m.write w address accumulator) base := by
  funext k
  cases k <;> rfl

theorem storePrependReset_step {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w address accumulator : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    TM2.step (storePrependTailProgram returnLabel right)
      (cleanReturnCfg (Sum.inl StorePrependResetLabel.reset) state
        (storePreparedStacks w address accumulator m base)) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg prependCoreRenaming FullInterpreterState.prependLens
        (prependLocalCfg .cellEnd
          ((fixedBits w address).reverse.map SparseSymbol.bit)
          ((fixedBits w accumulator).reverse.map SparseSymbol.bit)
          (encodeSparseMemory w m ++ [.memoryEnd])) state
        (storePreparedStacks w address accumulator m base))) := by
  simp [storePrependTailProgram, storePrependResetProgram, cleanReturnCfg,
    liftRightProgram, mapLabelCfg, TM2.step, lensRenamedCfg,
    prependLocalCfg]
  have hs : renamedStacks prependCoreRenaming
      (prependCellStacks
        ((fixedBits w address).reverse.map SparseSymbol.bit)
        ((fixedBits w accumulator).reverse.map SparseSymbol.bit)
        (encodeSparseMemory w m ++ [.memoryEnd]))
      (storePreparedStacks w address accumulator m base) =
      storePreparedStacks w address accumulator m base := by
    funext k
    cases k <;> simp [renamedStacks, prependCoreRenaming,
      prependCoreDecode, prependCellStacks, storePreparedStacks]
  rw [← List.map_reverse, ← List.map_reverse]
  exact hs.symm

theorem fullStore_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w address accumulator : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ finalState,
      ((fun o => o.bind (TM2.step (fullStoreProgram returnLabel right)))^[
        4 * w + 10])
        (some (lensRenamedCfg
          (copyCoreRenaming .accumulator .work1 .work7
            (by decide) (by decide) (by decide))
          FullInterpreterState.moveLens
          (copyCfg .scan ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
          state (operandResultBase w accumulator address m base))) =
      some (mapLabelCfg (fun l : StorePrependTailLabel R => Sum.inr l)
        (mapLabelCfg (fun l : FullPrependLabel R => Sum.inr l)
          (mapLabelCfg (fun l : R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w accumulator
                (m.write w address accumulator) base))))) := by
  have hcopy := fullCopyAccumulator_generic_correct
    (Sum.inl StorePrependResetLabel.reset)
    (storePrependTailProgram returnLabel right)
    ((fixedBits w accumulator).map SparseSymbol.bit)
    (operandResultBase w accumulator address m base) state
  simp only [List.length_map, fixedBits_length] at hcopy
  rw [copyAccumulatorStacks_operandResult w address accumulator m base] at hcopy
  let copyState := FullInterpreterState.moveLens.put state default
  have hresetStep := storePrependReset_step returnLabel right
    w address accumulator m base copyState
  have hreset :
      ((fun o => o.bind (TM2.step
        (storePrependTailProgram returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl StorePrependResetLabel.reset)
          copyState (storePreparedStacks w address accumulator m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg prependCoreRenaming FullInterpreterState.prependLens
          (prependLocalCfg .cellEnd
            ((fixedBits w address).reverse.map SparseSymbol.bit)
            ((fixedBits w accumulator).reverse.map SparseSymbol.bit)
            (encodeSparseMemory w m ++ [.memoryEnd])) copyState
          (storePreparedStacks w address accumulator m base))) := by
    simpa using hresetStep
  have hprepend := fullPrepend_fixed_correct returnLabel right
    w address accumulator m
    (storePreparedStacks w address accumulator m base) copyState
  rw [prependResultStacks_storePrepared w address accumulator m base] at hprepend
  dsimp only at hprepend
  have hstacks :
      (fun
        | .work0 => (fixedBits w address).reverse.map SparseSymbol.bit
        | .work1 => (fixedBits w accumulator).reverse.map SparseSymbol.bit
        | .memory => encodeSparseMemory w m ++ [.memoryEnd]
        | k => storePreparedStacks w address accumulator m base k) =
      storePreparedStacks w address accumulator m base := by
    funext k
    cases k <;> rfl
  have hcfg :
      lensRenamedCfg (Λx := R) prependCoreRenaming FullInterpreterState.prependLens
        (prependLocalCfg .cellEnd
          ((fixedBits w address).reverse.map SparseSymbol.bit)
          ((fixedBits w accumulator).reverse.map SparseSymbol.bit)
          (encodeSparseMemory w m ++ [.memoryEnd])) copyState
        (fun
          | .work0 => (fixedBits w address).reverse.map SparseSymbol.bit
          | .work1 => (fixedBits w accumulator).reverse.map SparseSymbol.bit
          | .memory => encodeSparseMemory w m ++ [.memoryEnd]
          | k => storePreparedStacks w address accumulator m base k) =
      lensRenamedCfg (Λx := R) prependCoreRenaming FullInterpreterState.prependLens
        (prependLocalCfg .cellEnd
          ((fixedBits w address).reverse.map SparseSymbol.bit)
          ((fixedBits w accumulator).reverse.map SparseSymbol.bit)
          (encodeSparseMemory w m ++ [.memoryEnd])) copyState
        (storePreparedStacks w address accumulator m base) := by
    rw [hstacks]
  have hprepend' :
      ((fun o => o.bind (TM2.step
        (fullPrependProgram returnLabel right)))^[2 * w + 6])
        (some (lensRenamedCfg (Λx := R) prependCoreRenaming
          FullInterpreterState.prependLens
          (prependLocalCfg .cellEnd
            ((fixedBits w address).reverse.map SparseSymbol.bit)
            ((fixedBits w accumulator).reverse.map SparseSymbol.bit)
            (encodeSparseMemory w m ++ [.memoryEnd])) copyState
          (storePreparedStacks w address accumulator m base))) =
      some (mapLabelCfg Sum.inr
        (cleanReturnCfg returnLabel
          (FullInterpreterState.prependLens.put copyState default)
          (operandBoundaryBase w accumulator
            (m.write w address accumulator) base))) := by
    calc
      _ = ((fun o => o.bind (TM2.step
          (fullPrependProgram returnLabel right)))^[2 * w + 6])
          (some (lensRenamedCfg (Λx := R) prependCoreRenaming
            FullInterpreterState.prependLens
            (prependLocalCfg .cellEnd
              ((fixedBits w address).reverse.map SparseSymbol.bit)
              ((fixedBits w accumulator).reverse.map SparseSymbol.bit)
              (encodeSparseMemory w m ++ [.memoryEnd])) copyState
            (fun
              | .work0 => (fixedBits w address).reverse.map SparseSymbol.bit
              | .work1 => (fixedBits w accumulator).reverse.map SparseSymbol.bit
              | .memory => encodeSparseMemory w m ++ [.memoryEnd]
              | k => storePreparedStacks w address accumulator m base k))) :=
        congrArg
          (fun c => ((fun o => o.bind (TM2.step
            (fullPrependProgram returnLabel right)))^[2 * w + 6]) (some c))
          hcfg.symm
      _ = _ := hprepend
  have htail := chain_liftRightProgram storePrependResetProgram
    (fullPrependProgram returnLabel right) hreset hprepend'
  have hlift := transport_iterate_liftRightProgram
    (lensPhaseLeft
      (copyCoreRenaming .accumulator .work1 .work7
        (by decide) (by decide) (by decide))
      FullInterpreterState.moveLens copyProgram .done
      (Sum.inl StorePrependResetLabel.reset))
    (storePrependTailProgram returnLabel right) htail
  have hchain := chain_loadInstruction_iterations
    (fun o : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (FullStoreLabel R) (FullInterpreterState N)) =>
        o.bind (TM2.step (fullStoreProgram returnLabel right)))
    hcopy hlift
  refine ⟨FullInterpreterState.prependLens.put copyState default, ?_⟩
  have htime : 4 * w + 10 = (2 * w + 3) + (1 + (2 * w + 6)) := by omega
  rw [htime]
  simpa [fullStoreProgram, copyState] using hchain

end Lax51Proofs.RamToTM
