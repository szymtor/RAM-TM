import Lax51Proofs.RamToTM.StoreInstruction

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax51Proofs.Microcode

inductive ReadTransferLabel
  | initialize | loop
  deriving DecidableEq, Fintype, Inhabited

abbrev ReadTailLabel (R : Type) := Sum ReadTransferLabel (FullPrependLabel R)

abbrev ReadInstructionLabel (address : Nat) (R : Type) :=
  OperandEvalLabel (.lit address) (ReadTailLabel R)

def readTransferLeftProgram {N : Nat} {R : Type} (exhaustedLabel : R) :
    ReadTransferLabel -> TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (ReadTailLabel R) (FullInterpreterState N)
  | .initialize =>
      .load (fun s => FullInterpreterState.moveLens.put s default) <|
      .goto fun _ => Sum.inl .loop
  | .loop =>
      .pop .input (fun s a => FullInterpreterState.moveLens.put s ⟨a⟩) <|
      .branch
        (fun s => (FullInterpreterState.moveLens.get s).held = some .inputEnd ∨
          (FullInterpreterState.moveLens.get s).held.isNone)
        (.load (fun s => FullInterpreterState.moveLens.put s default) <|
          .goto fun _ => Sum.inr (Sum.inr exhaustedLabel)) <|
      .branch
        (fun s => (FullInterpreterState.moveLens.get s).held = some .wordEnd)
        (.load (fun s => FullInterpreterState.prependLens.put
            (FullInterpreterState.moveLens.put s default) default) <|
          .goto fun _ => Sum.inr (Sum.inl PrependCellLabel.cellEnd))
        (.push .work1
          (fun s => (FullInterpreterState.moveLens.get s).held.getD (.bit false)) <|
          .load (fun s => FullInterpreterState.moveLens.put s default) <|
            .goto fun _ => Sum.inl .loop)

/-- Destructively remove the first encoded input word and place its reversed
bits on `work1`, where the verified prepend-cell macro expects its value. -/
def readTransferProgram {N : Nat} {R : Type} (exhaustedLabel returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ReadTailLabel R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (ReadTailLabel R) (FullInterpreterState N) :=
  liftRightProgram (readTransferLeftProgram exhaustedLabel)
    (fullPrependProgram returnLabel right)

def readInstructionProgram {N : Nat} {R : Type} (address : Nat)
    (exhaustedLabel returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ReadInstructionLabel address R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ReadInstructionLabel address R)
      (FullInterpreterState N) :=
  operandEvalProgram (.lit address) (Sum.inl ReadTransferLabel.initialize)
    (readTransferProgram exhaustedLabel returnLabel right)

def readTransferStacks (input value : List SparseSymbol)
    (base : CoreStack -> List SparseSymbol) : CoreStack -> List SparseSymbol
  | .input => input
  | .work1 => value
  | k => base k

def readTransferCfg {N : Nat} {R : Type} (state : FullInterpreterState N)
    (input value : List SparseSymbol) (base : CoreStack -> List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol) (ReadTailLabel R)
      (FullInterpreterState N) :=
  ⟨some (Sum.inl .loop), state, readTransferStacks input value base⟩

theorem readTransfer_initialize {N : Nat} {R : Type}
    (exhaustedLabel returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator address : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    TM2.step (readTransferProgram exhaustedLabel returnLabel right)
      (cleanReturnCfg (Sum.inl ReadTransferLabel.initialize) state
        (operandResultBase w accumulator address m base)) =
    some (readTransferCfg (FullInterpreterState.moveLens.put state default)
      (base .input) [] (operandResultBase w accumulator address m base)) := by
  simp [readTransferProgram, cleanReturnCfg, readTransferCfg,
    readTransferLeftProgram, readTransferStacks, operandResultBase,
    liftRightProgram, TM2.step]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem readTransfer_step_exhausted {N : Nat} {R : Type}
    (exhaustedLabel returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N) (value : List SparseSymbol)
    (base : CoreStack -> List SparseSymbol) :
    TM2.step (readTransferProgram exhaustedLabel returnLabel right)
      (readTransferCfg state [.inputEnd] value base) =
    some ⟨some (Sum.inr (Sum.inr exhaustedLabel)),
      FullInterpreterState.moveLens.put state default,
      readTransferStacks [] value base⟩ := by
  simp [readTransferProgram, readTransferCfg, readTransferStacks,
    readTransferLeftProgram, liftRightProgram, TM2.step, Function.update,
    FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem readTransfer_step_bit {N : Nat} {R : Type}
    (exhaustedLabel returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N) (bit : Bool)
    (input value : List SparseSymbol)
    (base : CoreStack -> List SparseSymbol) :
    TM2.step (readTransferProgram exhaustedLabel returnLabel right)
      (readTransferCfg state (.bit bit :: input) value base) =
    some (readTransferCfg
      (FullInterpreterState.moveLens.put state default)
      input (.bit bit :: value) base) := by
  simp [readTransferProgram, readTransferCfg, readTransferStacks,
    readTransferLeftProgram, liftRightProgram, TM2.step, Function.update,
    FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem readTransfer_step_end {N : Nat} {R : Type}
    (exhaustedLabel returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N) (input value : List SparseSymbol)
    (base : CoreStack -> List SparseSymbol) :
    TM2.step (readTransferProgram exhaustedLabel returnLabel right)
      (readTransferCfg state (.wordEnd :: input) value base) =
    some (⟨some (Sum.inr (Sum.inl PrependCellLabel.cellEnd)),
      FullInterpreterState.prependLens.put
        (FullInterpreterState.moveLens.put state default) default,
      readTransferStacks input value base⟩) := by
  simp [readTransferProgram, readTransferCfg, readTransferStacks,
    readTransferLeftProgram, liftRightProgram, TM2.step, Function.update,
    FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]
  congr 2
  funext k
  cases k <;> rfl

theorem readTransfer_fixed_correct {N : Nat} {R : Type}
    (exhaustedLabel returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w value : Nat) (input : List SparseSymbol)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ((fun o => o.bind (TM2.step
      (readTransferProgram exhaustedLabel returnLabel right)))^[w + 1])
      (some (readTransferCfg (FullInterpreterState.moveLens.put state default)
        (encodeFixedWord w value ++ input) [] base)) =
    some (⟨some (Sum.inr (Sum.inl PrependCellLabel.cellEnd)),
      FullInterpreterState.prependLens.put
        (FullInterpreterState.moveLens.put state default) default,
      readTransferStacks input
        ((fixedBits w value).reverse.map SparseSymbol.bit) base⟩) := by
  let stepO := fun o : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (ReadTailLabel R) (FullInterpreterState N)) =>
    o.bind (TM2.step (readTransferProgram exhaustedLabel returnLabel right))
  let cleanState := FullInterpreterState.moveLens.put state default
  have bitsRun (xs : List Bool) (acc : List SparseSymbol) :
      (stepO^[xs.length])
        (some (readTransferCfg cleanState
          (xs.map SparseSymbol.bit ++ .wordEnd :: input) acc base)) =
      some (readTransferCfg cleanState
        (.wordEnd :: input) (xs.reverse.map SparseSymbol.bit ++ acc) base) := by
    induction xs generalizing acc with
    | nil => rfl
    | cons bit bits ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [List.map_cons, List.cons_append, stepO, Option.bind_some,
        readTransfer_step_bit, cleanState,
        FullInterpreterState.moveLens.put_put]
      rw [ih]
      change some (readTransferCfg cleanState (.wordEnd :: input)
        ((bits.reverse.map SparseSymbol.bit) ++ .bit bit :: acc) base) = _
      simp [List.reverse_cons, List.map_append, List.append_assoc, cleanState]
  rw [encodeFixedWord, Nat.add_comm, Function.iterate_add_apply]
  simp only [List.append_assoc, List.singleton_append]
  change (stepO^[1]) ((stepO^[w]) _) = _
  have hrun := bitsRun (fixedBits w value) []
  simp only [fixedBits_length] at hrun
  rw [hrun]
  simp [stepO, cleanState, FullInterpreterState.moveLens.put_put]

theorem readTail_correct {N : Nat} {R : Type}
    (exhaustedLabel returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator address value : Nat) (m : SparseMemory)
    (inputTail : List SparseSymbol)
    (base : CoreStack -> List SparseSymbol)
    (hinput : base .input = encodeFixedWord w value ++ inputTail)
    (state : FullInterpreterState N) :
    ∃ finalState,
      ((fun o => o.bind (TM2.step
        (readTransferProgram exhaustedLabel returnLabel right)))^[
        3 * w + 8])
        (some (cleanReturnCfg (Sum.inl ReadTransferLabel.initialize) state
          (operandResultBase w accumulator address m base))) =
      some (mapLabelCfg Sum.inr (mapLabelCfg Sum.inr
        (cleanReturnCfg returnLabel finalState
          (prependResultStacks w address value m
            (readTransferStacks inputTail
              ((fixedBits w value).reverse.map SparseSymbol.bit)
              (operandResultBase w accumulator address m base)))))) := by
  let cleanState := FullInterpreterState.moveLens.put state default
  let transferBase := operandResultBase w accumulator address m base
  have hinit :
      ((fun o => o.bind (TM2.step
        (readTransferProgram exhaustedLabel returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl ReadTransferLabel.initialize) state
          transferBase)) =
      some (readTransferCfg cleanState
        (encodeFixedWord w value ++ inputTail) [] transferBase) := by
    simpa [cleanState, transferBase, hinput] using
      readTransfer_initialize exhaustedLabel returnLabel right w accumulator address m base state
  have htransfer := readTransfer_fixed_correct exhaustedLabel returnLabel right
    w value inputTail transferBase state
  let prependBase := readTransferStacks inputTail
    ((fixedBits w value).reverse.map SparseSymbol.bit) transferBase
  let prependCfg := lensRenamedCfg (Λx := R) prependCoreRenaming
    FullInterpreterState.prependLens
    (prependLocalCfg .cellEnd
      ((fixedBits w address).reverse.map SparseSymbol.bit)
      ((fixedBits w value).reverse.map SparseSymbol.bit)
      (encodeSparseMemory w m ++ [.memoryEnd])) cleanState prependBase
  have hcfg :
      (⟨some (Sum.inr (Sum.inl PrependCellLabel.cellEnd)),
        FullInterpreterState.prependLens.put cleanState default,
        prependBase⟩ : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
          (ReadTailLabel R) (FullInterpreterState N)) =
      mapLabelCfg Sum.inr prependCfg := by
    simp [prependCfg, prependBase, transferBase, lensRenamedCfg,
      prependLocalCfg, mapLabelCfg, renamedStacks, prependCoreRenaming,
      prependCoreDecode, prependCoreEncode, prependCellStacks,
      readTransferStacks, operandResultBase]
    funext k
    cases k <;> simp [renamedStacks, prependCoreRenaming,
      prependCoreDecode, prependCellStacks, prependBase, transferBase,
      readTransferStacks, operandResultBase]
  have hfirst :
      ((fun o => o.bind (TM2.step
        (readTransferProgram exhaustedLabel returnLabel right)))^[
        1 + (w + 1)])
        (some (cleanReturnCfg (Sum.inl ReadTransferLabel.initialize) state
          transferBase)) = some (mapLabelCfg Sum.inr prependCfg) := by
    rw [Nat.add_comm, Function.iterate_add_apply, hinit, htransfer, hcfg]
  have hprepend := fullPrepend_fixed_correct returnLabel right
    w address value m prependBase cleanState
  have hprependCfg : prependCfg =
      lensRenamedCfg (Λx := R) prependCoreRenaming
        FullInterpreterState.prependLens
        (prependLocalCfg .cellEnd
          ((fixedBits w address).reverse.map SparseSymbol.bit)
          ((fixedBits w value).reverse.map SparseSymbol.bit)
          (encodeSparseMemory w m ++ [.memoryEnd])) cleanState
        (fun
          | .work0 => (fixedBits w address).reverse.map SparseSymbol.bit
          | .work1 => (fixedBits w value).reverse.map SparseSymbol.bit
          | .memory => encodeSparseMemory w m ++ [.memoryEnd]
          | k => prependBase k) := by
    simp [prependCfg, lensRenamedCfg]
    funext k
    cases k <;> simp [renamedStacks, prependCoreRenaming,
      prependCoreDecode, prependCellStacks]
  have hprepend' :
      ((fun o => o.bind (TM2.step (fullPrependProgram returnLabel right)))^[
        2 * w + 6]) (some prependCfg) =
      some (mapLabelCfg Sum.inr
        (cleanReturnCfg returnLabel
          (FullInterpreterState.prependLens.put cleanState default)
          (prependResultStacks w address value m prependBase))) := by
    rw [hprependCfg]
    exact hprepend
  have hall := chain_liftRightProgram (readTransferLeftProgram exhaustedLabel)
    (fullPrependProgram returnLabel right) hfirst hprepend'
  refine ⟨FullInterpreterState.prependLens.put cleanState default, ?_⟩
  have htime : 3 * w + 8 = (1 + (w + 1)) + (2 * w + 6) := by omega
  rw [htime]
  simpa [readTransferProgram, transferBase, prependBase, prependCfg] using hall

def readInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + (3 * w + 8)

theorem readResultStacks_coreStacks (w address value : Nat)
    (s : SparseState) (inputTail : List Nat) :
    prependResultStacks w address value s.mem
        (readTransferStacks (encodeInputStack w inputTail)
          ((fixedBits w value).reverse.map SparseSymbol.bit)
          (operandResultBase w s.acc (address % 2 ^ w) s.mem
            (coreStacks w s))) =
      coreStacks w { s with
        mem := s.mem.write w address value
        inp := inputTail } := by
  funext k
  cases k <;> simp [prependResultStacks, readTransferStacks,
    operandResultBase, coreStacks, encodeAccumulator, encodeMemoryStack,
    encodeInputStack]

theorem readInstruction_correct {N : Nat} {R : Type}
    (address : Nat) (hN : address <= N)
    (exhaustedLabel returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator value : Nat) (inputTail : List SparseSymbol)
    (m : SparseMemory) (hm : m.Normalized w)
    (base : CoreStack -> List SparseSymbol)
    (hinput : base .input = encodeFixedWord w value ++ inputTail)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= readInstructionBound w m ∧ ∃ finalState,
      ((fun o => o.bind (TM2.step
        (readInstructionProgram address exhaustedLabel returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := ReadTailLabel R) (.lit address) hN
          w accumulator m state base)) =
      some (embedOperandReturnCfg (.lit address)
        (mapLabelCfg Sum.inr (mapLabelCfg Sum.inr
          (cleanReturnCfg returnLabel finalState
            (prependResultStacks w address value m
              (readTransferStacks inputTail
                ((fixedBits w value).reverse.map SparseSymbol.bit)
                (operandResultBase w accumulator
                  (operandWordValue w (.lit address) m) m base))))))) := by
  rcases operandEval_correct (.lit address) hN w accumulator m hm
      (Sum.inl ReadTransferLabel.initialize)
      (readTransferProgram exhaustedLabel returnLabel right) state base with
    ⟨operandSteps, operandBound, operandState, hoperand⟩
  let wordAddress := operandWordValue w (.lit address) m
  rcases readTail_correct exhaustedLabel returnLabel right w accumulator wordAddress value m
      inputTail base hinput operandState with ⟨tailState, htail⟩
  have hlift := transport_iterate_operand_right (.lit address)
    (Sum.inl ReadTransferLabel.initialize)
    (readTransferProgram exhaustedLabel returnLabel right) htail
  have hchain := chain_loadInstruction_iterations
    (fun o : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (ReadInstructionLabel address R) (FullInterpreterState N)) =>
        o.bind (TM2.step
          (readInstructionProgram address exhaustedLabel returnLabel right)))
    hoperand hlift
  refine ⟨operandSteps + (3 * w + 8), ?_, tailState, ?_⟩
  · simp [readInstructionBound]
    omega
  · have hwrite : m.write w wordAddress value = m.write w address value := by
      simp [wordAddress, operandWordValue, SparseMemory.write_mod_address]
    have hresult :
        prependResultStacks w wordAddress value m
            (readTransferStacks inputTail
              ((fixedBits w value).reverse.map SparseSymbol.bit)
              (operandResultBase w accumulator wordAddress m base)) =
          prependResultStacks w address value m
            (readTransferStacks inputTail
              ((fixedBits w value).reverse.map SparseSymbol.bit)
              (operandResultBase w accumulator wordAddress m base)) := by
      funext k
      cases k <;> simp [prependResultStacks, hwrite]
    rw [hresult] at hchain
    simpa [readInstructionProgram, wordAddress] using hchain

theorem readInstruction_exhausted {N : Nat} {R : Type}
    (address : Nat) (hN : address <= N)
    (exhaustedLabel returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator : Nat) (m : SparseMemory) (hm : m.Normalized w)
    (base : CoreStack -> List SparseSymbol)
    (hinput : base .input = [.inputEnd])
    (state : FullInterpreterState N) :
    ∃ steps, steps <= operandEvalBound w m + 2 ∧ ∃ finalState,
      ((fun o => o.bind (TM2.step
        (readInstructionProgram address exhaustedLabel returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := ReadTailLabel R) (.lit address) hN
          w accumulator m state base)) =
      some (embedOperandReturnCfg (.lit address)
        ⟨some (Sum.inr (Sum.inr exhaustedLabel)), finalState,
          readTransferStacks [] []
            (operandResultBase w accumulator
              (operandWordValue w (.lit address) m) m base)⟩) := by
  rcases operandEval_correct (.lit address) hN w accumulator m hm
      (Sum.inl ReadTransferLabel.initialize)
      (readTransferProgram exhaustedLabel returnLabel right) state base with
    ⟨operandSteps, hoperandSteps, operandState, hoperand⟩
  have hinit := readTransfer_initialize exhaustedLabel returnLabel right
    w accumulator (operandWordValue w (.lit address) m) m base operandState
  have hexhaust := readTransfer_step_exhausted exhaustedLabel returnLabel right
    (FullInterpreterState.moveLens.put operandState default) []
    (operandResultBase w accumulator
      (operandWordValue w (.lit address) m) m base)
  simp only [hinput] at hinit
  have hinit' :
      ((fun o : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
        (ReadTailLabel R) (FullInterpreterState N)) =>
          o.bind (TM2.step
            (readTransferProgram exhaustedLabel returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl ReadTransferLabel.initialize)
          operandState (operandResultBase w accumulator
            (operandWordValue w (.lit address) m) m base))) =
      some (readTransferCfg
        (FullInterpreterState.moveLens.put operandState default)
        [.inputEnd] [] (operandResultBase w accumulator
          (operandWordValue w (.lit address) m) m base)) := by
    simpa using hinit
  have hexhaust' :
      ((fun o : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
        (ReadTailLabel R) (FullInterpreterState N)) =>
          o.bind (TM2.step
            (readTransferProgram exhaustedLabel returnLabel right)))^[1])
        (some (readTransferCfg
          (FullInterpreterState.moveLens.put operandState default)
          [.inputEnd] [] (operandResultBase w accumulator
            (operandWordValue w (.lit address) m) m base))) =
      some ⟨some (Sum.inr (Sum.inr exhaustedLabel)),
        FullInterpreterState.moveLens.put
          (FullInterpreterState.moveLens.put operandState default) default,
        readTransferStacks [] [] (operandResultBase w accumulator
          (operandWordValue w (.lit address) m) m base)⟩ := by
    simpa using hexhaust
  have htail := chain_loadInstruction_iterations
    (fun o : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (ReadTailLabel R) (FullInterpreterState N)) =>
        o.bind (TM2.step
          (readTransferProgram exhaustedLabel returnLabel right)))
    hinit' hexhaust'
  have hlift := transport_iterate_operand_right (.lit address)
    (Sum.inl ReadTransferLabel.initialize)
    (readTransferProgram exhaustedLabel returnLabel right) htail
  have hchain := chain_loadInstruction_iterations
    (fun o : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (ReadInstructionLabel address R) (FullInterpreterState N)) =>
        o.bind (TM2.step
          (readInstructionProgram address exhaustedLabel returnLabel right)))
    hoperand hlift
  refine ⟨operandSteps + 2, by omega,
    FullInterpreterState.moveLens.put operandState default, ?_⟩
  simpa [readInstructionProgram] using hchain

end Lax51Proofs.RamToTM
