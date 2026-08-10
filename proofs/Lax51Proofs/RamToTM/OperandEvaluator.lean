import Lax51Proofs.RamToTM.FullAddMacro
import Lax51Proofs.RamToTM.IndirectOperandPipeline

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax13.Ram

def operandArgument : Op -> Nat
  | .lit n | .mem n | .ind n => n

def OperandEvalLabel (o : Op) (R : Type) : Type :=
  match o with
  | .lit _ => Sum LiteralWordLabel R
  | .mem _ => DirectOperandLabel R
  | .ind _ => IndirectOperandLabel R

noncomputable instance (o : Op) (R : Type) :
    DecidableEq (OperandEvalLabel o R) := Classical.decEq _

instance (o : Op) (R : Type) [Fintype R] : Fintype (OperandEvalLabel o R) := by
  cases o <;> dsimp [OperandEvalLabel] <;> infer_instance

instance (o : Op) (R : Type) : Inhabited (OperandEvalLabel o R) := by
  cases o <;> exact ⟨Sum.inl default⟩

def operandEvalProgram {N : Nat} {R : Type} (o : Op) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    OperandEvalLabel o R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (OperandEvalLabel o R) (FullInterpreterState N) :=
  match o with
  | .lit _ => literalOperandProgram returnLabel right
  | .mem _ => directOperandProgram returnLabel right
  | .ind _ => indirectOperandProgram returnLabel right

def operandEvalStartCfg {N : Nat} {R : Type} (o : Op)
    (hN : operandArgument o <= N) (w accumulator : Nat)
    (m : SparseMemory) (state : FullInterpreterState N)
    (base : CoreStack -> List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (OperandEvalLabel o R) (FullInterpreterState N) :=
  match o with
  | .lit n => literalOperandStartCfg n (by simpa [operandArgument] using hN)
      w accumulator m state base
  | .mem a => lensRenamedCfg literalQueryCoreRenaming
      FullInterpreterState.literalLens
      (boundedLiteralWordCfg N .emit
        ⟨a, by simpa [operandArgument] using hN⟩
        ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
      state (operandBoundaryBase w accumulator m base)
  | .ind a => lensRenamedCfg literalQueryCoreRenaming
      FullInterpreterState.literalLens
      (boundedLiteralWordCfg N .emit
        ⟨a, by simpa [operandArgument] using hN⟩
        ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
      state (operandBoundaryBase w accumulator m base)

def embedOperandReturnCfg {N : Nat} {R : Type} (o : Op)
    (c : TM2.Cfg (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (OperandEvalLabel o R) (FullInterpreterState N) :=
  match o with
  | .lit _ => mapLabelCfg Sum.inr c
  | .mem _ => embedDirectReturnCfg c
  | .ind _ => embedIndirectReturnCfg c

def operandEvalBound (w : Nat) (m : SparseMemory) : Nat :=
  2 * (m.length * (12 * w + 22)) + 28 * w + 61

theorem directOperand_correct_uniform {N : Nat} {R : Type}
    (address : Nat) (haN : address <= N)
    (w accumulator : Nat) (m : SparseMemory) (hm : m.Normalized w)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N)
    (base : CoreStack -> List SparseSymbol) :
    ∃ steps, steps <= operandEvalBound w m ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (directOperandProgram returnLabel right)))^[steps])
        (some (operandEvalStartCfg (R := R) (.mem address) haN
          w accumulator m state base)) =
      some (embedDirectReturnCfg
        (cleanReturnCfg returnLabel finalState
          (operandResultBase w accumulator
            (operandWordValue w (.mem address) m) m base))) := by
  cases hfind : m.find? (address % 2 ^ w) with
  | none =>
      have hread : m.read (address % 2 ^ w) = 0 := by
        have h := SparseMemory.find?_getD m (address % 2 ^ w)
        rw [hfind] at h
        exact h.symm
      let finalState := FullInterpreterState.zeroLens.put
        (FullInterpreterState.moveLens.put
          (lookupRecordOutcome .missing
            (FullInterpreterState.lookupLens.put
              (FullInterpreterState.literalLens.put state
                ⟨none, ⟨address / 2 ^ w, by
                  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩)
              ⟨none, decide m.isEmpty, none, none⟩)) default) default
      refine ⟨m.length * (12 * w + 22) + 5 * w + 13, by
        simp [operandEvalBound]
        omega, finalState, ?_⟩
      simpa [operandEvalStartCfg, operandArgument, operandWordValue,
        sparseValue, Op.value, hread, finalState] using
        directOperand_missing_clean address haN w accumulator m hm hfind
          returnLabel right state base
  | some value =>
      have hread : m.read (address % 2 ^ w) = value := by
        have h := SparseMemory.find?_getD m (address % 2 ^ w)
        rw [hfind] at h
        exact h.symm
      have hvalue : value < 2 ^ w := by
        rw [← hread]
        exact SparseMemory.read_lt_of_normalized hm _
      rcases directOperand_found_clean address haN w accumulator value m hm
        hfind returnLabel right state base with ⟨steps, hsteps, hrun⟩
      let finalState := FullInterpreterState.moveLens.put
        (lookupRecordOutcome .found
          (FullInterpreterState.lookupLens.put
            (FullInterpreterState.literalLens.put state
              ⟨none, ⟨address / 2 ^ w, by
                exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩)
            ⟨none, true, none, none⟩)) default
      refine ⟨steps, ?_, finalState, ?_⟩
      · simp [operandEvalBound]
        omega
      · simpa [operandEvalStartCfg, operandArgument, operandWordValue,
          sparseValue, Op.value, hread,
          Nat.mod_eq_of_lt hvalue, finalState]
          using hrun

theorem operandEval_correct {N : Nat} {R : Type}
    (o : Op) (hN : operandArgument o <= N)
    (w accumulator : Nat) (m : SparseMemory) (hm : m.Normalized w)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N)
    (base : CoreStack -> List SparseSymbol) :
    ∃ steps, steps <= operandEvalBound w m ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (operandEvalProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg (R := R) o hN
          w accumulator m state base)) =
      some (embedOperandReturnCfg o
        (cleanReturnCfg returnLabel finalState
          (operandResultBase w accumulator (operandWordValue w o m) m base))) := by
  cases o with
  | lit n =>
      change n <= N at hN
      let finalState := FullInterpreterState.literalLens.put state
        ⟨none, ⟨n / 2 ^ w, by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩
      refine ⟨2 * w + 3, by simp [operandEvalBound]; omega,
        finalState, ?_⟩
      simpa [operandEvalProgram, operandEvalStartCfg, operandArgument,
        embedOperandReturnCfg] using
        literalOperand_correct n hN
          w accumulator m returnLabel right state base
  | mem a =>
      change a <= N at hN
      simpa [operandEvalProgram, embedOperandReturnCfg] using
        directOperand_correct_uniform a hN w accumulator m hm
          returnLabel right state base
  | ind a =>
      change a <= N at hN
      have hp : m.read (a % 2 ^ w) < 2 ^ w :=
        SparseMemory.read_lt_of_normalized hm _
      have hv : m.read (m.read (a % 2 ^ w)) < 2 ^ w :=
        SparseMemory.read_lt_of_normalized hm _
      simpa [operandEvalProgram, operandEvalStartCfg, operandArgument,
        embedOperandReturnCfg, operandEvalBound, operandWordValue,
        sparseValue, Op.value, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hv] using
        indirectOperand_correct a hN w accumulator m hm returnLabel right
          state base

theorem transport_iterate_operand_right {N : Nat} {R : Type}
    (o : Op) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    {steps : Nat}
    {c d : TM2.Cfg (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)}
    (hrun : ((fun x => x.bind (TM2.step right))^[steps])
      (some c) = some d) :
    ((fun x => x.bind (TM2.step
      (operandEvalProgram o returnLabel right)))^[steps])
      (some (embedOperandReturnCfg o c)) =
    some (embedOperandReturnCfg o d) := by
  cases o with
  | lit n =>
      simpa [operandEvalProgram, embedOperandReturnCfg] using
        transport_iterate_literal_right returnLabel right hrun
  | mem a =>
      simpa [operandEvalProgram, embedOperandReturnCfg] using
        transport_iterate_direct_right returnLabel right hrun
  | ind a =>
      simpa [operandEvalProgram, embedOperandReturnCfg] using
        transport_iterate_indirect_right returnLabel right hrun

end Lax51Proofs.RamToTM
