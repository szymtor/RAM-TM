import Lax20Proofs.RamToTM.OutputAdapter
import Lax20.RamPolytime

namespace Lax20Proofs.RamToTM

open Lax20.BinaryWordEncoding Lax20.RamPolytime
open Polynomial

noncomputable section

/-- The RAM width selected by the TM simulator.  The extra bit makes the
strict positivity required by the fixed-width interpreter unconditional. -/
def simulationWordWidth (wordBound : Polynomial Nat) (x : List Nat) : Nat :=
  (polynomialSimpleMajorant wordBound).eval (bitSize x) + 1

theorem simulationWordWidth_pos (wordBound : Polynomial Nat) (x : List Nat) :
    0 < simulationWordWidth wordBound x := by
  simp [simulationWordWidth]

theorem fitsInWords_mono {u v : Nat} (huv : u ≤ v) {xs : List Nat}
    (h : FitsInWords u xs) : FitsInWords v xs := by
  intro a ha
  exact (h a ha).trans_le (Nat.pow_le_pow_right (by omega) huv)

theorem fits_simulationWordWidth (wordBound : Polynomial Nat)
    (x output : List Nat)
    (hfit : FitsInWords (wordBound.eval (bitSize x))
      ((x.length :: x) ++ output)) :
    FitsInWords (simulationWordWidth wordBound x)
      ((x.length :: x) ++ output) := by
  apply fitsInWords_mono (h := hfit)
  exact (polynomial_eval_le_simpleMajorant wordBound (bitSize x)).trans
    (by simp [simulationWordWidth])

/-- Sparse stack payload that the canonical-input adapter must produce. -/
def preprocessedInput (wordBound : Polynomial Nat) (x : List Nat) :
    List SparseSymbol :=
  encodeInputStack (simulationWordWidth wordBound x) (x.length :: x)

@[simp] theorem preprocessedInput_length (wordBound : Polynomial Nat)
    (x : List Nat) :
    (preprocessedInput wordBound x).length =
      (x.length + 1) * (simulationWordWidth wordBound x + 1) + 1 := by
  simp [preprocessedInput]

/-- A polynomial upper bound for the size of the preprocessed RAM input. -/
def inputPayloadPolynomial (wordBound : Polynomial Nat) : Polynomial Nat :=
  (X + 1) * (polynomialSimpleMajorant wordBound + 2) + 1

@[simp] theorem inputPayloadPolynomial_eval (wordBound : Polynomial Nat)
    (n : Nat) :
    (inputPayloadPolynomial wordBound).eval n =
      (n + 1) * ((polynomialSimpleMajorant wordBound).eval n + 2) + 1 := by
  simp [inputPayloadPolynomial]

theorem preprocessedInput_length_le (wordBound : Polynomial Nat)
    (x : List Nat) :
    (preprocessedInput wordBound x).length ≤
      (inputPayloadPolynomial wordBound).eval (bitSize x) := by
  rw [preprocessedInput_length, inputPayloadPolynomial_eval]
  have hx := Lax20Proofs.Encoding.length_le_bitSize x
  simp only [simulationWordWidth]
  gcongr

/-! The first executable preprocessing phase consumes the canonical input,
keeps a reversed sparse copy on `work0`, records its symbol length in unary
on `work1`, and records the number of encoded words on `work2`.  All three
are later used by the fixed-width padding phase. -/

inductive InputScanLabel
  | scan
  | decide
  | separator
  | zero
  | one
  | counted
  | done
  deriving DecidableEq, Fintype, Inhabited

def inputScanProgram {N : Nat} {L : Type} : InputScanLabel →
    Turing.TM2.Stmt WrapperAlphabet (Sum L InputScanLabel) (WrapperState N)
  | .scan =>
      .pop .input (fun s a => {s with heldInput := a}) <|
      .goto fun _ => .inr .decide
  | .decide =>
      .branch (fun s => s.heldInput.isNone)
        (.goto fun _ => .inr .done) <|
      .branch (fun s => match s.heldInput with
        | some .separator => true
        | _ => false)
        (.goto fun _ => .inr .separator) <|
      .branch (fun s => match s.heldInput with
        | some .one => true
        | _ => false)
        (.goto fun _ => .inr .one) <|
      .goto fun _ => .inr .zero
  | .separator =>
      .push (.core .work0) (fun _ => .wordEnd) <|
      .push (.core .work2) (fun _ => .wordEnd) <|
      .goto fun _ => .inr .counted
  | .zero =>
      .push (.core .work0) (fun _ => .bit false) <|
      .goto fun _ => .inr .counted
  | .one =>
      .push (.core .work0) (fun _ => .bit true) <|
      .goto fun _ => .inr .counted
  | .counted =>
      .push (.core .work1) (fun _ => .wordEnd) <|
      .load (fun s => {s with heldInput := none}) <|
      .goto fun _ => .inr .scan
  | .done => .halt

def sparseOfInputSymbol : Symbol → SparseSymbol
  | .separator => .wordEnd
  | .zero => .bit false
  | .one => .bit true

def inputSeparatorCount : List Symbol → Nat
  | [] => 0
  | .separator :: xs => inputSeparatorCount xs + 1
  | _ :: xs => inputSeparatorCount xs

theorem inputSeparatorCount_append (xs ys : List Symbol) :
    inputSeparatorCount (xs ++ ys) =
      inputSeparatorCount xs + inputSeparatorCount ys := by
  induction xs with
  | nil => simp [inputSeparatorCount]
  | cons x xs ih => cases x <;> simp [inputSeparatorCount, ih] <;> omega

theorem inputSeparatorCount_bits (bits : List Bool) :
    inputSeparatorCount
      (bits.map (fun b => if b then Symbol.one else Symbol.zero)) = 0 := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [inputSeparatorCount, ih]

theorem inputSeparatorCount_encode (x : List Nat) :
    inputSeparatorCount (encode x) = x.length := by
  induction x with
  | nil => rfl
  | cons n x ih =>
      simp only [encode, List.flatMap_cons, encodeNat]
      change inputSeparatorCount
        (n.bits.map (fun b => if b then Symbol.one else Symbol.zero) ++ encode x) + 1 =
          x.length + 1
      rw [inputSeparatorCount_append, inputSeparatorCount_bits, ih]
      omega

def inputScanStacks (input : List Symbol) (seen : List Symbol)
    (base : (k : WrapperStack) → List (WrapperAlphabet k)) :
    (k : WrapperStack) → List (WrapperAlphabet k) :=
  Function.update
    (Function.update
      (Function.update
        (Function.update base .input input)
          (.core .work0) (seen.reverse.map sparseOfInputSymbol))
        (.core .work1) (List.replicate seen.length .wordEnd))
      (.core .work2) (List.replicate (inputSeparatorCount seen) .wordEnd)

@[simp] theorem inputScanStacks_input (input seen base) :
    inputScanStacks input seen base .input = input := by
  simp [inputScanStacks]

@[simp] theorem inputScanStacks_work0 (input seen base) :
    inputScanStacks input seen base (.core .work0) =
      seen.reverse.map sparseOfInputSymbol := by
  simp [inputScanStacks]
  rfl

@[simp] theorem inputScanStacks_work1 (input seen base) :
    inputScanStacks input seen base (.core .work1) =
      List.replicate seen.length .wordEnd := by
  simp [inputScanStacks]

@[simp] theorem inputScanStacks_work2 (input seen base) :
    inputScanStacks input seen base (.core .work2) =
      List.replicate (inputSeparatorCount seen) .wordEnd := by
  simp [inputScanStacks]

def inputScanStepStacks (symbol : Symbol) (tail seen : List Symbol)
    (base : (k : WrapperStack) → List (WrapperAlphabet k)) :
    (k : WrapperStack) → List (WrapperAlphabet k) :=
  let s₀ := Function.update (inputScanStacks (symbol :: tail) seen base) .input tail
  let s₁ := Function.update s₀ (.core .work0)
    (sparseOfInputSymbol symbol :: s₀ (.core .work0))
  let s₂ := match symbol with
    | .separator => Function.update s₁ (.core .work2)
        (.wordEnd :: s₁ (.core .work2))
    | _ => s₁
  Function.update s₂ (.core .work1) (.wordEnd :: s₂ (.core .work1))

theorem inputScanStepStacks_eq (symbol : Symbol) (tail seen : List Symbol)
    (base : (k : WrapperStack) → List (WrapperAlphabet k)) :
    inputScanStepStacks symbol tail seen base =
      inputScanStacks tail (seen ++ [symbol]) base := by
  funext k
  cases symbol <;> cases k with
  | input => simp [inputScanStepStacks, inputScanStacks, Function.update]
  | output => simp [inputScanStepStacks, inputScanStacks, Function.update]
  | core k =>
      cases k <;> simp [inputScanStepStacks, inputScanStacks,
        sparseOfInputSymbol, inputSeparatorCount, List.reverse_append,
        inputSeparatorCount_append, Function.update, List.replicate_succ,
        Nat.add_assoc]

def inputScanMachine {N : Nat} :
    Sum Empty InputScanLabel →
      Turing.TM2.Stmt WrapperAlphabet (Sum Empty InputScanLabel)
        (WrapperState N) :=
  liftCoreProgram (fun _ : Empty => .halt)
    (inputScanProgram (N := N) (L := Empty))

def inputScanCfg {N : Nat} (label : InputScanLabel) (state : WrapperState N)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    Turing.TM2.Cfg WrapperAlphabet (Sum Empty InputScanLabel) (WrapperState N) :=
  ⟨some (.inr label), state, tapes⟩

theorem input_scan_symbol_run {N : Nat} (symbol : Symbol)
    (tail seen : List Symbol) (state : WrapperState N)
    (base : (k : WrapperStack) → List (WrapperAlphabet k)) :
    ((fun x => x.bind (Turing.TM2.step inputScanMachine))^[4])
      (some (inputScanCfg .scan {state with heldInput := none}
        (inputScanStacks (symbol :: tail) seen base))) =
    some (inputScanCfg .scan {state with heldInput := none}
      (inputScanStacks tail (seen ++ [symbol]) base)) := by
  have hst := inputScanStepStacks_eq symbol tail seen base
  rw [← hst]
  cases symbol <;>
    simp [inputScanMachine, inputScanCfg, inputScanProgram,
      liftCoreProgram, Turing.TM2.step, Turing.TM2.stepAux,
      inputScanStepStacks, inputScanStacks, sparseOfInputSymbol, inputSeparatorCount,
      List.reverse_append, Function.update_of_ne, List.head?, List.tail,
      Option.isNone,
      show decide (some Symbol.separator = some Symbol.separator) = true by decide,
      show decide (some Symbol.zero = some Symbol.separator) = false by decide,
      show decide (some Symbol.one = some Symbol.separator) = false by decide,
      show decide (some Symbol.separator = some Symbol.one) = false by decide,
      show decide (some Symbol.zero = some Symbol.one) = false by decide,
      show decide (some Symbol.one = some Symbol.one) = true by decide,
      show decide (some Symbol.zero = some Symbol.zero) = true by decide,
      show decide (some Symbol.one = some Symbol.zero) = false by decide]

theorem input_scan_run {N : Nat} (input seen : List Symbol)
    (state : WrapperState N)
    (base : (k : WrapperStack) → List (WrapperAlphabet k)) :
    ((fun x => x.bind (Turing.TM2.step inputScanMachine))^[
        4 * input.length])
      (some (inputScanCfg .scan {state with heldInput := none}
        (inputScanStacks input seen base))) =
    some (inputScanCfg .scan {state with heldInput := none}
      (inputScanStacks [] (seen ++ input) base)) := by
  induction input generalizing seen with
  | nil => simp
  | cons symbol tail ih =>
      rw [List.length_cons, show 4 * (tail.length + 1) = 4 * tail.length + 4 by omega,
        Function.iterate_add_apply]
      rw [input_scan_symbol_run]
      simpa [List.append_assoc] using ih (seen ++ [symbol])

theorem input_scan_finish {N : Nat} (seen : List Symbol)
    (state : WrapperState N)
    (base : (k : WrapperStack) → List (WrapperAlphabet k)) :
    ((fun x => x.bind (Turing.TM2.step inputScanMachine))^[2])
      (some (inputScanCfg .scan {state with heldInput := none}
        (inputScanStacks [] seen base))) =
    some (inputScanCfg .done {state with heldInput := none}
      (inputScanStacks [] seen base)) := by
  simp [inputScanMachine, inputScanCfg, inputScanProgram, liftCoreProgram,
    Turing.TM2.step, Turing.TM2.stepAux, List.head?, List.tail, Option.isNone]
  constructor <;> rfl

theorem input_scan_all {N : Nat} (input : List Symbol)
    (state : WrapperState N)
    (base : (k : WrapperStack) → List (WrapperAlphabet k)) :
    ((fun x => x.bind (Turing.TM2.step inputScanMachine))^[
        4 * input.length + 2])
      (some (inputScanCfg .scan {state with heldInput := none}
        (inputScanStacks input [] base))) =
    some (inputScanCfg .done {state with heldInput := none}
      (inputScanStacks [] input base)) := by
  exact chain_iterations _ (input_scan_run input [] state base)
    (input_scan_finish input state base)

theorem input_scan_encode {N : Nat} (x : List Nat)
    (state : WrapperState N)
    (base : (k : WrapperStack) → List (WrapperAlphabet k)) :
    let finalStacks := inputScanStacks [] (encode x) base
    ((fun z => z.bind (Turing.TM2.step inputScanMachine))^[
        4 * bitSize x + 2])
      (some (inputScanCfg .scan {state with heldInput := none}
        (inputScanStacks (encode x) [] base))) =
      some (inputScanCfg .done {state with heldInput := none} finalStacks) ∧
    finalStacks (.core .work0) =
      (encode x).reverse.map sparseOfInputSymbol ∧
    finalStacks (.core .work1) =
      List.replicate (bitSize x) .wordEnd ∧
    finalStacks (.core .work2) =
      List.replicate x.length .wordEnd := by
  dsimp
  refine ⟨?_, by simp, by simp [bitSize], ?_⟩
  · simpa [bitSize] using input_scan_all (N := N) (encode x) state base
  · simp [inputSeparatorCount_encode]

/-- Linear polynomial accounting for the complete canonical-input scan. -/
def inputScanPolynomial : Polynomial Nat := 4 * X + 2

@[simp] theorem inputScanPolynomial_eval (n : Nat) :
    inputScanPolynomial.eval n = 4 * n + 2 := by
  simp [inputScanPolynomial]

end

end Lax20Proofs.RamToTM
