import Lax20Proofs.TMToRam.Safety
import Lax20Proofs.Encoding

/-!
Concrete codecs between the length-prefixed native RAM tape and the binary
word encoding used by the simulated finite Turing machine.
-/

namespace Lax20Proofs.TMToRam

open Lax13Proofs.Imp

theorem BigStep.arr_length_eq {c : Com} {σ σ' : Env} {cost : ℕ}
    (hrun : BigStep c σ σ' cost) (name : String) :
    (σ'.arrs name).length = (σ.arrs name).length := by
  induction hrun with
  | skip | assign | read | write => rfl
  | store =>
      simp only [Env.setArr]
      split <;> simp_all
  | seq _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | ite_true _ _ ih | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | while_false => rfl

def inputCountVar : String := "tm_io_input_count"
def inputValueVar : String := "tm_io_input_value"
def inputHalfVar : String := "tm_io_input_half"
def inputBitVar : String := "tm_io_input_bit"
def encodedLengthVar : String := "tm_io_encoded_length"
def copyIndexVar : String := "tm_io_copy_index"
def ioValueVar : String := "tm_io_value"
def scratchName : String := "tm_io_scratch"

def outputIndexVar : String := "tm_io_output_index"
def outputCodeVar : String := "tm_io_output_code"
def outputValueVar : String := "tm_io_output_value"
def outputPlaceVar : String := "tm_io_output_place"
def outputHaveVar : String := "tm_io_output_have"

theorem topName_ne_copyIndexVar (stack : ℕ) : topName stack ≠ copyIndexVar := by
  intro h
  have hh := congrArg String.toList h
  simp [topName, copyIndexVar] at hh

theorem topName_ne_ioValueVar (stack : ℕ) : topName stack ≠ ioValueVar := by
  intro h
  have hh := congrArg String.toList h
  simp [topName, ioValueVar] at hh

theorem topName_ne_inputCountVar (stack : ℕ) : topName stack ≠ inputCountVar := by
  intro h
  have hh := congrArg String.toList h
  simp [topName, inputCountVar] at hh

theorem topName_ne_inputValueVar (stack : ℕ) : topName stack ≠ inputValueVar := by
  intro h
  have hh := congrArg String.toList h
  simp [topName, inputValueVar] at hh

theorem topName_ne_inputHalfVar (stack : ℕ) : topName stack ≠ inputHalfVar := by
  intro h
  have hh := congrArg String.toList h
  simp [topName, inputHalfVar] at hh

theorem topName_ne_inputBitVar (stack : ℕ) : topName stack ≠ inputBitVar := by
  intro h
  have hh := congrArg String.toList h
  simp [topName, inputBitVar] at hh

theorem topName_ne_encodedLengthVar (stack : ℕ) :
    topName stack ≠ encodedLengthVar := by
  intro h
  have hh := congrArg String.toList h
  simp [topName, encodedLengthVar] at hh

theorem scratchName_ne_stackName (stack : ℕ) : scratchName ≠ stackName stack := by
  intro h
  have hh := congrArg String.toList h
  simp [scratchName, stackName] at hh

theorem scratchName_ne_tableName (i : ℕ) : scratchName ≠ tableName i := by
  intro h
  have hh := congrArg String.toList h
  simp [scratchName, tableName] at hh

theorem copyIndexVar_ne_ioValueVar : copyIndexVar ≠ ioValueVar := by decide

/-- Append one literal symbol code to the temporary forward encoding. -/
def appendScratch (code : Expr) : Com :=
  seqs [
    .store scratchName (.var encodedLengthVar) code,
    .assign encodedLengthVar (.add (.var encodedLengthVar) (.lit 1))]

def appendScratchState (σ : Env) (code : ℕ) : Env :=
  (σ.setArr scratchName (σ.vars encodedLengthVar) code).setVar
    encodedLengthVar (σ.vars encodedLengthVar + 1)

theorem appendScratch_correct (σ : Env) (code : Expr) (value : ℕ)
    (hcode : code.eval σ = some value)
    (hroom : σ.vars encodedLengthVar < (σ.arrs scratchName).length) :
    BigStep (appendScratch code) σ (appendScratchState σ value)
      (code.size + 7) := by
  let σ₁ := σ.setArr scratchName (σ.vars encodedLengthVar) value
  let σ₂ := σ₁.setVar encodedLengthVar (σ.vars encodedLengthVar + 1)
  have hstore : BigStep
      (.store scratchName (.var encodedLengthVar) code) σ σ₁
      (2 + code.size) := by
    simpa [σ₁, Expr.eval, Expr.size, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      (BigStep.store (σ := σ) (a := scratchName)
        (i := .var encodedLengthVar) (e := code)
        (k := σ.vars encodedLengthVar) (v := value) rfl hcode hroom)
  have hassign : BigStep
      (.assign encodedLengthVar
        (.add (.var encodedLengthVar) (.lit 1))) σ₁ σ₂ 4 := by
    apply BigStep.assign
    simp [Expr.eval, σ₁, σ₂]
  have hrun := BigStep.seq hstore (BigStep.seq hassign (BigStep.skip (σ := σ₂)))
  convert hrun using 1 <;>
    simp [appendScratch, appendScratchState, seqs, σ₁, σ₂,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

theorem appendScratchState_length (σ : Env) (value : ℕ) :
    (appendScratchState σ value).vars encodedLengthVar =
      σ.vars encodedLengthVar + 1 := by
  simp [appendScratchState, Env.setVar]

theorem appendScratchState_prefix (σ : Env) (value : ℕ)
    (written : List ℕ)
    (hindex : σ.vars encodedLengthVar = written.length)
    (hprefix : (σ.arrs scratchName).take written.length = written)
    (hroom : written.length < (σ.arrs scratchName).length) :
    ((appendScratchState σ value).arrs scratchName).take
        (written ++ [value]).length = written ++ [value] := by
  simp only [appendScratchState, Env.setVar, Env.setArr, if_pos]
  rw [hindex]
  have h := take_set_top (σ.arrs scratchName) written.reverse value
    (by simpa using hprefix) (by simpa using hroom)
  simpa using h

theorem appendScratchState_arrs_of_ne (σ : Env) (value : ℕ)
    (name : String) (hne : name ≠ scratchName) :
    (appendScratchState σ value).arrs name = σ.arrs name := by
  simp [appendScratchState, Env.setArr, hne]

theorem appendScratchState_inp (σ : Env) (value : ℕ) :
    (appendScratchState σ value).inp = σ.inp := rfl

theorem appendScratchState_out (σ : Env) (value : ℕ) :
    (appendScratchState σ value).out = σ.out := rfl

def binaryDigitCode (zeroCode oneCode : ℕ) (n : ℕ) : ℕ :=
  if n % 2 = 0 then zeroCode else oneCode

def encodeBitsBody (zeroCode oneCode : ℕ) : Com :=
  seqs [
    .assign inputHalfVar (.div (.var inputValueVar) (.lit 2)),
    .assign inputBitVar
      (.sub (.var inputValueVar) (.mul (.var inputHalfVar) (.lit 2))),
    .ite (.eq (.var inputBitVar) (.lit 0))
      (appendScratch (.lit zeroCode))
      (appendScratch (.lit oneCode)),
    .assign inputValueVar (.var inputHalfVar)]

def encodeBitsLoop (zeroCode oneCode : ℕ) : Com :=
  .while (.lt (.lit 0) (.var inputValueVar))
    (encodeBitsBody zeroCode oneCode)

def encodeBitsBodyState (zeroCode oneCode : ℕ) (σ : Env) : Env :=
  let n := σ.vars inputValueVar
  let half := n / 2
  let bit := n - half * 2
  let σ₁ := σ.setVar inputHalfVar half
  let σ₂ := σ₁.setVar inputBitVar bit
  let σ₃ := appendScratchState σ₂ (binaryDigitCode zeroCode oneCode n)
  σ₃.setVar inputValueVar half

theorem sub_div_mul_two (n : ℕ) : n - n / 2 * 2 = n % 2 := by
  omega

theorem encodeBitsBody_correct (zeroCode oneCode : ℕ) (σ : Env)
    (hpositive : 0 < σ.vars inputValueVar)
    (hroom : σ.vars encodedLengthVar < (σ.arrs scratchName).length) :
    BigStep (encodeBitsBody zeroCode oneCode) σ
      (encodeBitsBodyState zeroCode oneCode σ) 25 := by
  let n := σ.vars inputValueVar
  let half := n / 2
  let bit := n - half * 2
  let σ₁ := σ.setVar inputHalfVar half
  let σ₂ := σ₁.setVar inputBitVar bit
  let digit := binaryDigitCode zeroCode oneCode n
  let σ₃ := appendScratchState σ₂ digit
  let σ₄ := σ₃.setVar inputValueVar half
  have hbitmod : bit = n % 2 := by
    simp [bit, half, sub_div_mul_two]
  have hhalf : BigStep
      (.assign inputHalfVar (.div (.var inputValueVar) (.lit 2))) σ σ₁ 4 := by
    apply BigStep.assign
    simp [Expr.eval, σ₁, half, n]
  have hbit : BigStep
      (.assign inputBitVar
        (.sub (.var inputValueVar) (.mul (.var inputHalfVar) (.lit 2))))
      σ₁ σ₂ 6 := by
    apply BigStep.assign
    simp [Expr.eval, σ₁, σ₂, bit, half, n, inputValueVar,
      inputHalfVar, inputBitVar]
  have hroom₂ : σ₂.vars encodedLengthVar < (σ₂.arrs scratchName).length := by
    simpa [σ₂, σ₁, Env.setVar] using hroom
  have happendZero : BigStep (appendScratch (.lit zeroCode)) σ₂
      (appendScratchState σ₂ zeroCode) 8 := by
    simpa using appendScratch_correct σ₂ (.lit zeroCode) zeroCode rfl hroom₂
  have happendOne : BigStep (appendScratch (.lit oneCode)) σ₂
      (appendScratchState σ₂ oneCode) 8 := by
    simpa using appendScratch_correct σ₂ (.lit oneCode) oneCode rfl hroom₂
  have hchoice : BigStep
      (.ite (.eq (.var inputBitVar) (.lit 0))
        (appendScratch (.lit zeroCode)) (appendScratch (.lit oneCode)))
      σ₂ σ₃ 12 := by
    by_cases hz : n % 2 = 0
    · have hσ₃ : σ₃ = appendScratchState σ₂ zeroCode := by
        simp [σ₃, digit, binaryDigitCode, hz]
      rw [hσ₃]
      simpa [Cond.size, Expr.size] using BigStep.ite_true
        (b := .eq (.var inputBitVar) (.lit 0))
        (d := appendScratch (.lit oneCode))
        (by simp [Cond.eval, Expr.eval, σ₂, hbitmod, hz,
          inputBitVar, inputHalfVar]) happendZero
    · have hσ₃ : σ₃ = appendScratchState σ₂ oneCode := by
        simp [σ₃, digit, binaryDigitCode, hz]
      rw [hσ₃]
      simpa [Cond.size, Expr.size] using BigStep.ite_false
        (b := .eq (.var inputBitVar) (.lit 0))
        (c := appendScratch (.lit zeroCode))
        (by simp [Cond.eval, Expr.eval, σ₂, hbitmod, hz,
          inputBitVar, inputHalfVar]) happendOne
  have hvalue : BigStep (.assign inputValueVar (.var inputHalfVar)) σ₃ σ₄ 2 := by
    apply BigStep.assign
    simp [Expr.eval, σ₄, σ₃, σ₂, σ₁, half, appendScratchState,
      inputValueVar, inputHalfVar, inputBitVar, encodedLengthVar]
  have hrun := BigStep.seq hhalf
    (BigStep.seq hbit (BigStep.seq hchoice
      (BigStep.seq hvalue (BigStep.skip (σ := σ₄)))))
  simpa [encodeBitsBody, encodeBitsBodyState, seqs, n, half, bit, digit,
    σ₁, σ₂, σ₃, σ₄, Nat.add_assoc] using hrun

theorem encodeBitsBodyState_value (zeroCode oneCode : ℕ) (σ : Env) :
    (encodeBitsBodyState zeroCode oneCode σ).vars inputValueVar =
      σ.vars inputValueVar / 2 := by
  simp [encodeBitsBodyState, Env.setVar]

theorem encodeBitsBodyState_encodedLength (zeroCode oneCode : ℕ) (σ : Env) :
    (encodeBitsBodyState zeroCode oneCode σ).vars encodedLengthVar =
      σ.vars encodedLengthVar + 1 := by
  simp [encodeBitsBodyState, appendScratchState, Env.setVar, encodedLengthVar,
    inputValueVar, inputHalfVar, inputBitVar]

theorem encodeBitsBodyState_prefix (zeroCode oneCode : ℕ) (σ : Env)
    (written : List ℕ)
    (hindex : σ.vars encodedLengthVar = written.length)
    (hprefix : (σ.arrs scratchName).take written.length = written)
    (hroom : written.length < (σ.arrs scratchName).length) :
    ((encodeBitsBodyState zeroCode oneCode σ).arrs scratchName).take
        (written ++ [binaryDigitCode zeroCode oneCode
          (σ.vars inputValueVar)]).length =
      written ++ [binaryDigitCode zeroCode oneCode (σ.vars inputValueVar)] := by
  apply appendScratchState_prefix
  · simpa [encodeBitsBodyState, Env.setVar, encodedLengthVar, inputValueVar,
      inputHalfVar, inputBitVar] using hindex
  · simpa [encodeBitsBodyState, Env.setVar] using hprefix
  · simpa [encodeBitsBodyState, Env.setVar] using hroom

def boolDigitCode (zeroCode oneCode : ℕ) (b : Bool) : ℕ :=
  if b then oneCode else zeroCode

theorem binaryDigitCode_eq_bodd (zeroCode oneCode n : ℕ) :
    binaryDigitCode zeroCode oneCode n =
      boolDigitCode zeroCode oneCode n.bodd := by
  rw [binaryDigitCode, boolDigitCode, Nat.mod_two_of_bodd]
  cases n.bodd <;> simp

theorem bits_eq_bodd_cons_div2 {n : ℕ} (hn : 0 < n) :
    n.bits = n.bodd :: (n / 2).bits := by
  induction n using Nat.binaryRec' with
  | zero => omega
  | bit b m h => simp [Nat.bits_append_bit m b h]

theorem encodeBitsBodyState_scratch_length (zeroCode oneCode : ℕ) (σ : Env) :
    ((encodeBitsBodyState zeroCode oneCode σ).arrs scratchName).length =
      (σ.arrs scratchName).length := by
  simp [encodeBitsBodyState, appendScratchState, Env.setArr]

/-- The inner input-codec loop emits precisely the canonical least-significant
bit-first representation of its initial natural number. -/
theorem encodeBitsLoop_correct (zeroCode oneCode : ℕ) (σ : Env)
    (written : List ℕ)
    (hindex : σ.vars encodedLengthVar = written.length)
    (hprefix : (σ.arrs scratchName).take written.length = written)
    (hspace : written.length + (σ.vars inputValueVar).bits.length ≤
      (σ.arrs scratchName).length) :
    ∃ σ' cost,
      BigStep (encodeBitsLoop zeroCode oneCode) σ σ' cost ∧
      cost = 29 * (σ.vars inputValueVar).bits.length + 4 ∧
      σ'.vars inputValueVar = 0 ∧
      σ'.vars encodedLengthVar =
        written.length + (σ.vars inputValueVar).bits.length ∧
      (σ'.arrs scratchName).take
          (written ++ (σ.vars inputValueVar).bits.map
            (boolDigitCode zeroCode oneCode)).length =
        written ++ (σ.vars inputValueVar).bits.map
          (boolDigitCode zeroCode oneCode) := by
  generalize hval : σ.vars inputValueVar = n
  induction n using Nat.strong_induction_on generalizing σ written with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        have hvalue : σ.vars inputValueVar = 0 := by assumption
        refine ⟨σ, 4, ?_, ?_, hvalue, ?_, ?_⟩
        · unfold encodeBitsLoop
          exact BigStep.while_false (by simp [Cond.eval, Expr.eval, hvalue])
        · simp [hvalue]
        · simpa [hvalue] using hindex
        · simpa [hvalue] using hprefix
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hvalue : σ.vars inputValueVar = n := hval
        rw [hvalue] at hspace
        have hroom : σ.vars encodedLengthVar < (σ.arrs scratchName).length := by
          rw [hindex]
          have hbits : 0 < n.bits.length := by
            rw [bits_eq_bodd_cons_div2 hnpos]
            simp
          omega
        let τ := encodeBitsBodyState zeroCode oneCode σ
        have hbody := encodeBitsBody_correct zeroCode oneCode σ
          (by simpa [hvalue] using hnpos) hroom
        let digit := binaryDigitCode zeroCode oneCode n
        let written' := written ++ [digit]
        have hτvalue : τ.vars inputValueVar = n / 2 := by
          simpa [τ, hvalue] using encodeBitsBodyState_value zeroCode oneCode σ
        have hτindex : τ.vars encodedLengthVar = written'.length := by
          rw [encodeBitsBodyState_encodedLength]
          simp [written', hindex]
        have hτprefix : (τ.arrs scratchName).take written'.length = written' := by
          simpa [τ, written', digit, hvalue] using
            encodeBitsBodyState_prefix zeroCode oneCode σ written hindex hprefix
              (by simpa [hindex] using hroom)
        have hbits := bits_eq_bodd_cons_div2 hnpos
        have hτspace : written'.length + (τ.vars inputValueVar).bits.length ≤
            (τ.arrs scratchName).length := by
          rw [hτvalue, encodeBitsBodyState_scratch_length]
          rw [hbits] at hspace
          simp only [List.length_cons] at hspace
          simp [written']
          omega
        have hdecrease : n / 2 < n := Nat.div_lt_self hnpos (by omega)
        obtain ⟨σ', tailCost, htail, htailCost, hfinalValue,
            hfinalLength, hfinalPrefix⟩ :=
          ih (n / 2) hdecrease τ written' hτindex hτprefix hτspace hτvalue
        refine ⟨σ', 29 + tailCost, ?_, ?_, hfinalValue, ?_, ?_⟩
        · unfold encodeBitsLoop at htail ⊢
          simpa [hvalue] using BigStep.while_true
            (b := .lt (.lit 0) (.var inputValueVar))
            (by simp [Cond.eval, Expr.eval, hvalue, hnpos]) hbody htail
        · rw [htailCost]
          rw [hbits]
          simp
          omega
        · rw [hfinalLength]
          rw [hbits]
          simp [written'] <;> omega
        · rw [hbits]
          simp only [List.map_cons]
          simpa [written', digit, binaryDigitCode_eq_bodd,
            List.append_assoc] using hfinalPrefix

def encodeNatCodes (separatorCode zeroCode oneCode n : ℕ) : List ℕ :=
  separatorCode :: n.bits.map (boolDigitCode zeroCode oneCode)

def encodeWordCodes (separatorCode zeroCode oneCode : ℕ)
    (x : List ℕ) : List ℕ :=
  x.flatMap (encodeNatCodes separatorCode zeroCode oneCode)

noncomputable def FinTM2.inputSymbolCode (tm : Turing.FinTM2)
    (inputAlphabet : tm.Γ tm.k₀ ≃ Lax20.BinaryWordEncoding.Symbol)
    (a : Lax20.BinaryWordEncoding.Symbol) : ℕ :=
  FinTM2.codeSymbol tm (inputAlphabet.invFun a) (by
    apply Set.mem_union_left
    exact ⟨inputAlphabet.invFun a, rfl⟩)

theorem FinTM2.codeStack_map_inputAlphabet (tm : Turing.FinTM2)
    (inputAlphabet : tm.Γ tm.k₀ ≃ Lax20.BinaryWordEncoding.Symbol)
    (word : List Lax20.BinaryWordEncoding.Symbol)
    (hword : ∀ a ∈ word.map inputAlphabet.invFun,
      (⟨tm.k₀, a⟩ : Σ k, tm.Γ k) ∈ FinTM2.availableSymbols tm) :
    FinTM2.codeStack tm tm.k₀ (word.map inputAlphabet.invFun) hword =
      word.map (FinTM2.inputSymbolCode tm inputAlphabet) := by
  induction word with
  | nil => simp
  | cons a word ih =>
      change FinTM2.codeStack tm tm.k₀
          (inputAlphabet.invFun a :: word.map inputAlphabet.invFun) _ = _
      rw [FinTM2.codeStack_cons]
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · rfl
      · exact ih (fun b hb => hword b (by
          change b ∈ inputAlphabet.invFun a :: word.map inputAlphabet.invFun
          exact List.mem_cons_of_mem _ hb))

theorem encodeNatCodes_eq_inputSymbolCodes (tm : Turing.FinTM2)
    (inputAlphabet : tm.Γ tm.k₀ ≃ Lax20.BinaryWordEncoding.Symbol)
    (n : ℕ) :
    encodeNatCodes
        (FinTM2.inputSymbolCode tm inputAlphabet .separator)
        (FinTM2.inputSymbolCode tm inputAlphabet .zero)
        (FinTM2.inputSymbolCode tm inputAlphabet .one) n =
      (Lax20.BinaryWordEncoding.encodeNat n).map
        (FinTM2.inputSymbolCode tm inputAlphabet) := by
  simp [encodeNatCodes, Lax20.BinaryWordEncoding.encodeNat,
    boolDigitCode]

theorem encodeWordCodes_eq_inputSymbolCodes (tm : Turing.FinTM2)
    (inputAlphabet : tm.Γ tm.k₀ ≃ Lax20.BinaryWordEncoding.Symbol)
    (x : List ℕ) :
    encodeWordCodes
        (FinTM2.inputSymbolCode tm inputAlphabet .separator)
        (FinTM2.inputSymbolCode tm inputAlphabet .zero)
        (FinTM2.inputSymbolCode tm inputAlphabet .one) x =
      (Lax20.BinaryWordEncoding.encode x).map
        (FinTM2.inputSymbolCode tm inputAlphabet) := by
  induction x with
  | nil => rfl
  | cons a x ih =>
      rw [show encodeWordCodes
          (FinTM2.inputSymbolCode tm inputAlphabet .separator)
          (FinTM2.inputSymbolCode tm inputAlphabet .zero)
          (FinTM2.inputSymbolCode tm inputAlphabet .one) (a :: x) =
          encodeNatCodes
            (FinTM2.inputSymbolCode tm inputAlphabet .separator)
            (FinTM2.inputSymbolCode tm inputAlphabet .zero)
            (FinTM2.inputSymbolCode tm inputAlphabet .one) a ++
          encodeWordCodes
            (FinTM2.inputSymbolCode tm inputAlphabet .separator)
            (FinTM2.inputSymbolCode tm inputAlphabet .zero)
            (FinTM2.inputSymbolCode tm inputAlphabet .one) x by
        simp [encodeWordCodes]]
      rw [encodeNatCodes_eq_inputSymbolCodes, ih]
      simp [Lax20.BinaryWordEncoding.encode]

/-- A total code for an arbitrary typed stack symbol.  Symbols in the
reachable finite alphabet receive their actual interpreter code; other
symbols receive the out-of-range sentinel `card`.  This lets the native
output decoder contain constants for all three external alphabet symbols
even when one of them never occurs in any execution of the particular
machine. -/
noncomputable def FinTM2.symbolCodeD (tm : Turing.FinTM2) (k : tm.K)
    (a : tm.Γ k) : ℕ := by
  classical
  exact if ha : (⟨k, a⟩ : Σ k, tm.Γ k) ∈ FinTM2.availableSymbols tm then
    FinTM2.codeSymbol tm a ha
  else Fintype.card (FinTM2.AvailableAt tm k)

theorem FinTM2.symbolCodeD_eq_codeSymbol (tm : Turing.FinTM2) (k : tm.K)
    (a : tm.Γ k)
    (ha : (⟨k, a⟩ : Σ k, tm.Γ k) ∈ FinTM2.availableSymbols tm) :
    FinTM2.symbolCodeD tm k a = FinTM2.codeSymbol tm a ha := by
  classical
  simp [FinTM2.symbolCodeD, ha]

noncomputable def FinTM2.outputSymbolCode (tm : Turing.FinTM2)
    (outputAlphabet : tm.Γ tm.k₁ ≃ Lax20.BinaryWordEncoding.Symbol)
    (a : Lax20.BinaryWordEncoding.Symbol) : ℕ := by
  classical
  exact if ha : (⟨tm.k₁, outputAlphabet.invFun a⟩ : Σ k, tm.Γ k) ∈
      FinTM2.availableSymbols tm then
    FinTM2.codeSymbol tm (outputAlphabet.invFun a) ha
  else Fintype.card (FinTM2.AvailableAt tm tm.k₁) + finCode a

theorem FinTM2.outputSymbolCode_eq_codeSymbol (tm : Turing.FinTM2)
    (outputAlphabet : tm.Γ tm.k₁ ≃ Lax20.BinaryWordEncoding.Symbol)
    (a : Lax20.BinaryWordEncoding.Symbol)
    (ha : (⟨tm.k₁, outputAlphabet.invFun a⟩ : Σ k, tm.Γ k) ∈
      FinTM2.availableSymbols tm) :
    FinTM2.outputSymbolCode tm outputAlphabet a =
      FinTM2.codeSymbol tm (outputAlphabet.invFun a) ha := by
  classical
  unfold FinTM2.outputSymbolCode
  rw [dif_pos ha]

theorem FinTM2.outputSymbolCode_injective (tm : Turing.FinTM2)
    (outputAlphabet : tm.Γ tm.k₁ ≃ Lax20.BinaryWordEncoding.Symbol) :
    Function.Injective (FinTM2.outputSymbolCode tm outputAlphabet) := by
  classical
  letI := FinTM2.AvailableAt.instFintype tm tm.k₁
  letI := FinTM2.AvailableAt.instDecidableEq tm tm.k₁
  intro a b hab
  by_cases ha : (⟨tm.k₁, outputAlphabet.invFun a⟩ : Σ k, tm.Γ k) ∈
      FinTM2.availableSymbols tm
  · by_cases hb : (⟨tm.k₁, outputAlphabet.invFun b⟩ : Σ k, tm.Γ k) ∈
        FinTM2.availableSymbols tm
    · rw [FinTM2.outputSymbolCode_eq_codeSymbol tm outputAlphabet a ha,
          FinTM2.outputSymbolCode_eq_codeSymbol tm outputAlphabet b hb] at hab
      have hsub : (⟨outputAlphabet.invFun a, ha⟩ :
          FinTM2.AvailableAt tm tm.k₁) = ⟨outputAlphabet.invFun b, hb⟩ := by
        apply @finCode_injective (FinTM2.AvailableAt tm tm.k₁)
          (FinTM2.AvailableAt.instFintype tm tm.k₁)
          (FinTM2.AvailableAt.instDecidableEq tm tm.k₁)
        exact hab
      exact outputAlphabet.symm.injective (congrArg Subtype.val hsub)
    · have hlt := @finCode_lt (FinTM2.AvailableAt tm tm.k₁)
          (FinTM2.AvailableAt.instFintype tm tm.k₁)
          (FinTM2.AvailableAt.instDecidableEq tm tm.k₁)
          (⟨outputAlphabet.invFun a, ha⟩ : FinTM2.AvailableAt tm tm.k₁)
      have hdefault : FinTM2.outputSymbolCode tm outputAlphabet b =
          Fintype.card (FinTM2.AvailableAt tm tm.k₁) + finCode b := by
        unfold FinTM2.outputSymbolCode
        rw [dif_neg hb]
      have heq : FinTM2.codeSymbol tm (outputAlphabet.invFun a) ha =
          Fintype.card (FinTM2.AvailableAt tm tm.k₁) + finCode b := calc
        _ = FinTM2.outputSymbolCode tm outputAlphabet a :=
          (FinTM2.outputSymbolCode_eq_codeSymbol tm outputAlphabet a ha).symm
        _ = FinTM2.outputSymbolCode tm outputAlphabet b := hab
        _ = _ := hdefault
      change @finCode (FinTM2.AvailableAt tm tm.k₁)
        (FinTM2.AvailableAt.instFintype tm tm.k₁)
        (FinTM2.AvailableAt.instDecidableEq tm tm.k₁)
        ⟨outputAlphabet.invFun a, ha⟩ = _ at heq
      omega
  · by_cases hb : (⟨tm.k₁, outputAlphabet.invFun b⟩ : Σ k, tm.Γ k) ∈
        FinTM2.availableSymbols tm
    · have hlt := @finCode_lt (FinTM2.AvailableAt tm tm.k₁)
          (FinTM2.AvailableAt.instFintype tm tm.k₁)
          (FinTM2.AvailableAt.instDecidableEq tm tm.k₁)
          (⟨outputAlphabet.invFun b, hb⟩ : FinTM2.AvailableAt tm tm.k₁)
      have hdefault : FinTM2.outputSymbolCode tm outputAlphabet a =
          Fintype.card (FinTM2.AvailableAt tm tm.k₁) + finCode a := by
        unfold FinTM2.outputSymbolCode
        rw [dif_neg ha]
      have heq : FinTM2.codeSymbol tm (outputAlphabet.invFun b) hb =
          Fintype.card (FinTM2.AvailableAt tm tm.k₁) + finCode a := calc
        _ = FinTM2.outputSymbolCode tm outputAlphabet b :=
          (FinTM2.outputSymbolCode_eq_codeSymbol tm outputAlphabet b hb).symm
        _ = FinTM2.outputSymbolCode tm outputAlphabet a := hab.symm
        _ = _ := hdefault
      change @finCode (FinTM2.AvailableAt tm tm.k₁)
        (FinTM2.AvailableAt.instFintype tm tm.k₁)
        (FinTM2.AvailableAt.instDecidableEq tm tm.k₁)
        ⟨outputAlphabet.invFun b, hb⟩ = _ at heq
      omega
    · have hdefaultA : FinTM2.outputSymbolCode tm outputAlphabet a =
          Fintype.card (FinTM2.AvailableAt tm tm.k₁) + finCode a := by
        unfold FinTM2.outputSymbolCode
        rw [dif_neg ha]
      have hdefaultB : FinTM2.outputSymbolCode tm outputAlphabet b =
          Fintype.card (FinTM2.AvailableAt tm tm.k₁) + finCode b := by
        unfold FinTM2.outputSymbolCode
        rw [dif_neg hb]
      rw [hdefaultA, hdefaultB, Nat.add_left_cancel_iff] at hab
      exact finCode_injective hab

theorem FinTM2.codeStack_map_outputAlphabet (tm : Turing.FinTM2)
    (outputAlphabet : tm.Γ tm.k₁ ≃ Lax20.BinaryWordEncoding.Symbol)
    (word : List Lax20.BinaryWordEncoding.Symbol)
    (hword : ∀ a ∈ word.map outputAlphabet.invFun,
      (⟨tm.k₁, a⟩ : Σ k, tm.Γ k) ∈ FinTM2.availableSymbols tm) :
    FinTM2.codeStack tm tm.k₁ (word.map outputAlphabet.invFun) hword =
      word.map (fun a => FinTM2.outputSymbolCode tm outputAlphabet a) := by
  induction word with
  | nil => simp
  | cons a word ih =>
      change FinTM2.codeStack tm tm.k₁
          (outputAlphabet.invFun a :: word.map outputAlphabet.invFun) _ = _
      rw [FinTM2.codeStack_cons]
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · symm
        exact FinTM2.outputSymbolCode_eq_codeSymbol tm outputAlphabet a _
      · exact ih (fun b hb => hword b (by
          change b ∈ outputAlphabet.invFun a :: word.map outputAlphabet.invFun
          exact List.mem_cons_of_mem _ hb))

theorem encodeNatCodes_eq_outputSymbolCodes (tm : Turing.FinTM2)
    (outputAlphabet : tm.Γ tm.k₁ ≃ Lax20.BinaryWordEncoding.Symbol)
    (n : ℕ) :
    encodeNatCodes
        (FinTM2.outputSymbolCode tm outputAlphabet .separator)
        (FinTM2.outputSymbolCode tm outputAlphabet .zero)
        (FinTM2.outputSymbolCode tm outputAlphabet .one) n =
      (Lax20.BinaryWordEncoding.encodeNat n).map
        (FinTM2.outputSymbolCode tm outputAlphabet) := by
  simp [encodeNatCodes, Lax20.BinaryWordEncoding.encodeNat,
    boolDigitCode]

theorem encodeWordCodes_eq_outputSymbolCodes (tm : Turing.FinTM2)
    (outputAlphabet : tm.Γ tm.k₁ ≃ Lax20.BinaryWordEncoding.Symbol)
    (x : List ℕ) :
    encodeWordCodes
        (FinTM2.outputSymbolCode tm outputAlphabet .separator)
        (FinTM2.outputSymbolCode tm outputAlphabet .zero)
        (FinTM2.outputSymbolCode tm outputAlphabet .one) x =
      (Lax20.BinaryWordEncoding.encode x).map
        (FinTM2.outputSymbolCode tm outputAlphabet) := by
  induction x with
  | nil => rfl
  | cons a x ih =>
      rw [show encodeWordCodes
          (FinTM2.outputSymbolCode tm outputAlphabet .separator)
          (FinTM2.outputSymbolCode tm outputAlphabet .zero)
          (FinTM2.outputSymbolCode tm outputAlphabet .one) (a :: x) =
          encodeNatCodes
            (FinTM2.outputSymbolCode tm outputAlphabet .separator)
            (FinTM2.outputSymbolCode tm outputAlphabet .zero)
            (FinTM2.outputSymbolCode tm outputAlphabet .one) a ++
          encodeWordCodes
            (FinTM2.outputSymbolCode tm outputAlphabet .separator)
            (FinTM2.outputSymbolCode tm outputAlphabet .zero)
            (FinTM2.outputSymbolCode tm outputAlphabet .one) x by
        simp [encodeWordCodes]]
      rw [encodeNatCodes_eq_outputSymbolCodes, ih]
      simp [Lax20.BinaryWordEncoding.encode]

def encodeInputBody (separatorCode zeroCode oneCode : ℕ) : Com :=
  seqs [
    .read inputValueVar,
    appendScratch (.lit separatorCode),
    encodeBitsLoop zeroCode oneCode,
    .assign inputCountVar (.sub (.var inputCountVar) (.lit 1))]

def encodeInputLoop (separatorCode zeroCode oneCode : ℕ) : Com :=
  .while (.lt (.lit 0) (.var inputCountVar))
    (encodeInputBody separatorCode zeroCode oneCode)

def encodeInputLoopCost : List ℕ → ℕ
  | [] => 4
  | a :: x => 4 + (29 * a.bits.length + 18) + encodeInputLoopCost x

/-- Encoding the native input tape costs linearly many IMP+ steps in the
canonical bit-size. -/
theorem encodeInputLoopCost_le (x : List ℕ) :
    encodeInputLoopCost x ≤ 51 * Lax20.BinaryWordEncoding.bitSize x + 4 := by
  induction x with
  | nil => simp [encodeInputLoopCost, Lax20.BinaryWordEncoding.bitSize]
  | cons a x ih =>
      rw [encodeInputLoopCost]
      rw [Lax20Proofs.Encoding.bitSize_cons]
      have hlen := Lax20Proofs.Encoding.length_le_bitSize x
      omega

theorem encodeInputBody_correct (separatorCode zeroCode oneCode : ℕ)
    (σ : Env) (a : ℕ) (rest written : List ℕ)
    (hinp : σ.inp = a :: rest)
    (hcount : 0 < σ.vars inputCountVar)
    (hindex : σ.vars encodedLengthVar = written.length)
    (hprefix : (σ.arrs scratchName).take written.length = written)
    (hspace : written.length + (encodeNatCodes separatorCode zeroCode oneCode a).length ≤
      (σ.arrs scratchName).length) :
    ∃ σ' cost,
      BigStep (encodeInputBody separatorCode zeroCode oneCode) σ σ' cost ∧
      cost = 29 * a.bits.length + 18 ∧
      σ'.inp = rest ∧
      σ'.vars inputCountVar = σ.vars inputCountVar - 1 ∧
      σ'.vars encodedLengthVar =
        written.length + (encodeNatCodes separatorCode zeroCode oneCode a).length ∧
      (σ'.arrs scratchName).take
          (written ++ encodeNatCodes separatorCode zeroCode oneCode a).length =
        written ++ encodeNatCodes separatorCode zeroCode oneCode a := by
  let σ₁ := { σ.setVar inputValueVar a with inp := rest }
  have hread : BigStep (.read inputValueVar) σ σ₁ 1 := by
    exact BigStep.read hinp
  let σ₂ := appendScratchState σ₁ separatorCode
  have hindex₁ : σ₁.vars encodedLengthVar = written.length := by
    simpa [σ₁, Env.setVar, encodedLengthVar, inputValueVar] using hindex
  have hroom : σ₁.vars encodedLengthVar < (σ₁.arrs scratchName).length := by
    have hlen : 0 < (encodeNatCodes separatorCode zeroCode oneCode a).length := by
      simp [encodeNatCodes]
    rw [hindex₁]
    simpa [σ₁] using (show written.length < (σ.arrs scratchName).length by omega)
  have happend : BigStep (appendScratch (.lit separatorCode)) σ₁ σ₂ 8 := by
    simpa [σ₂] using appendScratch_correct σ₁ (.lit separatorCode)
      separatorCode rfl hroom
  let written₂ := written ++ [separatorCode]
  have hindex₂ : σ₂.vars encodedLengthVar = written₂.length := by
    rw [appendScratchState_length, hindex₁]
    simp [written₂]
  have hprefix₂ : (σ₂.arrs scratchName).take written₂.length = written₂ := by
    simpa [σ₂, σ₁, written₂, Env.setVar, encodedLengthVar, inputValueVar] using
      appendScratchState_prefix σ₁ separatorCode written
        hindex₁
        (by simpa [σ₁] using hprefix)
        (by simpa [σ₁, hindex] using hroom)
  have hspace₂ : written₂.length + (σ₂.vars inputValueVar).bits.length ≤
      (σ₂.arrs scratchName).length := by
    have hv : σ₂.vars inputValueVar = a := by
      simp [σ₂, appendScratchState, σ₁, Env.setVar, inputValueVar,
        inputBitVar, inputHalfVar, encodedLengthVar]
    have harr : (σ₂.arrs scratchName).length = (σ.arrs scratchName).length := by
      simp [σ₂, appendScratchState, σ₁, Env.setArr]
    rw [hv, harr]
    simp [written₂, encodeNatCodes] at hspace ⊢
    omega
  obtain ⟨σ₃, bitsCost, hbitsRun, hbitsCost, hbitsValue,
      hbitsLength, hbitsPrefix⟩ :=
    encodeBitsLoop_correct zeroCode oneCode σ₂ written₂
      hindex₂ hprefix₂ hspace₂
  have hcount₃ : σ₃.vars inputCountVar = σ.vars inputCountVar := by
    rw [hbitsRun.vars_eq]
    · simp [σ₂, appendScratchState, σ₁, Env.setVar, inputCountVar,
        inputValueVar, inputBitVar, inputHalfVar, encodedLengthVar]
    · simp [encodeBitsLoop, encodeBitsBody, appendScratch, seqs, Com.wvars,
        inputCountVar, inputValueVar, inputBitVar, inputHalfVar,
        encodedLengthVar]
  have hinp₃ : σ₃.inp = rest := by
    rw [hbitsRun.inp_eq]
    · rfl
    · simp [encodeBitsLoop, encodeBitsBody, appendScratch, seqs, Com.reads]
  let σ₄ := σ₃.setVar inputCountVar (σ.vars inputCountVar - 1)
  have hdecrement : BigStep
      (.assign inputCountVar (.sub (.var inputCountVar) (.lit 1))) σ₃ σ₄ 4 := by
    apply BigStep.assign
    simp [Expr.eval, σ₄, hcount₃]
  have hrun := BigStep.seq hread (BigStep.seq happend
    (BigStep.seq hbitsRun (BigStep.seq hdecrement (BigStep.skip (σ := σ₄)))))
  refine ⟨σ₄, 1 + 8 + bitsCost + 4 + 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert hrun using 1 <;> simp [encodeInputBody, seqs] <;> omega
  · rw [hbitsCost]
    have hv : σ₂.vars inputValueVar = a := by
      simp [σ₂, appendScratchState, σ₁, Env.setVar, inputValueVar,
        inputBitVar, inputHalfVar, encodedLengthVar]
    rw [hv]
    omega
  · simpa [σ₄] using hinp₃
  · simp [σ₄, Env.setVar]
  · have hv : σ₂.vars inputValueVar = a := by
      simp [σ₂, appendScratchState, σ₁, Env.setVar, inputValueVar,
        inputBitVar, inputHalfVar, encodedLengthVar]
    rw [show σ₄.vars encodedLengthVar = σ₃.vars encodedLengthVar by
      simp [σ₄, Env.setVar, encodedLengthVar, inputCountVar]]
    rw [hbitsLength, hv]
    simp [encodeNatCodes, written₂]
    omega
  · have hv : σ₂.vars inputValueVar = a := by
      simp [σ₂, appendScratchState, σ₁, Env.setVar, inputValueVar,
        inputBitVar, inputHalfVar, encodedLengthVar]
    change (σ₃.arrs scratchName).take
        (written ++ encodeNatCodes separatorCode zeroCode oneCode a).length = _
    rw [hv] at hbitsPrefix
    simpa [encodeNatCodes, written₂, List.append_assoc] using hbitsPrefix

/-- The length-counted outer loop consumes exactly the native word and emits
the concatenation of the canonical encodings of its entries. -/
theorem encodeInputLoop_correct (separatorCode zeroCode oneCode : ℕ)
    (σ : Env) (remaining written : List ℕ)
    (hinp : σ.inp = remaining)
    (hcount : σ.vars inputCountVar = remaining.length)
    (hindex : σ.vars encodedLengthVar = written.length)
    (hprefix : (σ.arrs scratchName).take written.length = written)
    (hspace : written.length +
        (encodeWordCodes separatorCode zeroCode oneCode remaining).length ≤
      (σ.arrs scratchName).length) :
    ∃ σ' cost,
      BigStep (encodeInputLoop separatorCode zeroCode oneCode) σ σ' cost ∧
      cost = encodeInputLoopCost remaining ∧
      σ'.inp = [] ∧ σ'.vars inputCountVar = 0 ∧
      σ'.vars encodedLengthVar = written.length +
        (encodeWordCodes separatorCode zeroCode oneCode remaining).length ∧
      (σ'.arrs scratchName).take
          (written ++ encodeWordCodes separatorCode zeroCode oneCode remaining).length =
        written ++ encodeWordCodes separatorCode zeroCode oneCode remaining := by
  induction remaining generalizing σ written with
  | nil =>
      have hzero : σ.vars inputCountVar = 0 := by simpa using hcount
      refine ⟨σ, 4, ?_, rfl, by simpa using hinp, hzero, ?_, ?_⟩
      · unfold encodeInputLoop
        exact BigStep.while_false (by simp [Cond.eval, Expr.eval, hzero])
      · simpa [encodeWordCodes] using hindex
      · simpa [encodeWordCodes] using hprefix
  | cons a remaining ih =>
      have hpositive : 0 < σ.vars inputCountVar := by simp [hcount]
      have hheadSpace : written.length +
          (encodeNatCodes separatorCode zeroCode oneCode a).length ≤
          (σ.arrs scratchName).length := by
        simp [encodeWordCodes, List.length_append] at hspace
        omega
      obtain ⟨τ, bodyCost, hbody, hbodyCost, hτinp, hτcount,
          hτlength, hτprefix⟩ :=
        encodeInputBody_correct separatorCode zeroCode oneCode σ a remaining written
          (by simpa using hinp) hpositive hindex hprefix hheadSpace
      let written' := written ++ encodeNatCodes separatorCode zeroCode oneCode a
      have hτcount' : τ.vars inputCountVar = remaining.length := by
        rw [hτcount, hcount]
        simp
      have hτlength' : τ.vars encodedLengthVar = written'.length := by
        simpa [written', List.length_append] using hτlength
      have hτprefix' : (τ.arrs scratchName).take written'.length = written' := by
        simpa [written'] using hτprefix
      have hτspace : written'.length +
          (encodeWordCodes separatorCode zeroCode oneCode remaining).length ≤
          (τ.arrs scratchName).length := by
        rw [BigStep.arr_length_eq hbody scratchName]
        simpa [written', encodeWordCodes, List.length_append,
          Nat.add_assoc] using hspace
      obtain ⟨σ', tailCost, htail, htailCost, hfinalInp, hfinalCount,
          hfinalLength, hfinalPrefix⟩ :=
        ih τ written' hτinp hτcount' hτlength' hτprefix' hτspace
      refine ⟨σ', 4 + bodyCost + tailCost, ?_, ?_, hfinalInp,
        hfinalCount, ?_, ?_⟩
      · unfold encodeInputLoop at htail ⊢
        simpa using BigStep.while_true
          (b := .lt (.lit 0) (.var inputCountVar))
          (by simp [Cond.eval, Expr.eval, hpositive]) hbody htail
      · rw [hbodyCost, htailCost]
        rfl
      · rw [hfinalLength]
        simp [written', encodeWordCodes, List.length_append, Nat.add_assoc]
      · simpa [written', encodeWordCodes, List.append_assoc] using hfinalPrefix

/-- Read the length-prefixed native input and construct its canonical binary
symbol encoding in `scratchName`.  Remainders are derived using division,
multiplication and truncated subtraction, all available in IMP+. -/
def encodeNativeInputToScratch (separatorCode zeroCode oneCode : ℕ) : Com :=
  seqs [
    .read inputCountVar,
    .assign encodedLengthVar (.lit 0),
    encodeInputLoop separatorCode zeroCode oneCode]

theorem encodeNativeInputToScratch_correct (separatorCode zeroCode oneCode : ℕ)
    (σ : Env) (x : List ℕ)
    (hinp : σ.inp = x.length :: x)
    (hspace : (encodeWordCodes separatorCode zeroCode oneCode x).length ≤
      (σ.arrs scratchName).length) :
    ∃ σ' cost,
      BigStep (encodeNativeInputToScratch separatorCode zeroCode oneCode)
        σ σ' cost ∧
      cost = encodeInputLoopCost x + 4 ∧
      σ'.inp = [] ∧
      σ'.vars encodedLengthVar =
        (encodeWordCodes separatorCode zeroCode oneCode x).length ∧
      (σ'.arrs scratchName).take
          (encodeWordCodes separatorCode zeroCode oneCode x).length =
        encodeWordCodes separatorCode zeroCode oneCode x := by
  let σ₁ := { σ.setVar inputCountVar x.length with inp := x }
  have hread : BigStep (.read inputCountVar) σ σ₁ 1 := BigStep.read hinp
  let σ₂ := σ₁.setVar encodedLengthVar 0
  have hzero : BigStep (.assign encodedLengthVar (.lit 0)) σ₁ σ₂ 2 := by
    exact BigStep.assign rfl
  obtain ⟨σ', loopCost, hloop, hloopCost, hfinalInp, _hfinalCount,
      hfinalLength, hfinalPrefix⟩ :=
    encodeInputLoop_correct separatorCode zeroCode oneCode σ₂ x []
      (by rfl)
      (by simp [σ₂, σ₁, Env.setVar, inputCountVar, encodedLengthVar])
      (by simp [σ₂, Env.setVar]) (by simp)
      (by simpa [σ₂, σ₁] using hspace)
  have hrun := BigStep.seq hread
    (BigStep.seq hzero (BigStep.seq hloop (BigStep.skip (σ := σ'))))
  refine ⟨σ', 1 + 2 + loopCost + 1, ?_, ?_, hfinalInp, ?_, ?_⟩
  · convert hrun using 1 <;> simp [encodeNativeInputToScratch, seqs] <;> omega
  · rw [hloopCost]
    omega
  · simpa using hfinalLength
  · simpa using hfinalPrefix

/-- Reverse the forward scratch encoding into the array convention used by
`StackRep`, whose active prefix is the reverse of the logical TM stack. -/
def reverseScratchBody (stack : ℕ) : Com :=
  seqs [
    .assign copyIndexVar (.sub (.var copyIndexVar) (.lit 1)),
    .assign ioValueVar (.get scratchName (.var copyIndexVar)),
    .store (stackName stack) (.var (topName stack)) (.var ioValueVar),
    .assign (topName stack) (.add (.var (topName stack)) (.lit 1))]

def reverseScratchLoop (stack : ℕ) : Com :=
  .while (.lt (.lit 0) (.var copyIndexVar)) (reverseScratchBody stack)

def reverseScratchIntoStack (stack : ℕ) : Com :=
  seqs [
    .assign copyIndexVar (.var encodedLengthVar),
    .assign (topName stack) (.lit 0),
    reverseScratchLoop stack]

def reverseScratchBodyState (stack : ℕ) (σ : Env) : Env :=
  let i := σ.vars copyIndexVar - 1
  let v := (σ.arrs scratchName).getD i 0
  let σ₁ := σ.setVar copyIndexVar i
  let σ₂ := σ₁.setVar ioValueVar v
  let σ₃ := σ₂.setArr (stackName stack) (σ.vars (topName stack)) v
  σ₃.setVar (topName stack) (σ.vars (topName stack) + 1)

theorem reverseScratchBody_correct (stack : ℕ) (σ : Env)
    (hpositive : 0 < σ.vars copyIndexVar)
    (hscratch : σ.vars copyIndexVar ≤ (σ.arrs scratchName).length)
    (hstack : σ.vars (topName stack) < (σ.arrs (stackName stack)).length) :
    BigStep (reverseScratchBody stack) σ
      (reverseScratchBodyState stack σ) 15 := by
  let i := σ.vars copyIndexVar - 1
  have hi : i < (σ.arrs scratchName).length := by
    dsimp [i]
    omega
  let v := (σ.arrs scratchName).getD i 0
  have hget : (σ.arrs scratchName)[i]? = some v :=
    getElem?_eq_getD hi
  let σ₁ := σ.setVar copyIndexVar i
  let σ₂ := σ₁.setVar ioValueVar v
  let σ₃ := σ₂.setArr (stackName stack) (σ.vars (topName stack)) v
  let σ₄ := σ₃.setVar (topName stack) (σ.vars (topName stack) + 1)
  have hdec : BigStep
      (.assign copyIndexVar (.sub (.var copyIndexVar) (.lit 1))) σ σ₁ 4 := by
    apply BigStep.assign
    simp [Expr.eval, σ₁, i]
  have hload : BigStep
      (.assign ioValueVar (.get scratchName (.var copyIndexVar))) σ₁ σ₂ 3 := by
    apply BigStep.assign
    simp only [Expr.eval]
    simp [σ₁, copyIndexVar, ioValueVar, hget]
  have hstore : BigStep
      (.store (stackName stack) (.var (topName stack)) (.var ioValueVar))
      σ₂ σ₃ 3 := by
    apply BigStep.store
    · simp [σ₂, σ₁, topName_ne_copyIndexVar, topName_ne_ioValueVar]
    · simp [σ₂, Env.setVar]
    · simpa [σ₂, σ₁] using hstack
  have htop : BigStep
      (.assign (topName stack) (.add (.var (topName stack)) (.lit 1)))
      σ₃ σ₄ 4 := by
    apply BigStep.assign
    simp [Expr.eval, σ₃, σ₂, σ₁, topName_ne_copyIndexVar,
      topName_ne_ioValueVar]
  have hrun := BigStep.seq hdec (BigStep.seq hload
    (BigStep.seq hstore (BigStep.seq htop (BigStep.skip (σ := σ₄)))))
  simpa [reverseScratchBody, reverseScratchBodyState, seqs, i, v,
    σ₁, σ₂, σ₃, σ₄, Nat.add_assoc] using hrun

theorem reverseScratchBodyState_index (stack : ℕ) (σ : Env) :
    (reverseScratchBodyState stack σ).vars copyIndexVar =
      σ.vars copyIndexVar - 1 := by
  simp [reverseScratchBodyState, Env.setVar,
    topName_ne_copyIndexVar, (topName_ne_copyIndexVar stack).symm,
    topName_ne_ioValueVar, (topName_ne_ioValueVar stack).symm,
    copyIndexVar_ne_ioValueVar, copyIndexVar_ne_ioValueVar.symm]

theorem reverseScratchBodyState_top (stack : ℕ) (σ : Env) :
    (reverseScratchBodyState stack σ).vars (topName stack) =
      σ.vars (topName stack) + 1 := by
  simp [reverseScratchBodyState, Env.setVar]

theorem reverseScratchBodyState_scratch (stack : ℕ) (σ : Env) :
    (reverseScratchBodyState stack σ).arrs scratchName =
      σ.arrs scratchName := by
  simp [reverseScratchBodyState, Env.setArr, scratchName_ne_stackName]

theorem reverseScratchBodyState_stack_prefix (stack : ℕ) (σ : Env)
    (copied : List ℕ)
    (htop : σ.vars (topName stack) = copied.length)
    (hprefix : (σ.arrs (stackName stack)).take copied.length = copied)
    (hroom : copied.length < (σ.arrs (stackName stack)).length) :
    ((reverseScratchBodyState stack σ).arrs (stackName stack)).take
        (copied ++ [(σ.arrs scratchName).getD
          (σ.vars copyIndexVar - 1) 0]).length =
      copied ++ [(σ.arrs scratchName).getD
        (σ.vars copyIndexVar - 1) 0] := by
  simp only [reverseScratchBodyState, Env.setVar, Env.setArr, if_pos]
  rw [htop]
  have h := take_set_top (σ.arrs (stackName stack)) copied.reverse
    ((σ.arrs scratchName).getD (σ.vars copyIndexVar - 1) 0)
    (by simpa using hprefix) (by simpa using hroom)
  simpa using h

theorem scratch_getD_eq_of_prefix (σ : Env) (codes : List ℕ) (i : ℕ)
    (hprefix : (σ.arrs scratchName).take codes.length = codes)
    (hi : i < codes.length) :
    (σ.arrs scratchName).getD i 0 = codes.getD i 0 := by
  have h := congrArg (fun l : List ℕ => l[i]?.getD 0) hprefix
  simpa [List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt hi] using h

theorem reverse_drop_step (codes : List ℕ) (i : ℕ)
    (hpositive : 0 < i) (hbound : i ≤ codes.length) :
    (codes.drop (i - 1)).reverse =
      (codes.drop i).reverse ++ [codes.getD (i - 1) 0] := by
  have hi : i - 1 < codes.length := by omega
  have hdrop := List.drop_eq_getElem_cons (l := codes) hi
  have hsucc : i - 1 + 1 = i := by omega
  rw [hsucc] at hdrop
  rw [hdrop, List.reverse_cons]
  congr 2
  simp [List.getD_eq_getElem?_getD, hi]

/-- Reversing loop invariant.  When the read index is `i`, exactly the suffix
after `i` has been copied, in reverse order, into the destination prefix. -/
theorem reverseScratchLoop_correct (stack : ℕ) (σ : Env) (codes : List ℕ)
    (hindex : σ.vars copyIndexVar = codes.length)
    (htop : σ.vars (topName stack) = 0)
    (hscratch : (σ.arrs scratchName).take codes.length = codes)
    (hcapacity : codes.length ≤ (σ.arrs (stackName stack)).length) :
    ∃ σ' cost,
      BigStep (reverseScratchLoop stack) σ σ' cost ∧
      cost = 19 * codes.length + 4 ∧
      σ'.vars copyIndexVar = 0 ∧
      σ'.vars (topName stack) = codes.length ∧
      (σ'.arrs (stackName stack)).take codes.length = codes.reverse := by
  suffices loop : ∀ (i : ℕ) (τ : Env),
      τ.vars copyIndexVar = i →
      i ≤ codes.length →
      τ.vars (topName stack) = codes.length - i →
      (τ.arrs scratchName).take codes.length = codes →
      (τ.arrs (stackName stack)).take (codes.drop i).reverse.length =
        (codes.drop i).reverse →
      codes.length ≤ (τ.arrs (stackName stack)).length →
      ∃ τ' cost,
        BigStep (reverseScratchLoop stack) τ τ' cost ∧
        cost = 19 * i + 4 ∧
        τ'.vars copyIndexVar = 0 ∧
        τ'.vars (topName stack) = codes.length ∧
        (τ'.arrs (stackName stack)).take codes.length = codes.reverse by
    simpa [hindex, htop] using loop codes.length σ hindex (by omega)
      (by simp [htop]) hscratch (by simp) hcapacity
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro τ hτindex hibound hτtop hτscratch hτprefix hτcapacity
      by_cases hizero : i = 0
      · refine ⟨τ, 4, ?_, by simp [hizero], ?_, ?_, ?_⟩
        · unfold reverseScratchLoop
          exact BigStep.while_false
            (by simp [Cond.eval, Expr.eval, hτindex, hizero])
        · omega
        · omega
        · simpa [hizero] using hτprefix
      · have hipositive : 0 < i := Nat.pos_of_ne_zero hizero
        have hscratchBound : τ.vars copyIndexVar ≤
            (τ.arrs scratchName).length := by
          have hlen := congrArg List.length hτscratch
          simp only [List.length_take] at hlen
          calc
            τ.vars copyIndexVar = i := hτindex
            _ ≤ codes.length := hibound
            _ ≤ (τ.arrs scratchName).length := by omega
        have hroom : τ.vars (topName stack) <
            (τ.arrs (stackName stack)).length := by
          rw [hτtop]
          omega
        let υ := reverseScratchBodyState stack τ
        have hbody := reverseScratchBody_correct stack τ
          (by simpa [hτindex] using hipositive) hscratchBound hroom
        have hυindex : υ.vars copyIndexVar = i - 1 := by
          rw [reverseScratchBodyState_index, hτindex]
        have hυtop : υ.vars (topName stack) = codes.length - (i - 1) := by
          rw [reverseScratchBodyState_top, hτtop]
          omega
        have hυscratch : (υ.arrs scratchName).take codes.length = codes := by
          rw [reverseScratchBodyState_scratch]
          exact hτscratch
        have hvalue : (τ.arrs scratchName).getD (i - 1) 0 =
            codes.getD (i - 1) 0 := by
          apply scratch_getD_eq_of_prefix τ codes
          · exact hτscratch
          · omega
        have hstep := reverse_drop_step codes i hipositive hibound
        have hυprefix :
            (υ.arrs (stackName stack)).take
                (codes.drop (i - 1)).reverse.length =
              (codes.drop (i - 1)).reverse := by
          rw [hstep, ← hvalue]
          simpa [υ, hτindex] using
            (reverseScratchBodyState_stack_prefix stack τ
              (codes.drop i).reverse
              (by simpa [List.length_reverse, List.length_drop] using hτtop)
              hτprefix
              (by
                calc
                  (codes.drop i).reverse.length = codes.length - i := by simp
                  _ = τ.vars (topName stack) := hτtop.symm
                  _ < (τ.arrs (stackName stack)).length := hroom))
        have hυcapacity : codes.length ≤
            (υ.arrs (stackName stack)).length := by
          rw [BigStep.arr_length_eq hbody (stackName stack)]
          exact hτcapacity
        obtain ⟨τ', tailCost, htail, htailCost, hfinalIndex,
            hfinalTop, hfinalPrefix⟩ :=
          ih (i - 1) (by omega) υ hυindex (by omega) hυtop hυscratch
            hυprefix hυcapacity
        refine ⟨τ', 19 + tailCost, ?_, ?_, hfinalIndex,
          hfinalTop, hfinalPrefix⟩
        · unfold reverseScratchLoop at htail ⊢
          simpa [hτindex] using BigStep.while_true
            (b := .lt (.lit 0) (.var copyIndexVar))
            (by simp [Cond.eval, Expr.eval, hτindex, hipositive]) hbody htail
        · rw [htailCost]
          omega

theorem reverseScratchIntoStack_correct (stack : ℕ) (σ : Env)
    (codes : List ℕ)
    (hlength : σ.vars encodedLengthVar = codes.length)
    (hscratch : (σ.arrs scratchName).take codes.length = codes)
    (hcapacity : codes.length ≤ (σ.arrs (stackName stack)).length) :
    ∃ σ' cost,
      BigStep (reverseScratchIntoStack stack) σ σ' cost ∧
      cost = 19 * codes.length + 9 ∧
      σ'.vars copyIndexVar = 0 ∧
      σ'.vars (topName stack) = codes.length ∧
      (σ'.arrs (stackName stack)).take codes.length = codes.reverse := by
  let σ₁ := σ.setVar copyIndexVar codes.length
  have hcopy : BigStep
      (.assign copyIndexVar (.var encodedLengthVar)) σ σ₁ 2 := by
    apply BigStep.assign
    simp [Expr.eval, σ₁, hlength]
  let σ₂ := σ₁.setVar (topName stack) 0
  have hzero : BigStep (.assign (topName stack) (.lit 0)) σ₁ σ₂ 2 := by
    exact BigStep.assign rfl
  have hσ₂index : σ₂.vars copyIndexVar = codes.length := by
    simp [σ₂, σ₁, Env.setVar, (topName_ne_copyIndexVar stack).symm]
  have hσ₂top : σ₂.vars (topName stack) = 0 := by
    simp [σ₂, Env.setVar]
  have hσ₂scratch : (σ₂.arrs scratchName).take codes.length = codes := by
    simpa [σ₂, σ₁] using hscratch
  have hσ₂capacity : codes.length ≤
      (σ₂.arrs (stackName stack)).length := by
    simpa [σ₂, σ₁] using hcapacity
  obtain ⟨σ', loopCost, hloop, hloopCost, hfinalIndex,
      hfinalTop, hfinalPrefix⟩ :=
    reverseScratchLoop_correct stack σ₂ codes hσ₂index hσ₂top
      hσ₂scratch hσ₂capacity
  have hrun := BigStep.seq hcopy (BigStep.seq hzero
    (BigStep.seq hloop (BigStep.skip (σ := σ'))))
  refine ⟨σ', 2 + 2 + loopCost + 1, ?_, ?_, hfinalIndex,
    hfinalTop, hfinalPrefix⟩
  · convert hrun using 1 <;> simp [reverseScratchIntoStack, seqs] <;> omega
  · rw [hloopCost]
    omega

/-- Complete native-input prelude, including finite-control initialization. -/
def compileInputCodec (inputStack separatorCode zeroCode oneCode
    initialStateCode mainLabelCode : ℕ) : Com :=
  seqs [
    encodeNativeInputToScratch separatorCode zeroCode oneCode,
    reverseScratchIntoStack inputStack,
    .assign stateVar (.lit initialStateCode),
    .assign labelVar (.lit (mainLabelCode + 1))]

theorem compileInputCodec_correct (inputStack separatorCode zeroCode oneCode
    initialStateCode mainLabelCode : ℕ) (σ : Env) (x : List ℕ)
    (hinp : σ.inp = x.length :: x)
    (hscratchCapacity :
      (encodeWordCodes separatorCode zeroCode oneCode x).length ≤
        (σ.arrs scratchName).length)
    (hstackCapacity :
      (encodeWordCodes separatorCode zeroCode oneCode x).length ≤
        (σ.arrs (stackName inputStack)).length) :
    ∃ σ' cost,
      BigStep (compileInputCodec inputStack separatorCode zeroCode oneCode
        initialStateCode mainLabelCode) σ σ' cost ∧
      cost = encodeInputLoopCost x + 19 *
          (encodeWordCodes separatorCode zeroCode oneCode x).length + 18 ∧
      σ'.inp = [] ∧
      σ'.vars stateVar = initialStateCode ∧
      σ'.vars labelVar = mainLabelCode + 1 ∧
      σ'.vars (topName inputStack) =
        (encodeWordCodes separatorCode zeroCode oneCode x).length ∧
      (σ'.arrs (stackName inputStack)).take
          (encodeWordCodes separatorCode zeroCode oneCode x).length =
        (encodeWordCodes separatorCode zeroCode oneCode x).reverse := by
  let codes := encodeWordCodes separatorCode zeroCode oneCode x
  obtain ⟨σ₁, encodeCost, hencode, hencodeCost, hencodeInp,
      hencodeLength, hencodePrefix⟩ :=
    encodeNativeInputToScratch_correct separatorCode zeroCode oneCode σ x
      hinp hscratchCapacity
  have hstackCapacity₁ : codes.length ≤
      (σ₁.arrs (stackName inputStack)).length := by
    rw [BigStep.arr_length_eq hencode (stackName inputStack)]
    exact hstackCapacity
  obtain ⟨σ₂, reverseCost, hreverse, hreverseCost, hreverseIndex,
      hreverseTop, hreversePrefix⟩ :=
    reverseScratchIntoStack_correct inputStack σ₁ codes
      (by simpa [codes] using hencodeLength)
      (by simpa [codes] using hencodePrefix) hstackCapacity₁
  let σ₃ := σ₂.setVar stateVar initialStateCode
  have hstate : BigStep (.assign stateVar (.lit initialStateCode)) σ₂ σ₃ 2 :=
    BigStep.assign rfl
  let σ₄ := σ₃.setVar labelVar (mainLabelCode + 1)
  have hlabel : BigStep
      (.assign labelVar (.lit (mainLabelCode + 1))) σ₃ σ₄ 2 :=
    BigStep.assign rfl
  have hrun := BigStep.seq hencode (BigStep.seq hreverse
    (BigStep.seq hstate (BigStep.seq hlabel (BigStep.skip (σ := σ₄)))))
  refine ⟨σ₄, encodeCost + reverseCost + 2 + 2 + 1, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · convert hrun using 1 <;> simp [compileInputCodec, seqs] <;> omega
  · rw [hencodeCost, hreverseCost]
    simp [codes]
    omega
  · rw [show σ₄.inp = σ₂.inp by rfl]
    rw [hreverse.inp_eq]
    · exact hencodeInp
    · simp [reverseScratchIntoStack, reverseScratchLoop,
        reverseScratchBody, seqs, Com.reads]
  · simp [σ₄, σ₃, Env.setVar, stateVar, labelVar]
  · simp [σ₄, Env.setVar]
  · simpa [σ₄, σ₃, codes] using hreverseTop
  · simpa [σ₄, σ₃, codes] using hreversePrefix

/-- Consume one logical output symbol.  Separators flush the preceding number
(except before the first number); binary digits update a little-endian
accumulator. -/
def consumeOutputSymbol (separatorCode zeroCode oneCode : ℕ) : Com :=
  .ite (.eq (.var outputCodeVar) (.lit separatorCode))
    (seqs [
      .ite (.eq (.var outputHaveVar) (.lit 0)) .skip
        (.write (.var outputValueVar)),
      .assign outputValueVar (.lit 0),
      .assign outputPlaceVar (.lit 1),
      .assign outputHaveVar (.lit 1)])
    (.ite (.eq (.var outputCodeVar) (.lit zeroCode))
      (.assign outputPlaceVar (.mul (.var outputPlaceVar) (.lit 2)))
      (seqs [
        .assign outputValueVar
          (.add (.var outputValueVar) (.var outputPlaceVar)),
        .assign outputPlaceVar (.mul (.var outputPlaceVar) (.lit 2))]))

/-- Decode the halted TM output stack to the native RAM output tape.  The
valid-encoding invariant ensures every non-separator symbol is one of the two
digit codes, so the final branch is the `one` case. -/
def compileOutputCodec (outputStack separatorCode zeroCode oneCode : ℕ) : Com :=
  seqs [
    .assign outputIndexVar (.var (topName outputStack)),
    .assign outputValueVar (.lit 0),
    .assign outputPlaceVar (.lit 1),
    .assign outputHaveVar (.lit 0),
    .while (.lt (.lit 0) (.var outputIndexVar)) (seqs [
      .assign outputIndexVar (.sub (.var outputIndexVar) (.lit 1)),
      .assign outputCodeVar (.get (stackName outputStack) (.var outputIndexVar)),
      consumeOutputSymbol separatorCode zeroCode oneCode]),
    .ite (.eq (.var outputHaveVar) (.lit 0)) .skip
      (.write (.var outputValueVar))]

/-- Native tape wrapper around the initialized finite-TM interpreter. -/
noncomputable def FinTM2.compileNativeMachine (tm : Turing.FinTM2)
    (inputStack outputStack separatorIn zeroIn oneIn separatorOut zeroOut oneOut
      initialStateCode mainLabelCode : ℕ) : Com :=
  seqs [
    compileInputCodec inputStack separatorIn zeroIn oneIn
      initialStateCode mainLabelCode,
    FinTM2.compileMachine tm,
    compileOutputCodec outputStack separatorOut zeroOut oneOut]

end Lax20Proofs.TMToRam
