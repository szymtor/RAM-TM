import Lax20Proofs.Computability.FiniteToPartrec
import Lax20Proofs.TMToRam.NativeMachine

namespace Lax20Proofs.Computability.PartrecNativeCodec

open Computability Turing Turing.PartrecToTM2
open Lax13Proofs.Imp
open Lax20Proofs.TMToRam

def bitSymbol : Bool → Γ'
  | false => .bit0
  | true => .bit1

theorem trPosNum_eq_bits (n : PosNum) :
    trPosNum n = (n : ℕ).bits.map bitSymbol := by
  induction n with
  | one => rfl
  | bit0 n ih =>
      have hb := Nat.bits_append_bit (n : ℕ) false (by
        intro h
        have hp : 0 < (n : ℕ) := PosNum.cast_pos n
        omega)
      have hc : (PosNum.bit0 n : ℕ) = Nat.bit false (n : ℕ) := by
        simp [PosNum.cast_bit0, Nat.bit, Nat.two_mul]
      rw [hc, hb]
      change Γ'.bit0 :: trPosNum n =
        Γ'.bit0 :: List.map bitSymbol (n : ℕ).bits
      simp [ih]
  | bit1 n ih =>
      have hb := Nat.bits_append_bit (n : ℕ) true (by simp)
      have hc : (PosNum.bit1 n : ℕ) = Nat.bit true (n : ℕ) := by
        simp [PosNum.cast_bit1, Nat.bit, Nat.two_mul]
      rw [hc, hb]
      change Γ'.bit1 :: trPosNum n =
        Γ'.bit1 :: List.map bitSymbol (n : ℕ).bits
      simp [ih]

theorem trNat_eq_bits (n : ℕ) : trNat n = n.bits.map bitSymbol := by
  rw [trNat]
  cases hnum : (n : Num) with
  | zero =>
      have hn : n = 0 := by
        have h := congrArg (fun x : Num => (x : ℕ)) hnum
        simpa using h
      subst n
      rfl
  | pos p =>
      have hn : n = (p : ℕ) := by
        have h := congrArg (fun x : Num => (x : ℕ)) hnum
        simpa using h
      subst n
      change trPosNum p = (p : ℕ).bits.map bitSymbol
      exact trPosNum_eq_bits p

/-- Numeric interpreter codes for one `ToPartrec` natural: little-endian
bits followed by the list delimiter. -/
def encodePartrecNatCodes (consCode zeroCode oneCode n : ℕ) : List ℕ :=
  n.bits.map (boolDigitCode zeroCode oneCode) ++ [consCode]

def encodePartrecListCodes (consCode zeroCode oneCode : ℕ) :
    List ℕ → List ℕ
  | [] => []
  | n :: ns => encodePartrecNatCodes consCode zeroCode oneCode n ++
      encodePartrecListCodes consCode zeroCode oneCode ns

@[simp] theorem encodePartrecListCodes_nil (consCode zeroCode oneCode : ℕ) :
    encodePartrecListCodes consCode zeroCode oneCode [] = [] := rfl

@[simp] theorem encodePartrecListCodes_cons (consCode zeroCode oneCode n : ℕ)
    (ns : List ℕ) :
    encodePartrecListCodes consCode zeroCode oneCode (n :: ns) =
      encodePartrecNatCodes consCode zeroCode oneCode n ++
        encodePartrecListCodes consCode zeroCode oneCode ns := rfl

open PartrecFiniteTM2 in
theorem mainSymbol_available (c : ToPartrec.Code) (a : Γ') :
    (⟨(machine c).k₀, a⟩ : Σ k, (machine c).Γ k) ∈
      FinTM2.availableSymbols (machine c) := by
  apply Set.mem_union_left
  exact ⟨a, rfl⟩

open PartrecFiniteTM2 in
noncomputable def symbolCode (c : ToPartrec.Code) (a : Γ') : ℕ :=
  FinTM2.codeSymbol (machine c) a (mainSymbol_available c a)

open PartrecFiniteTM2 in
theorem codeStack_eq_map_symbolCode (c : ToPartrec.Code) (xs : List Γ')
    (hxs : ∀ a ∈ xs,
      (⟨(machine c).k₀, a⟩ : Σ k, (machine c).Γ k) ∈
        FinTM2.availableSymbols (machine c)) :
    FinTM2.codeStack (machine c) (machine c).k₀ xs hxs =
      xs.map (symbolCode c) := by
  induction xs with
  | nil =>
      rw [FinTM2.codeStack_nil]
      rfl
  | cons a xs ih =>
      rw [FinTM2.codeStack_cons]
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · rfl
      · exact ih (fun b hb => hxs b (by simp [hb]))

theorem map_trNat_symbolCode (c : ToPartrec.Code) (n : ℕ) :
    (trNat n).map (symbolCode c) =
      n.bits.map (boolDigitCode (symbolCode c .bit0) (symbolCode c .bit1)) := by
  rw [trNat_eq_bits, List.map_map]
  apply List.map_congr_left
  intro b hb
  cases b <;> rfl

theorem map_trList_symbolCode (c : ToPartrec.Code) (xs : List ℕ) :
    (trList xs).map (symbolCode c) =
      encodePartrecListCodes (symbolCode c .cons)
        (symbolCode c .bit0) (symbolCode c .bit1) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [trList, List.map_append, List.map_cons, List.map_nil,
        encodePartrecListCodes_cons]
      rw [map_trNat_symbolCode, ih]
      simp [encodePartrecNatCodes]

open PartrecFiniteTM2 in
theorem codeStack_trList (c : ToPartrec.Code) (xs : List ℕ)
    (hxs : ∀ a ∈ trList xs,
      (⟨(machine c).k₀, a⟩ : Σ k, (machine c).Γ k) ∈
        FinTM2.availableSymbols (machine c)) :
    FinTM2.codeStack (machine c) (machine c).k₀ (trList xs) hxs =
      encodePartrecListCodes (symbolCode c .cons)
        (symbolCode c .bit0) (symbolCode c .bit1) xs := by
  rw [codeStack_eq_map_symbolCode, map_trList_symbolCode]

theorem symbolCodes_pairwise (c : ToPartrec.Code) :
    symbolCode c Γ'.cons ≠ symbolCode c Γ'.bit0 ∧
      symbolCode c Γ'.cons ≠ symbolCode c Γ'.bit1 ∧
      symbolCode c Γ'.bit0 ≠ symbolCode c Γ'.bit1 := by
  have hinj : Function.Injective (symbolCode c) := by
    intro a b h
    unfold symbolCode FinTM2.codeSymbol at h
    have hs := @finCode_injective
      (FinTM2.AvailableAt (PartrecFiniteTM2.machine c)
        (PartrecFiniteTM2.machine c).k₀)
      (FinTM2.AvailableAt.instFintype _ _)
      (FinTM2.AvailableAt.instDecidableEq _ _)
      ⟨a, mainSymbol_available c a⟩
      ⟨b, mainSymbol_available c b⟩ h
    exact congrArg Subtype.val hs
  constructor
  · intro h
    cases hinj h
  constructor
  · intro h
    cases hinj h
  · intro h
    cases hinj h

/-- One outer-loop iteration for the native `ToPartrec` input codec. -/
def encodePartrecInputBody (consCode zeroCode oneCode : ℕ) : Com :=
  seqs [
    .read inputValueVar,
    encodeBitsLoop zeroCode oneCode,
    appendScratch (.lit consCode),
    .assign inputCountVar (.sub (.var inputCountVar) (.lit 1))]

def encodePartrecInputLoop (consCode zeroCode oneCode : ℕ) : Com :=
  .while (.lt (.lit 0) (.var inputCountVar))
    (encodePartrecInputBody consCode zeroCode oneCode)

def encodePartrecInputLoopCost : List ℕ → ℕ
  | [] => 4
  | a :: xs => 4 + (29 * a.bits.length + 18) +
      encodePartrecInputLoopCost xs

theorem encodePartrecInputBody_correct (consCode zeroCode oneCode : ℕ)
    (σ : Env) (a : ℕ) (rest written : List ℕ)
    (hinp : σ.inp = a :: rest)
    (hcount : 0 < σ.vars inputCountVar)
    (hindex : σ.vars encodedLengthVar = written.length)
    (hprefix : (σ.arrs scratchName).take written.length = written)
    (hspace : written.length +
        (encodePartrecNatCodes consCode zeroCode oneCode a).length ≤
      (σ.arrs scratchName).length) :
    ∃ σ' cost,
      BigStep (encodePartrecInputBody consCode zeroCode oneCode) σ σ' cost ∧
      cost = 29 * a.bits.length + 18 ∧
      σ'.inp = rest ∧
      σ'.vars inputCountVar = σ.vars inputCountVar - 1 ∧
      σ'.vars encodedLengthVar = written.length +
        (encodePartrecNatCodes consCode zeroCode oneCode a).length ∧
      (σ'.arrs scratchName).take
          (written ++ encodePartrecNatCodes consCode zeroCode oneCode a).length =
        written ++ encodePartrecNatCodes consCode zeroCode oneCode a := by
  let σ₁ := { σ.setVar inputValueVar a with inp := rest }
  have hread : BigStep (.read inputValueVar) σ σ₁ 1 := BigStep.read hinp
  have hσ₁value : σ₁.vars inputValueVar = a := by
    simp [σ₁, Env.setVar]
  have hbitsSpace : written.length + a.bits.length ≤
      (σ₁.arrs scratchName).length := by
    have h : written.length + a.bits.length ≤
        (σ.arrs scratchName).length := by
      simp [encodePartrecNatCodes] at hspace
      omega
    simpa [σ₁] using h
  obtain ⟨σ₂, bitsCost, hbits, hbitsCost, hbitsValue,
      hbitsLength, hbitsPrefix⟩ :=
    encodeBitsLoop_correct zeroCode oneCode σ₁ written
      (by simpa [σ₁, Env.setVar, encodedLengthVar, inputValueVar] using hindex)
      (by simpa [σ₁] using hprefix)
      (by simpa [hσ₁value] using hbitsSpace)
  let written₂ := written ++
    a.bits.map (boolDigitCode zeroCode oneCode)
  have hσ₂index : σ₂.vars encodedLengthVar = written₂.length := by
    rw [hbitsLength, hσ₁value]
    simp [written₂]
  have hσ₂prefix : (σ₂.arrs scratchName).take written₂.length = written₂ := by
    simpa [written₂, hσ₁value] using hbitsPrefix
  have hroom : σ₂.vars encodedLengthVar < (σ₂.arrs scratchName).length := by
    have harr : (σ₂.arrs scratchName).length =
        (σ.arrs scratchName).length := by
      rw [BigStep.arr_length_eq hbits scratchName]
      rfl
    rw [hσ₂index, harr]
    simp [written₂, encodePartrecNatCodes] at hspace ⊢
    omega
  let σ₃ := appendScratchState σ₂ consCode
  have happend : BigStep (appendScratch (.lit consCode)) σ₂ σ₃ 8 := by
    simpa [σ₃] using appendScratch_correct σ₂ (.lit consCode) consCode rfl hroom
  have hσ₃index : σ₃.vars encodedLengthVar =
      (written ++ encodePartrecNatCodes consCode zeroCode oneCode a).length := by
    rw [appendScratchState_length, hσ₂index]
    simp [written₂, encodePartrecNatCodes, List.append_assoc]
    omega
  have hσ₃prefix : (σ₃.arrs scratchName).take
      (written ++ encodePartrecNatCodes consCode zeroCode oneCode a).length =
      written ++ encodePartrecNatCodes consCode zeroCode oneCode a := by
    have h := appendScratchState_prefix σ₂ consCode written₂
      hσ₂index hσ₂prefix (by simpa [hσ₂index] using hroom)
    simpa [σ₃, written₂, encodePartrecNatCodes, List.append_assoc] using h
  have hcount₂ : σ₂.vars inputCountVar = σ.vars inputCountVar := by
    rw [hbits.vars_eq]
    · simp [σ₁, Env.setVar, inputCountVar, inputValueVar]
    · simp [encodeBitsLoop, encodeBitsBody, appendScratch, seqs, Com.wvars,
        inputCountVar, inputValueVar, inputBitVar, inputHalfVar,
        encodedLengthVar]
  have hcount₃ : σ₃.vars inputCountVar = σ.vars inputCountVar := by
    rw [show σ₃.vars inputCountVar = σ₂.vars inputCountVar by
      simp [σ₃, appendScratchState, Env.setVar, Env.setArr,
        inputCountVar, encodedLengthVar]]
    exact hcount₂
  have hinp₂ : σ₂.inp = rest := by
    have hpreserve := hbits.inp_eq (by
      simp [encodeBitsLoop, encodeBitsBody, appendScratch, seqs, Com.reads])
    rw [hpreserve]
  have hinp₃ : σ₃.inp = rest := by simpa [σ₃] using hinp₂
  let σ₄ := σ₃.setVar inputCountVar (σ.vars inputCountVar - 1)
  have hdecrement : BigStep
      (.assign inputCountVar (.sub (.var inputCountVar) (.lit 1))) σ₃ σ₄ 4 := by
    apply BigStep.assign
    simp [Expr.eval, σ₄, hcount₃]
  have hrun := BigStep.seq hread (BigStep.seq hbits
    (BigStep.seq happend (BigStep.seq hdecrement (BigStep.skip (σ := σ₄)))))
  refine ⟨σ₄, 1 + bitsCost + 8 + 4 + 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert hrun using 1 <;> simp [encodePartrecInputBody, seqs] <;> omega
  · rw [hbitsCost, hσ₁value]
    omega
  · simpa [σ₄] using hinp₃
  · simp [σ₄, Env.setVar]
  · simpa [σ₄, Env.setVar, inputCountVar, encodedLengthVar] using hσ₃index
  · simpa [σ₄] using hσ₃prefix

theorem encodePartrecInputLoop_correct (consCode zeroCode oneCode : ℕ)
    (σ : Env) (remaining written : List ℕ)
    (hinp : σ.inp = remaining)
    (hcount : σ.vars inputCountVar = remaining.length)
    (hindex : σ.vars encodedLengthVar = written.length)
    (hprefix : (σ.arrs scratchName).take written.length = written)
    (hspace : written.length +
        (encodePartrecListCodes consCode zeroCode oneCode remaining).length ≤
      (σ.arrs scratchName).length) :
    ∃ σ' cost,
      BigStep (encodePartrecInputLoop consCode zeroCode oneCode) σ σ' cost ∧
      cost = encodePartrecInputLoopCost remaining ∧
      σ'.inp = [] ∧ σ'.vars inputCountVar = 0 ∧
      σ'.vars encodedLengthVar = written.length +
        (encodePartrecListCodes consCode zeroCode oneCode remaining).length ∧
      (σ'.arrs scratchName).take
          (written ++ encodePartrecListCodes consCode zeroCode oneCode remaining).length =
        written ++ encodePartrecListCodes consCode zeroCode oneCode remaining := by
  induction remaining generalizing σ written with
  | nil =>
      have hzero : σ.vars inputCountVar = 0 := by simpa using hcount
      refine ⟨σ, 4, ?_, rfl, by simpa using hinp, hzero, ?_, ?_⟩
      · exact BigStep.while_false (by simp [Cond.eval, Expr.eval, hzero])
      · simpa using hindex
      · simpa using hprefix
  | cons a remaining ih =>
      have hpositive : 0 < σ.vars inputCountVar := by simp [hcount]
      have hheadSpace : written.length +
          (encodePartrecNatCodes consCode zeroCode oneCode a).length ≤
          (σ.arrs scratchName).length := by
        simp only [encodePartrecListCodes_cons, List.length_append] at hspace
        omega
      obtain ⟨τ, bodyCost, hbody, hbodyCost, hτinp, hτcount,
          hτlength, hτprefix⟩ :=
        encodePartrecInputBody_correct consCode zeroCode oneCode σ a remaining
          written (by simpa using hinp) hpositive hindex hprefix hheadSpace
      let written' := written ++
        encodePartrecNatCodes consCode zeroCode oneCode a
      have hτcount' : τ.vars inputCountVar = remaining.length := by
        rw [hτcount, hcount]
        simp
      have hτlength' : τ.vars encodedLengthVar = written'.length := by
        simpa [written'] using hτlength
      have hτprefix' : (τ.arrs scratchName).take written'.length = written' := by
        simpa [written'] using hτprefix
      have hτspace : written'.length +
          (encodePartrecListCodes consCode zeroCode oneCode remaining).length ≤
          (τ.arrs scratchName).length := by
        rw [BigStep.arr_length_eq hbody scratchName]
        simpa [written', List.length_append, Nat.add_assoc] using hspace
      obtain ⟨σ', tailCost, htail, htailCost, hfinalInp, hfinalCount,
          hfinalLength, hfinalPrefix⟩ :=
        ih τ written' hτinp hτcount' hτlength' hτprefix' hτspace
      refine ⟨σ', 4 + bodyCost + tailCost, ?_, ?_, hfinalInp,
        hfinalCount, ?_, ?_⟩
      · simpa [encodePartrecInputLoop] using BigStep.while_true
          (b := .lt (.lit 0) (.var inputCountVar))
          (by simp [Cond.eval, Expr.eval, hpositive]) hbody htail
      · rw [hbodyCost, htailCost]
        rfl
      · rw [hfinalLength]
        simp [written', List.length_append, Nat.add_assoc]
      · simpa [written', List.append_assoc] using hfinalPrefix

/-- Read all of the already length-prefixed native input and encode that
entire list in the `ToPartrec` stack convention. -/
def encodeNativePartrecInputToScratch (consCode zeroCode oneCode : ℕ) : Com :=
  seqs [
    .read inputCountVar,
    .assign encodedLengthVar (.lit 0),
    .assign inputValueVar (.var inputCountVar),
    encodeBitsLoop zeroCode oneCode,
    appendScratch (.lit consCode),
    encodePartrecInputLoop consCode zeroCode oneCode]

theorem encodeNativePartrecInputToScratch_correct
    (consCode zeroCode oneCode : ℕ) (σ : Env) (x : List ℕ)
    (hinp : σ.inp = x.length :: x)
    (hspace : (encodePartrecListCodes consCode zeroCode oneCode
        (x.length :: x)).length ≤ (σ.arrs scratchName).length) :
    ∃ σ' cost,
      BigStep (encodeNativePartrecInputToScratch consCode zeroCode oneCode)
        σ σ' cost ∧
      cost = 29 * x.length.bits.length + 18 +
        encodePartrecInputLoopCost x ∧
      σ'.inp = [] ∧
      σ'.vars encodedLengthVar =
        (encodePartrecListCodes consCode zeroCode oneCode
          (x.length :: x)).length ∧
      (σ'.arrs scratchName).take
          (encodePartrecListCodes consCode zeroCode oneCode
            (x.length :: x)).length =
        encodePartrecListCodes consCode zeroCode oneCode (x.length :: x) := by
  let σ₁ := { σ.setVar inputCountVar x.length with inp := x }
  have hread : BigStep (.read inputCountVar) σ σ₁ 1 := BigStep.read hinp
  let σ₂ := σ₁.setVar encodedLengthVar 0
  have hzero : BigStep (.assign encodedLengthVar (.lit 0)) σ₁ σ₂ 2 :=
    BigStep.assign rfl
  let σ₃ := σ₂.setVar inputValueVar x.length
  have hvalue : BigStep (.assign inputValueVar (.var inputCountVar)) σ₂ σ₃ 2 := by
    apply BigStep.assign
    simp [Expr.eval, σ₃, σ₂, σ₁, Env.setVar,
      inputCountVar, encodedLengthVar, inputValueVar]
  have hheadSpace : x.length.bits.length ≤
      (σ₃.arrs scratchName).length := by
    simp [encodePartrecListCodes, encodePartrecNatCodes] at hspace
    simpa [σ₃, σ₂, σ₁] using
      (show x.length.bits.length ≤ (σ.arrs scratchName).length by omega)
  have hσ₃value : σ₃.vars inputValueVar = x.length := by
    simp [σ₃, Env.setVar]
  obtain ⟨σ₄, bitsCost, hbits, hbitsCost, hbitsValue,
      hbitsLength, hbitsPrefix⟩ :=
    encodeBitsLoop_correct zeroCode oneCode σ₃ []
      (by
        have hne : encodedLengthVar ≠ inputValueVar := by decide
        simp [σ₃, σ₂, Env.setVar, hne])
      (by simp)
      (by simpa [hσ₃value] using hheadSpace)
  let headBits := x.length.bits.map (boolDigitCode zeroCode oneCode)
  have hσ₄index : σ₄.vars encodedLengthVar = headBits.length := by
    rw [hbitsLength, hσ₃value]
    simp [headBits]
  have hσ₄prefix : (σ₄.arrs scratchName).take headBits.length = headBits := by
    simpa [headBits, hσ₃value] using hbitsPrefix
  have hroom : σ₄.vars encodedLengthVar < (σ₄.arrs scratchName).length := by
    have harr : (σ₄.arrs scratchName).length =
        (σ.arrs scratchName).length := by
      rw [BigStep.arr_length_eq hbits scratchName]
      rfl
    rw [hσ₄index, harr]
    simp [headBits, encodePartrecListCodes, encodePartrecNatCodes] at hspace ⊢
    omega
  let σ₅ := appendScratchState σ₄ consCode
  have happend : BigStep (appendScratch (.lit consCode)) σ₄ σ₅ 8 := by
    simpa [σ₅] using appendScratch_correct σ₄ (.lit consCode) consCode rfl hroom
  let written := encodePartrecNatCodes consCode zeroCode oneCode x.length
  have hσ₅index : σ₅.vars encodedLengthVar = written.length := by
    rw [appendScratchState_length, hσ₄index]
    simp [written, headBits, encodePartrecNatCodes]
  have hσ₅prefix : (σ₅.arrs scratchName).take written.length = written := by
    have h := appendScratchState_prefix σ₄ consCode headBits
      hσ₄index hσ₄prefix (by simpa [hσ₄index] using hroom)
    simpa [σ₅, written, headBits, encodePartrecNatCodes] using h
  have hσ₅count : σ₅.vars inputCountVar = x.length := by
    rw [show σ₅.vars inputCountVar = σ₄.vars inputCountVar by
      simp [σ₅, appendScratchState, Env.setVar, Env.setArr,
        inputCountVar, encodedLengthVar]]
    rw [hbits.vars_eq]
    · simp [σ₃, σ₂, σ₁, Env.setVar, inputCountVar,
        inputValueVar, encodedLengthVar]
    · simp [encodeBitsLoop, encodeBitsBody, appendScratch, seqs, Com.wvars,
        inputCountVar, inputValueVar, inputBitVar, inputHalfVar,
        encodedLengthVar]
  have hσ₅inp : σ₅.inp = x := by
    have hpreserve := hbits.inp_eq (by
      simp [encodeBitsLoop, encodeBitsBody, appendScratch, seqs, Com.reads])
    rw [show σ₅.inp = σ₄.inp by rfl, hpreserve]
    rfl
  have htailSpace : written.length +
      (encodePartrecListCodes consCode zeroCode oneCode x).length ≤
      (σ₅.arrs scratchName).length := by
    rw [BigStep.arr_length_eq happend scratchName,
      BigStep.arr_length_eq hbits scratchName]
    simpa [written] using hspace
  obtain ⟨σ', loopCost, hloop, hloopCost, hfinalInp, _hfinalCount,
      hfinalLength, hfinalPrefix⟩ :=
    encodePartrecInputLoop_correct consCode zeroCode oneCode σ₅ x written
      hσ₅inp hσ₅count hσ₅index hσ₅prefix htailSpace
  have hrun := BigStep.seq hread (BigStep.seq hzero
    (BigStep.seq hvalue (BigStep.seq hbits (BigStep.seq happend
      (BigStep.seq hloop (BigStep.skip (σ := σ')))))))
  refine ⟨σ', 1 + 2 + 2 + bitsCost + 8 + loopCost + 1,
    ?_, ?_, hfinalInp, ?_, ?_⟩
  · convert hrun using 1 <;>
      simp [encodeNativePartrecInputToScratch, seqs] <;> omega
  · rw [hbitsCost, hσ₃value, hloopCost]
    omega
  · rw [hfinalLength]
    simp [written]
  · simpa [written, List.append_assoc] using hfinalPrefix

def compilePartrecInputCodec (inputStack consCode zeroCode oneCode
    initialStateCode mainLabelCode : ℕ) : Com :=
  seqs [
    encodeNativePartrecInputToScratch consCode zeroCode oneCode,
    reverseScratchIntoStack inputStack,
    .assign stateVar (.lit initialStateCode),
    .assign labelVar (.lit (mainLabelCode + 1))]

theorem compilePartrecInputCodec_correct
    (inputStack consCode zeroCode oneCode initialStateCode mainLabelCode : ℕ)
    (σ : Env) (x : List ℕ)
    (hinp : σ.inp = x.length :: x)
    (hscratchCapacity :
      (encodePartrecListCodes consCode zeroCode oneCode
        (x.length :: x)).length ≤ (σ.arrs scratchName).length)
    (hstackCapacity :
      (encodePartrecListCodes consCode zeroCode oneCode
        (x.length :: x)).length ≤
        (σ.arrs (stackName inputStack)).length) :
    ∃ σ' cost,
      BigStep (compilePartrecInputCodec inputStack consCode zeroCode oneCode
        initialStateCode mainLabelCode) σ σ' cost ∧
      cost =
        (29 * x.length.bits.length + 18 + encodePartrecInputLoopCost x) +
          19 * (encodePartrecListCodes consCode zeroCode oneCode
            (x.length :: x)).length + 14 ∧
      σ'.inp = [] ∧
      σ'.vars stateVar = initialStateCode ∧
      σ'.vars labelVar = mainLabelCode + 1 ∧
      σ'.vars (topName inputStack) =
        (encodePartrecListCodes consCode zeroCode oneCode
          (x.length :: x)).length ∧
      (σ'.arrs (stackName inputStack)).take
          (encodePartrecListCodes consCode zeroCode oneCode
            (x.length :: x)).length =
        (encodePartrecListCodes consCode zeroCode oneCode
          (x.length :: x)).reverse := by
  let codes := encodePartrecListCodes consCode zeroCode oneCode
    (x.length :: x)
  obtain ⟨σ₁, encodeCost, hencode, hencodeCost, hencodeInp,
      hencodeLength, hencodePrefix⟩ :=
    encodeNativePartrecInputToScratch_correct consCode zeroCode oneCode σ x
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
  refine ⟨σ₄, encodeCost + reverseCost + 2 + 2 + 1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert hrun using 1 <;> simp [compilePartrecInputCodec, seqs] <;> omega
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

open PartrecFiniteTM2 in
theorem compilePartrecInputCodec_initialRep (c : ToPartrec.Code)
    (capacity : ℕ → ℕ) (ext : String → ℕ) (x : List ℕ)
    (hstackLengths : ∀ j, ext (stackName j) = capacity j)
    (hscratch : (encodePartrecListCodes (symbolCode c .cons)
      (symbolCode c .bit0) (symbolCode c .bit1)
      (x.length :: x)).length ≤ ext scratchName)
    (hinputCapacity : (encodePartrecListCodes (symbolCode c .cons)
      (symbolCode c .bit0) (symbolCode c .bit1)
      (x.length :: x)).length ≤
        capacity (@finCode (machine c).K (machine c).kFin
          (machine c).kDecidableEq (machine c).k₀)) :
    ∃ σ' cost,
      BigStep (compilePartrecInputCodec
        (@finCode (machine c).K (machine c).kFin
          (machine c).kDecidableEq (machine c).k₀)
        (symbolCode c .cons) (symbolCode c .bit0) (symbolCode c .bit1)
        (@finCode (machine c).σ (machine c).σFin
          (Classical.decEq (machine c).σ) (machine c).initialState)
        (@finCode (machine c).Λ (machine c).ΛFin
          (Classical.decEq (machine c).Λ) (machine c).main))
        (initEnv ext (x.length :: x)) σ' cost ∧
      cost =
        (29 * x.length.bits.length + 18 + encodePartrecInputLoopCost x) +
          19 * (encodePartrecListCodes (symbolCode c .cons)
            (symbolCode c .bit0) (symbolCode c .bit1)
            (x.length :: x)).length + 14 ∧
      NumericRep σ' capacity
        (FinTM2.encodeNumericState (machine c)
          (Turing.initList (machine c) (trList (x.length :: x)))
          (FinTM2.initList_stacksWithin (machine c)
            (trList (x.length :: x)))) := by
  let tm := machine c
  let input := trList (x.length :: x)
  let hc := FinTM2.initList_stacksWithin tm input
  let inputStack := @finCode tm.K tm.kFin tm.kDecidableEq tm.k₀
  let codes := encodePartrecListCodes (symbolCode c .cons)
    (symbolCode c .bit0) (symbolCode c .bit1) (x.length :: x)
  have hscratch' : codes.length ≤
      ((initEnv ext (x.length :: x)).arrs scratchName).length := by
    simpa [initEnv, codes, encodePartrecListCodes] using hscratch
  have hstack' : codes.length ≤
      ((initEnv ext (x.length :: x)).arrs (stackName inputStack)).length := by
    simpa [initEnv, hstackLengths, codes, inputStack, tm,
      encodePartrecListCodes] using hinputCapacity
  obtain ⟨σ', cost, hrun, hcost, hinp, hstate, hlabel, htop, hprefix⟩ :=
    compilePartrecInputCodec_correct inputStack
      (symbolCode c .cons) (symbolCode c .bit0) (symbolCode c .bit1)
      (@finCode tm.σ tm.σFin (Classical.decEq tm.σ) tm.initialState)
      (@finCode tm.Λ tm.ΛFin (Classical.decEq tm.Λ) tm.main)
      (initEnv ext (x.length :: x)) x rfl hscratch' hstack'
  refine ⟨σ', cost, by simpa [tm, inputStack] using hrun,
    by simpa [codes] using hcost, ?_⟩
  change NumericRep σ' capacity
    (FinTM2.encodeNumericState tm (Turing.initList tm input) hc)
  refine ⟨?_, ?_, ?_⟩
  · simpa [FinTM2.encodeNumericState, Turing.initList] using hstate
  · simpa [FinTM2.encodeNumericState, Turing.initList] using hlabel
  · intro j
    have harrLength : (σ'.arrs (stackName j)).length = capacity j := by
      rw [BigStep.arr_length_eq hrun (stackName j)]
      simp [initEnv, hstackLengths]
    by_cases hj : j = inputStack
    · subst j
      have hcodeStack :
          (FinTM2.encodeNumericState tm (Turing.initList tm input) hc).stackData
              inputStack = codes := by
        dsimp [inputStack]
        rw [FinTM2.encodeNumericState_stack]
        have havail : ∀ a ∈ trList (x.length :: x),
            (⟨tm.k₀, a⟩ : Σ k, tm.Γ k) ∈ FinTM2.availableSymbols tm := by
          intro a ha
          exact hc tm.k₀ a (by simpa [Turing.initList, input] using ha)
        simpa [tm, input, codes] using (codeStack_trList c
          (x.length :: x) havail)
      rw [hcodeStack]
      exact ⟨htop, harrLength, hprefix⟩
    · have htarget :
          (FinTM2.encodeNumericState tm (Turing.initList tm input) hc).stackData
              j = [] := by
        simp only [FinTM2.encodeNumericState, FinTM2.codeStackFamily]
        split
        · rfl
        · rename_i k hdecode
          have hkcode : @finCode tm.K tm.kFin tm.kDecidableEq k = j :=
            @finCode_of_finDecode_eq_some tm.K tm.kFin tm.kDecidableEq
              j k hdecode
          have hk : k ≠ tm.k₀ := by
            intro heq
            subst k
            exact hj hkcode.symm
          simp [Turing.initList, hk]
      rw [htarget]
      refine ⟨?_, harrLength, by simp⟩
      rw [hrun.vars_eq]
      · simp [initEnv]
      · simp [compilePartrecInputCodec,
          encodeNativePartrecInputToScratch, encodePartrecInputLoop,
          encodePartrecInputBody, encodeBitsLoop, encodeBitsBody,
          appendScratch, reverseScratchIntoStack, reverseScratchLoop,
          reverseScratchBody, seqs, Com.wvars, hj,
          topName_injective.eq_iff, topName_ne_inputCountVar,
          topName_ne_inputValueVar, topName_ne_inputHalfVar,
          topName_ne_inputBitVar, topName_ne_encodedLengthVar,
          topName_ne_copyIndexVar, topName_ne_ioValueVar,
          (stateVar_ne_topName j).symm, (labelVar_ne_topName j).symm]

/-- The existing decoder also handles `ToPartrec`'s delimiter-after-bits
format when it starts in an already-active empty-number state and omits its
usual final flush. -/
theorem consume_encodePartrecNatCodes
    (consCode zeroCode oneCode : ℕ)
    (hconsZero : consCode ≠ zeroCode)
    (hconsOne : consCode ≠ oneCode)
    (hzeroOne : zeroCode ≠ oneCode)
    (out : List ℕ) (n : ℕ) :
    (({ out := out, value := 0, place := 1, active := 1 } : DecoderAcc).consumeCodes
      consCode zeroCode
        (encodePartrecNatCodes consCode zeroCode oneCode n)) =
      ({ out := out ++ [n], value := 0, place := 1, active := 1 } :
        DecoderAcc) := by
  rw [encodePartrecNatCodes, DecoderAcc.consumeCodes_append]
  rw [DecoderAcc.consume_bit_codes consCode zeroCode oneCode
    hconsZero hconsOne hzeroOne]
  rw [bitsValue_bits]
  simp [DecoderAcc.consumeCodes, DecoderAcc.consume, hconsZero.symm]

theorem consume_encodePartrecListCodes
    (consCode zeroCode oneCode : ℕ)
    (hconsZero : consCode ≠ zeroCode)
    (hconsOne : consCode ≠ oneCode)
    (hzeroOne : zeroCode ≠ oneCode)
    (pre xs : List ℕ) :
    (({ out := pre, value := 0, place := 1, active := 1 } : DecoderAcc).consumeCodes
      consCode zeroCode
        (encodePartrecListCodes consCode zeroCode oneCode xs)) =
      ({ out := pre ++ xs, value := 0, place := 1, active := 1 } :
        DecoderAcc) := by
  induction xs generalizing pre with
  | nil => simp [encodePartrecListCodes, DecoderAcc.consumeCodes]
  | cons a xs ih =>
      rw [encodePartrecListCodes_cons, DecoderAcc.consumeCodes_append]
      rw [consume_encodePartrecNatCodes consCode zeroCode oneCode
        hconsZero hconsOne hzeroOne]
      rw [ih]
      simp [List.append_assoc]

/-- Decode a halted `ToPartrec` main stack. Delimiters terminate numbers, so
the last delimiter has already written the last output and no final flush is
performed. -/
def compilePartrecOutputCodec
    (outputStack consCode zeroCode oneCode : ℕ) : Com :=
  seqs [
    .assign outputIndexVar (.var (topName outputStack)),
    .assign outputValueVar (.lit 0),
    .assign outputPlaceVar (.lit 1),
    .assign outputHaveVar (.lit 1),
    .while (.lt (.lit 0) (.var outputIndexVar)) (seqs [
      .assign outputIndexVar
        (.sub (.var outputIndexVar) (.lit 1)),
      .assign outputCodeVar
        (.get (stackName outputStack) (.var outputIndexVar)),
      consumeOutputSymbol consCode zeroCode oneCode])]

theorem compilePartrecOutputCodec_correct
    (outputStack consCode zeroCode oneCode : ℕ)
    (hconsZero : consCode ≠ zeroCode)
    (hconsOne : consCode ≠ oneCode)
    (hzeroOne : zeroCode ≠ oneCode)
    (σ : Env) (x : List ℕ)
    (htop : σ.vars (topName outputStack) =
      (encodePartrecListCodes consCode zeroCode oneCode x).length)
    (hstack : (σ.arrs (stackName outputStack)).take
        (encodePartrecListCodes consCode zeroCode oneCode x).length =
      (encodePartrecListCodes consCode zeroCode oneCode x).reverse) :
    ∃ σ' cost,
      BigStep (compilePartrecOutputCodec outputStack consCode zeroCode oneCode)
        σ σ' cost ∧
      cost ≤ 29 *
        (encodePartrecListCodes consCode zeroCode oneCode x).length + 13 ∧
      σ'.out = σ.out ++ x := by
  let codes := encodePartrecListCodes consCode zeroCode oneCode x
  let σ₁ := σ.setVar outputIndexVar codes.length
  have hindex : BigStep
      (.assign outputIndexVar (.var (topName outputStack))) σ σ₁ 2 := by
    apply BigStep.assign
    simp [Expr.eval, σ₁, codes, htop]
  let σ₂ := σ₁.setVar outputValueVar 0
  have hvalue : BigStep (.assign outputValueVar (.lit 0)) σ₁ σ₂ 2 :=
    BigStep.assign rfl
  let σ₃ := σ₂.setVar outputPlaceVar 1
  have hplace : BigStep (.assign outputPlaceVar (.lit 1)) σ₂ σ₃ 2 :=
    BigStep.assign rfl
  let σ₄ := σ₃.setVar outputHaveVar 1
  have hactive : BigStep (.assign outputHaveVar (.lit 1)) σ₃ σ₄ 2 :=
    BigStep.assign rfl
  let d₀ : DecoderAcc :=
    { out := σ.out, value := 0, place := 1, active := 1 }
  have hmatch₄ : d₀.Matches σ₄ := by
    simp [d₀, DecoderAcc.Matches, σ₄, σ₃, σ₂, σ₁, Env.setVar]
  have hindex₄ : σ₄.vars outputIndexVar = codes.length := by
    simp [σ₄, σ₃, σ₂, σ₁, Env.setVar, outputIndexVar,
      outputValueVar, outputPlaceVar, outputHaveVar]
  have hstack₄ : (σ₄.arrs (stackName outputStack)).take codes.length =
      codes.reverse := by
    simpa [σ₄, σ₃, σ₂, σ₁, codes] using hstack
  obtain ⟨σ₅, loopCost, hloop, hloopBound, hfinalIndex, hmatch₅⟩ :=
    outputLoop_correct outputStack consCode zeroCode oneCode σ₄ codes d₀
      hindex₄ hstack₄ hmatch₄
  have hrun := BigStep.seq hindex (BigStep.seq hvalue (BigStep.seq hplace
    (BigStep.seq hactive (BigStep.seq hloop (BigStep.skip (σ := σ₅))))))
  refine ⟨σ₅, 2 + 2 + 2 + 2 + loopCost + 1, ?_, ?_, ?_⟩
  · convert hrun using 1 <;>
      simp [compilePartrecOutputCodec, seqs] <;> omega
  · dsimp [codes]
    dsimp [codes] at hloopBound
    omega
  · have hdecoded := consume_encodePartrecListCodes
      consCode zeroCode oneCode hconsZero hconsOne hzeroOne σ.out x
    calc
      σ₅.out = (d₀.consumeCodes consCode zeroCode codes).out := hmatch₅.1
      _ = σ.out ++ x := by
        have h := congrArg DecoderAcc.out hdecoded
        simpa [d₀, codes] using h

open PartrecFiniteTM2 in
theorem compilePartrecOutputCodec_haltList (c : ToPartrec.Code)
    (y : List ℕ) (σ : Env) (capacity : ℕ → ℕ)
    (hfinal : StacksWithin (FinTM2.availableSymbols (machine c))
      (Turing.haltList (machine c) (trList y)).stk)
    (hrep : NumericRep σ capacity
      (FinTM2.encodeNumericState (machine c)
        (Turing.haltList (machine c) (trList y)) hfinal))
    (hout : σ.out = []) :
    ∃ σ' cost,
      BigStep (compilePartrecOutputCodec
        (@finCode (machine c).K (machine c).kFin
          (machine c).kDecidableEq (machine c).k₁)
        (symbolCode c .cons) (symbolCode c .bit0) (symbolCode c .bit1))
        σ σ' cost ∧
      cost ≤ 29 * (encodePartrecListCodes (symbolCode c .cons)
        (symbolCode c .bit0) (symbolCode c .bit1) y).length + 13 ∧
      σ'.out = y := by
  let tm := machine c
  letI := tm.ΛFin
  letI : DecidableEq tm.Λ := Classical.decEq _
  let stack := @finCode tm.K tm.kFin tm.kDecidableEq tm.k₁
  let codes := encodePartrecListCodes (symbolCode c .cons)
    (symbolCode c .bit0) (symbolCode c .bit1) y
  have havail : ∀ a ∈ trList y,
      (⟨tm.k₁, a⟩ : Σ k, tm.Γ k) ∈ FinTM2.availableSymbols tm := by
    intro a ha
    exact hfinal tm.k₁ a (by simpa [tm, Turing.haltList] using ha)
  have hcodes : FinTM2.codeStack tm tm.k₁ (trList y) havail = codes := by
    simpa [tm, codes] using codeStack_trList c y havail
  have hstackRep := hrep.2.2 stack
  rw [FinTM2.encodeNumericState_stack] at hstackRep
  have hstackRep' : StackRep σ stack (capacity stack)
      (FinTM2.codeStack tm tm.k₁ (trList y) havail) := by
    simpa [Turing.haltList] using hstackRep
  have htop : σ.vars (topName stack) = codes.length := by
    rw [hstackRep'.1, hcodes]
  have hstack : (σ.arrs (stackName stack)).take codes.length =
      codes.reverse := by
    have hp := hstackRep'.2.2
    rw [hcodes] at hp
    exact hp
  rcases symbolCodes_pairwise c with ⟨hconsZero, hconsOne, hzeroOne⟩
  obtain ⟨σ', cost, hrun, hcost, hout'⟩ :=
    compilePartrecOutputCodec_correct stack
      (symbolCode c .cons) (symbolCode c .bit0) (symbolCode c .bit1)
      hconsZero hconsOne hzeroOne σ y htop hstack
  refine ⟨σ', cost, by simpa [tm, stack] using hrun, ?_, ?_⟩
  · simpa [codes] using hcost
  · simpa [hout] using hout'

open PartrecFiniteTM2 in
noncomputable def compilePartrecNativeMachine (c : ToPartrec.Code) : Com :=
  let tm := machine c
  let stack := @finCode tm.K tm.kFin tm.kDecidableEq tm.k₀
  seqs [
    compilePartrecInputCodec stack
      (symbolCode c .cons) (symbolCode c .bit0) (symbolCode c .bit1)
      (@finCode tm.σ tm.σFin (Classical.decEq tm.σ) tm.initialState)
      (@finCode tm.Λ tm.ΛFin (Classical.decEq tm.Λ) tm.main),
    FinTM2.compileMachine tm,
    compilePartrecOutputCodec stack
      (symbolCode c .cons) (symbolCode c .bit0) (symbolCode c .bit1)]

open PartrecFiniteTM2 in
theorem compilePartrecNativeMachine_safeRun (c : ToPartrec.Code)
    (x y : List ℕ) (capacity : ℕ → ℕ) (ext : String → ℕ)
    (hrun : SafeRun (machine c) capacity
      (Turing.initList (machine c) (trList (x.length :: x)))
      (Turing.haltList (machine c) (trList y)))
    (hstackLengths : ∀ j, ext (stackName j) = capacity j)
    (hscratch : (encodePartrecListCodes (symbolCode c .cons)
      (symbolCode c .bit0) (symbolCode c .bit1)
      (x.length :: x)).length ≤ ext scratchName)
    (hinputCapacity : (encodePartrecListCodes (symbolCode c .cons)
      (symbolCode c .bit0) (symbolCode c .bit1)
      (x.length :: x)).length ≤
        capacity (@finCode (machine c).K (machine c).kFin
          (machine c).kDecidableEq (machine c).k₀))
    (htableLengths : ∀ name values,
      (name, values) ∈ (FinTM2.compileDispatcher (machine c) 0).tables →
      ext name = values.length) :
    ∃ σ' cost,
      BigStep (compilePartrecNativeMachine c)
        (initEnv ext (x.length :: x)) σ' cost ∧
      cost ≤
        ((29 * x.length.bits.length + 18 + encodePartrecInputLoopCost x) +
          19 * (encodePartrecListCodes (symbolCode c .cons)
            (symbolCode c .bit0) (symbolCode c .bit1)
            (x.length :: x)).length + 14) +
        (initializeTablesCost (FinTM2.compileDispatcher (machine c) 0).tables +
          (1 + Cond.size (.lt (.lit 0) (.var labelVar)) +
            maxCost (FinTM2.compileDispatcher (machine c) 0).com) * hrun.steps +
          (1 + Cond.size (.lt (.lit 0) (.var labelVar)))) +
        (29 * (encodePartrecListCodes (symbolCode c .cons)
          (symbolCode c .bit0) (symbolCode c .bit1) y).length + 13) + 1 ∧
      σ'.out = y := by
  let tm := machine c
  let input := trList (x.length :: x)
  let output := trList y
  let hc := FinTM2.initList_stacksWithin tm input
  obtain ⟨σ₁, preCost, hpre, hpreCost, hpreRep⟩ :=
    compilePartrecInputCodec_initialRep c capacity ext x hstackLengths
      hscratch hinputCapacity
  have hzero : ∀ name values,
      (name, values) ∈ (FinTM2.compileDispatcher tm 0).tables →
      σ₁.arrs name = List.replicate values.length 0 := by
    intro name values hm
    have hname := @compileLabelList_tables_name tm tm.ΛFin
      (Classical.decEq tm.Λ) (FinTM2.labelList tm) 0 name values
      (by simpa [FinTM2.compileDispatcher] using hm)
    obtain ⟨i, rfl⟩ := hname
    rw [hpre.arrs_eq]
    · simp [initEnv, htableLengths (tableName i) values hm]
    · simp [compilePartrecInputCodec,
        encodeNativePartrecInputToScratch, encodePartrecInputLoop,
        encodePartrecInputBody, encodeBitsLoop, encodeBitsBody,
        appendScratch, reverseScratchIntoStack, reverseScratchLoop,
        reverseScratchBody, seqs, Com.warrs,
        (scratchName_ne_tableName i).symm,
        (stackName_ne_tableName _ i).symm]
  obtain ⟨σ₂, coreCost, hcore, hcoreCost, hfinal, hfinalRep, htables⟩ :=
    FinTM2.compileMachine_safeRun tm capacity
      (Turing.initList tm input) (Turing.haltList tm output) hc hrun σ₁
      (by simpa [tm, input, hc] using hpreRep) hzero
  have hcoreOut : σ₂.out = [] := by
    rw [hcore.out_eq]
    · rw [hpre.out_eq]
      · rfl
      · simp [compilePartrecInputCodec,
          encodeNativePartrecInputToScratch, encodePartrecInputLoop,
          encodePartrecInputBody, encodeBitsLoop, encodeBitsBody,
          appendScratch, reverseScratchIntoStack, reverseScratchLoop,
          reverseScratchBody, seqs, Com.NoWrite]
    · exact FinTM2.compileMachine_noWrite tm
  obtain ⟨σ₃, outCost, houtRun, houtCost, houtput⟩ :=
    compilePartrecOutputCodec_haltList c y σ₂ capacity
      (by simpa [tm, output] using hfinal)
      (by simpa [tm, output] using hfinalRep) hcoreOut
  have hall := BigStep.seq hpre (BigStep.seq hcore
    (BigStep.seq houtRun (BigStep.skip (σ := σ₃))))
  refine ⟨σ₃, preCost + coreCost + outCost + 1, ?_, ?_, houtput⟩
  · simpa only [compilePartrecNativeMachine, seqs, Nat.add_assoc] using hall
  · rw [hpreCost]
    have hcoreCost' : coreCost ≤
        initializeTablesCost
            (FinTM2.compileDispatcher (machine c) 0).tables +
          (1 + Cond.size (.lt (.lit 0) (.var labelVar)) +
            maxCost (FinTM2.compileDispatcher (machine c) 0).com) *
              hrun.steps +
          (1 + Cond.size (.lt (.lit 0) (.var labelVar))) := by
      simpa [tm] using hcoreCost
    omega

end Lax20Proofs.Computability.PartrecNativeCodec
