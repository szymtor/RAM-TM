import Lax51Proofs.TMToRam.IOCompiler

namespace Lax51Proofs.TMToRam

open Lax13Proofs.Imp

@[simp] theorem outputValueVar_ne_outputPlaceVar : outputValueVar ≠ outputPlaceVar := by
  decide

@[simp] theorem outputPlaceVar_ne_outputValueVar : outputPlaceVar ≠ outputValueVar := by
  decide

@[simp] theorem outputValueVar_ne_outputHaveVar : outputValueVar ≠ outputHaveVar := by
  decide

@[simp] theorem outputHaveVar_ne_outputValueVar : outputHaveVar ≠ outputValueVar := by
  decide

@[simp] theorem outputPlaceVar_ne_outputHaveVar : outputPlaceVar ≠ outputHaveVar := by
  decide

@[simp] theorem outputHaveVar_ne_outputPlaceVar : outputHaveVar ≠ outputPlaceVar := by
  decide

@[simp] theorem outputIndexVar_ne_outputCodeVar : outputIndexVar ≠ outputCodeVar := by
  decide

@[simp] theorem outputCodeVar_ne_outputIndexVar : outputCodeVar ≠ outputIndexVar := by
  decide

structure DecoderAcc where
  out : List ℕ
  value : ℕ
  place : ℕ
  active : ℕ

def DecoderAcc.Matches (d : DecoderAcc) (σ : Env) : Prop :=
  σ.out = d.out ∧
  σ.vars outputValueVar = d.value ∧
  σ.vars outputPlaceVar = d.place ∧
  σ.vars outputHaveVar = d.active

def DecoderAcc.consume (separatorCode zeroCode code : ℕ)
    (d : DecoderAcc) : DecoderAcc :=
  if code = separatorCode then
    { out := if d.active = 0 then d.out else d.out ++ [d.value]
      value := 0, place := 1, active := 1 }
  else if code = zeroCode then
    { d with place := d.place * 2 }
  else
    { d with value := d.value + d.place, place := d.place * 2 }

def DecoderAcc.flush (d : DecoderAcc) : List ℕ :=
  if d.active = 0 then d.out else d.out ++ [d.value]

theorem consumeOutputSymbol_correct (separatorCode zeroCode oneCode code : ℕ)
    (σ : Env) (d : DecoderAcc)
    (hcode : σ.vars outputCodeVar = code)
    (hmatch : d.Matches σ) :
    ∃ σ' cost,
      BigStep (consumeOutputSymbol separatorCode zeroCode oneCode) σ σ' cost ∧
      cost ≤ 17 ∧
      (d.consume separatorCode zeroCode code).Matches σ' := by
  rcases hmatch with ⟨hout, hvalue, hplace, hhave⟩
  by_cases hsep : code = separatorCode
  · have houter : Cond.eval
        (.eq (.var outputCodeVar) (.lit separatorCode)) σ = some true := by
      simp [Cond.eval, Expr.eval, hcode, hsep]
    by_cases hnone : d.active = 0
    · have hinner : Cond.eval
          (.eq (.var outputHaveVar) (.lit 0)) σ = some true := by
        simp [Cond.eval, Expr.eval, hhave, hnone]
      let σ₀ := σ
      have hoptional : BigStep
          (.ite (.eq (.var outputHaveVar) (.lit 0)) .skip
            (.write (.var outputValueVar))) σ σ₀ 5 := by
        simpa [σ₀, Cond.size, Expr.size] using
          BigStep.ite_true hinner (BigStep.skip (σ := σ))
      let σ₁ := σ₀.setVar outputValueVar 0
      have hv : BigStep (.assign outputValueVar (.lit 0)) σ₀ σ₁ 2 :=
        BigStep.assign rfl
      let σ₂ := σ₁.setVar outputPlaceVar 1
      have hp : BigStep (.assign outputPlaceVar (.lit 1)) σ₁ σ₂ 2 :=
        BigStep.assign rfl
      let σ₃ := σ₂.setVar outputHaveVar 1
      have hh : BigStep (.assign outputHaveVar (.lit 1)) σ₂ σ₃ 2 :=
        BigStep.assign rfl
      have hbranch := BigStep.seq hoptional (BigStep.seq hv
        (BigStep.seq hp (BigStep.seq hh (BigStep.skip (σ := σ₃)))))
      refine ⟨σ₃, 4 + 12, ?_, by omega, ?_⟩
      · simpa [consumeOutputSymbol, seqs, Cond.size, Expr.size] using
          BigStep.ite_true houter hbranch
      · simp [DecoderAcc.consume, DecoderAcc.Matches, hsep, hnone,
          σ₃, σ₂, σ₁, σ₀, Env.setVar, hout,
          outputValueVar_ne_outputPlaceVar, outputValueVar_ne_outputHaveVar,
          outputPlaceVar_ne_outputHaveVar]
    · have hinner : Cond.eval
          (.eq (.var outputHaveVar) (.lit 0)) σ = some false := by
        simp [Cond.eval, Expr.eval, hhave, hnone]
      let σ₀ := { σ with out := σ.out ++ [d.value] }
      have hoptional : BigStep
          (.ite (.eq (.var outputHaveVar) (.lit 0)) .skip
            (.write (.var outputValueVar))) σ σ₀ 6 := by
        have hw : BigStep (.write (.var outputValueVar)) σ σ₀ 2 := by
          simpa [σ₀, hvalue] using
            (BigStep.write (σ := σ) (e := .var outputValueVar)
              (v := d.value) (by simp [Expr.eval, hvalue]))
        simpa [Cond.size, Expr.size] using BigStep.ite_false hinner hw
      let σ₁ := σ₀.setVar outputValueVar 0
      have hv : BigStep (.assign outputValueVar (.lit 0)) σ₀ σ₁ 2 :=
        BigStep.assign rfl
      let σ₂ := σ₁.setVar outputPlaceVar 1
      have hp : BigStep (.assign outputPlaceVar (.lit 1)) σ₁ σ₂ 2 :=
        BigStep.assign rfl
      let σ₃ := σ₂.setVar outputHaveVar 1
      have hh : BigStep (.assign outputHaveVar (.lit 1)) σ₂ σ₃ 2 :=
        BigStep.assign rfl
      have hbranch := BigStep.seq hoptional (BigStep.seq hv
        (BigStep.seq hp (BigStep.seq hh (BigStep.skip (σ := σ₃)))))
      refine ⟨σ₃, 4 + 13, ?_, by omega, ?_⟩
      · simpa [consumeOutputSymbol, seqs, Cond.size, Expr.size] using
          BigStep.ite_true houter hbranch
      · simp [DecoderAcc.consume, DecoderAcc.Matches, hsep, hnone,
          σ₃, σ₂, σ₁, σ₀, Env.setVar, hout,
          outputValueVar_ne_outputPlaceVar, outputValueVar_ne_outputHaveVar,
          outputPlaceVar_ne_outputHaveVar]
  · have houter : Cond.eval
        (.eq (.var outputCodeVar) (.lit separatorCode)) σ = some false := by
      simp [Cond.eval, Expr.eval, hcode, hsep]
    by_cases hzero : code = zeroCode
    · have hinner : Cond.eval
          (.eq (.var outputCodeVar) (.lit zeroCode)) σ = some true := by
        simp [Cond.eval, Expr.eval, hcode, hzero]
      have hzeroSep : zeroCode ≠ separatorCode := by
        intro heq
        apply hsep
        exact hzero.trans heq
      let σ₁ := σ.setVar outputPlaceVar (d.place * 2)
      have hp : BigStep
          (.assign outputPlaceVar
            (.mul (.var outputPlaceVar) (.lit 2))) σ σ₁ 4 := by
        apply BigStep.assign
        simp [Expr.eval, σ₁, hplace]
      have hbranch : BigStep
          (.ite (.eq (.var outputCodeVar) (.lit zeroCode))
            (.assign outputPlaceVar
              (.mul (.var outputPlaceVar) (.lit 2)))
            (seqs [
              .assign outputValueVar
                (.add (.var outputValueVar) (.var outputPlaceVar)),
              .assign outputPlaceVar
                (.mul (.var outputPlaceVar) (.lit 2))])) σ σ₁ 8 := by
        simpa [Cond.size, Expr.size] using BigStep.ite_true hinner hp
      refine ⟨σ₁, 4 + 8, ?_, by omega, ?_⟩
      · simpa [consumeOutputSymbol, Cond.size, Expr.size] using
          BigStep.ite_false houter hbranch
      · simp [DecoderAcc.consume, DecoderAcc.Matches, hsep, hzero,
          hzeroSep, σ₁, Env.setVar, hout, hvalue, hplace, hhave,
          outputValueVar_ne_outputPlaceVar, outputValueVar_ne_outputHaveVar,
          outputPlaceVar_ne_outputHaveVar]
    · have hinner : Cond.eval
          (.eq (.var outputCodeVar) (.lit zeroCode)) σ = some false := by
        simp [Cond.eval, Expr.eval, hcode, hzero]
      let σ₁ := σ.setVar outputValueVar (d.value + d.place)
      have hv : BigStep
          (.assign outputValueVar
            (.add (.var outputValueVar) (.var outputPlaceVar))) σ σ₁ 4 := by
        apply BigStep.assign
        simp [Expr.eval, σ₁, hvalue, hplace]
      let σ₂ := σ₁.setVar outputPlaceVar (d.place * 2)
      have hp : BigStep
          (.assign outputPlaceVar
            (.mul (.var outputPlaceVar) (.lit 2))) σ₁ σ₂ 4 := by
        apply BigStep.assign
        simp [Expr.eval, σ₂, σ₁, hplace,
          outputValueVar_ne_outputPlaceVar]
      have helse := BigStep.seq hv (BigStep.seq hp (BigStep.skip (σ := σ₂)))
      have hbranch : BigStep
          (.ite (.eq (.var outputCodeVar) (.lit zeroCode))
            (.assign outputPlaceVar
              (.mul (.var outputPlaceVar) (.lit 2)))
            (seqs [
              .assign outputValueVar
                (.add (.var outputValueVar) (.var outputPlaceVar)),
              .assign outputPlaceVar
                (.mul (.var outputPlaceVar) (.lit 2))])) σ σ₂ 13 := by
        simpa [seqs, Cond.size, Expr.size] using BigStep.ite_false hinner helse
      refine ⟨σ₂, 4 + 13, ?_, by omega, ?_⟩
      · simpa [consumeOutputSymbol, Cond.size, Expr.size] using
          BigStep.ite_false houter hbranch
      · simp [DecoderAcc.consume, DecoderAcc.Matches, hsep, hzero,
          σ₂, σ₁, Env.setVar, hout, hvalue, hplace, hhave,
          outputValueVar_ne_outputPlaceVar, outputValueVar_ne_outputHaveVar,
          outputPlaceVar_ne_outputHaveVar]

def DecoderAcc.consumeCodes (separatorCode zeroCode : ℕ) :
    List ℕ → DecoderAcc → DecoderAcc
  | [], d => d
  | code :: codes, d =>
      consumeCodes separatorCode zeroCode codes
        (d.consume separatorCode zeroCode code)

theorem reverse_prefix_getD_head (arr : List ℕ) (a : ℕ) (rest : List ℕ)
    (hprefix : arr.take (a :: rest).length = (a :: rest).reverse) :
    arr.getD rest.length 0 = a := by
  have hi : rest.length < (a :: rest).length := by simp
  have h := congrArg (fun l : List ℕ => l[rest.length]?.getD 0) hprefix
  simpa [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi,
    List.reverse_cons] using h

theorem reverse_prefix_tail (arr : List ℕ) (a : ℕ) (rest : List ℕ)
    (hprefix : arr.take (a :: rest).length = (a :: rest).reverse) :
    arr.take rest.length = rest.reverse := by
  have h := congrArg (List.take rest.length) hprefix
  simpa [List.take_take, List.reverse_cons] using h

/-- The output loop walks the represented logical stack from head to tail
and realizes the pure decoder fold. -/
theorem outputLoop_correct (outputStack separatorCode zeroCode oneCode : ℕ)
    (σ : Env) (codes : List ℕ) (d : DecoderAcc)
    (hindex : σ.vars outputIndexVar = codes.length)
    (hstack : (σ.arrs (stackName outputStack)).take codes.length =
      codes.reverse)
    (hmatch : d.Matches σ) :
    ∃ σ' cost,
      BigStep
        (.while (.lt (.lit 0) (.var outputIndexVar)) (seqs [
          .assign outputIndexVar
            (.sub (.var outputIndexVar) (.lit 1)),
          .assign outputCodeVar
            (.get (stackName outputStack) (.var outputIndexVar)),
          consumeOutputSymbol separatorCode zeroCode oneCode]))
        σ σ' cost ∧
      cost ≤ 29 * codes.length + 4 ∧
      σ'.vars outputIndexVar = 0 ∧
      (d.consumeCodes separatorCode zeroCode codes).Matches σ' := by
  induction codes generalizing σ d with
  | nil =>
      refine ⟨σ, 4, ?_, by simp, ?_, ?_⟩
      · exact BigStep.while_false
          (by simp [Cond.eval, Expr.eval, hindex])
      · simpa using hindex
      · simpa [DecoderAcc.consumeCodes] using hmatch
  | cons a rest ih =>
      have hpositive : 0 < σ.vars outputIndexVar := by simp [hindex]
      let σ₁ := σ.setVar outputIndexVar rest.length
      have hdec : BigStep
          (.assign outputIndexVar
            (.sub (.var outputIndexVar) (.lit 1))) σ σ₁ 4 := by
        apply BigStep.assign
        simp [Expr.eval, σ₁, hindex]
      have hgetD : (σ.arrs (stackName outputStack)).getD rest.length 0 = a :=
        reverse_prefix_getD_head _ a rest hstack
      have hget : (σ.arrs (stackName outputStack))[rest.length]? = some a := by
        have hlen : rest.length < (σ.arrs (stackName outputStack)).length := by
          by_contra hn
          have harrle : (σ.arrs (stackName outputStack)).length ≤ rest.length :=
            Nat.le_of_not_gt hn
          have heq := congrArg List.length hstack
          simp only [List.length_take, List.length_reverse,
            List.length_cons] at heq
          rw [Nat.min_eq_right (by omega)] at heq
          omega
        have hd :
            (σ.arrs (stackName outputStack))[rest.length]?.getD 0 = a := by
          simpa [List.getD_eq_getElem?_getD] using hgetD
        calc
          (σ.arrs (stackName outputStack))[rest.length]? =
              some ((σ.arrs (stackName outputStack))[rest.length]?.getD 0) :=
            getElem?_eq_getD (d := 0) hlen
          _ = some a := congrArg some hd
      let σ₂ := σ₁.setVar outputCodeVar a
      have hload : BigStep
          (.assign outputCodeVar
            (.get (stackName outputStack) (.var outputIndexVar))) σ₁ σ₂ 3 := by
        apply BigStep.assign
        simp [Expr.eval, σ₁, σ₂, hget]
      have hmatch₂ : d.Matches σ₂ := by
        rcases hmatch with ⟨ho, hv, hp, hh⟩
        exact ⟨ho, by simpa [σ₂, σ₁, Env.setVar] using hv,
          by simpa [σ₂, σ₁, Env.setVar] using hp,
          by simpa [σ₂, σ₁, Env.setVar] using hh⟩
      obtain ⟨σ₃, consumeCost, hconsume, hconsumeBound, hmatch₃⟩ :=
        consumeOutputSymbol_correct separatorCode zeroCode oneCode a σ₂ d
          (by simp [σ₂, Env.setVar]) hmatch₂
      have hbody := BigStep.seq hdec (BigStep.seq hload
        (BigStep.seq hconsume (BigStep.skip (σ := σ₃))))
      have hbody' : BigStep (seqs [
          .assign outputIndexVar
            (.sub (.var outputIndexVar) (.lit 1)),
          .assign outputCodeVar
            (.get (stackName outputStack) (.var outputIndexVar)),
          consumeOutputSymbol separatorCode zeroCode oneCode])
          σ σ₃ (4 + 3 + consumeCost + 1) := by
        convert hbody using 1 <;> simp [seqs] <;> omega
      have hindex₃ : σ₃.vars outputIndexVar = rest.length := by
        rw [hconsume.vars_eq]
        · simp [σ₂, σ₁, Env.setVar]
        · simp [consumeOutputSymbol, seqs, Com.wvars, outputIndexVar,
            outputValueVar, outputPlaceVar, outputHaveVar]
      have hstack₃ :
          (σ₃.arrs (stackName outputStack)).take rest.length =
            rest.reverse := by
        rw [hconsume.arrs_eq]
        · simpa [σ₂, σ₁] using reverse_prefix_tail _ a rest hstack
        · simp [consumeOutputSymbol, seqs, Com.warrs]
      obtain ⟨σ', tailCost, htail, htailBound, hfinalIndex, hfinalMatch⟩ :=
        ih σ₃ (d.consume separatorCode zeroCode a) hindex₃ hstack₃ hmatch₃
      refine ⟨σ', 4 + (4 + 3 + consumeCost + 1) + tailCost, ?_,
        ?_, hfinalIndex, ?_⟩
      · exact BigStep.while_true
          (by simp [Cond.eval, Expr.eval, hpositive]) hbody' htail
      · simp only [List.length_cons]
        omega
      · simpa [DecoderAcc.consumeCodes] using hfinalMatch

def bitsValue : List Bool → ℕ
  | [] => 0
  | b :: bits => (if b then 1 else 0) + 2 * bitsValue bits

theorem bitsValue_bits (n : ℕ) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      simp [bitsValue, ih, Nat.bit]
      cases b <;> simp [Nat.bit, Nat.add_comm]

theorem DecoderAcc.consumeCodes_append (separatorCode zeroCode : ℕ)
    (xs ys : List ℕ) (d : DecoderAcc) :
    d.consumeCodes separatorCode zeroCode (xs ++ ys) =
      (d.consumeCodes separatorCode zeroCode xs).consumeCodes
        separatorCode zeroCode ys := by
  induction xs generalizing d with
  | nil => rfl
  | cons a xs ih =>
      simp [DecoderAcc.consumeCodes, ih]

theorem DecoderAcc.consume_bit_codes (separatorCode zeroCode oneCode : ℕ)
    (hsepZero : separatorCode ≠ zeroCode)
    (hsepOne : separatorCode ≠ oneCode)
    (hzeroOne : zeroCode ≠ oneCode) (bits : List Bool) (d : DecoderAcc) :
    d.consumeCodes separatorCode zeroCode
        (bits.map (boolDigitCode zeroCode oneCode)) =
      { d with
        value := d.value + d.place * bitsValue bits
        place := d.place * 2 ^ bits.length } := by
  induction bits generalizing d with
  | nil => simp [DecoderAcc.consumeCodes, bitsValue]
  | cons b bits ih =>
      rw [List.map_cons]
      simp only [DecoderAcc.consumeCodes]
      cases b with
      | false =>
          have hcode : boolDigitCode zeroCode oneCode false = zeroCode := rfl
          rw [hcode]
          have hconsumed : d.consume separatorCode zeroCode zeroCode =
              if zeroCode = separatorCode then
                { out := if d.active = 0 then d.out else d.out ++ [d.value]
                  value := 0, place := 1, active := 1 }
              else { d with place := d.place * 2 } := by
            simp [DecoderAcc.consume]
          rw [hconsumed]
          have hzs : zeroCode ≠ separatorCode := hsepZero.symm
          rw [if_neg hzs, ih]
          simp [bitsValue, Nat.pow_succ, Nat.mul_assoc,
            Nat.mul_left_comm, Nat.mul_comm]
          <;> ring
      | true =>
          have hcode : boolDigitCode zeroCode oneCode true = oneCode := rfl
          rw [hcode]
          have hos : oneCode ≠ separatorCode := hsepOne.symm
          have hoz : oneCode ≠ zeroCode := hzeroOne.symm
          rw [show d.consume separatorCode zeroCode oneCode =
              { { d with value := d.value + d.place } with
                place := d.place * 2 } by
            simp [DecoderAcc.consume, hos, hoz]]
          rw [ih]
          simp [bitsValue, Nat.pow_succ, Nat.mul_assoc,
            Nat.mul_left_comm, Nat.mul_comm, Nat.mul_add]
          <;> ring

theorem DecoderAcc.consume_encodeNat (separatorCode zeroCode oneCode n : ℕ)
    (hsepZero : separatorCode ≠ zeroCode)
    (hsepOne : separatorCode ≠ oneCode)
    (hzeroOne : zeroCode ≠ oneCode)
    (d : DecoderAcc) :
    d.consumeCodes separatorCode zeroCode
        (encodeNatCodes separatorCode zeroCode oneCode n) =
      { out := d.flush, value := n,
        place := 2 ^ n.bits.length, active := 1 } := by
  rw [show encodeNatCodes separatorCode zeroCode oneCode n =
      separatorCode :: n.bits.map (boolDigitCode zeroCode oneCode) by rfl]
  simp only [DecoderAcc.consumeCodes]
  have hseparator : d.consume separatorCode zeroCode separatorCode =
      { out := d.flush, value := 0, place := 1, active := 1 } := by
    simp [DecoderAcc.consume, DecoderAcc.flush]
  rw [hseparator, DecoderAcc.consume_bit_codes separatorCode zeroCode oneCode
    hsepZero hsepOne hzeroOne, bitsValue_bits]
  simp

theorem DecoderAcc.flush_consume_encodeWordCodes
    (separatorCode zeroCode oneCode : ℕ)
    (hsepZero : separatorCode ≠ zeroCode)
    (hsepOne : separatorCode ≠ oneCode)
    (hzeroOne : zeroCode ≠ oneCode)
    (x : List ℕ) (d : DecoderAcc) :
    (d.consumeCodes separatorCode zeroCode
      (encodeWordCodes separatorCode zeroCode oneCode x)).flush =
      d.flush ++ x := by
  induction x generalizing d with
  | nil => simp [encodeWordCodes, DecoderAcc.consumeCodes]
  | cons a x ih =>
      rw [show encodeWordCodes separatorCode zeroCode oneCode (a :: x) =
          encodeNatCodes separatorCode zeroCode oneCode a ++
            encodeWordCodes separatorCode zeroCode oneCode x by
        simp [encodeWordCodes]]
      rw [DecoderAcc.consumeCodes_append]
      rw [ih]
      rw [DecoderAcc.consume_encodeNat separatorCode zeroCode oneCode a
        hsepZero hsepOne hzeroOne]
      simp [DecoderAcc.flush, List.append_assoc]

theorem DecoderAcc.decode_encodeWordCodes
    (separatorCode zeroCode oneCode : ℕ)
    (hsepZero : separatorCode ≠ zeroCode)
    (hsepOne : separatorCode ≠ oneCode)
    (hzeroOne : zeroCode ≠ oneCode)
    (x : List ℕ) :
    (({ out := [], value := 0, place := 1, active := 0 } : DecoderAcc).consumeCodes
      separatorCode zeroCode
        (encodeWordCodes separatorCode zeroCode oneCode x)).flush = x := by
  simpa [DecoderAcc.flush] using
    DecoderAcc.flush_consume_encodeWordCodes separatorCode zeroCode oneCode
      hsepZero hsepOne hzeroOne x
      ({ out := [], value := 0, place := 1, active := 0 } : DecoderAcc)

theorem flushDecoder_correct (σ : Env) (d : DecoderAcc)
    (hmatch : d.Matches σ) :
    ∃ σ' cost,
      BigStep
        (.ite (.eq (.var outputHaveVar) (.lit 0)) .skip
          (.write (.var outputValueVar))) σ σ' cost ∧
      cost ≤ 6 ∧ σ'.out = d.flush := by
  rcases hmatch with ⟨hout, hvalue, hplace, hactive⟩
  by_cases hz : d.active = 0
  · refine ⟨σ, 5, ?_, by omega, ?_⟩
    · simpa [Cond.size, Expr.size] using BigStep.ite_true
        (by simp [Cond.eval, Expr.eval, hactive, hz])
        (BigStep.skip (σ := σ))
    · simp [DecoderAcc.flush, hz, hout]
  · let σ' := { σ with out := σ.out ++ [d.value] }
    have hw : BigStep (.write (.var outputValueVar)) σ σ' 2 := by
      simpa [σ', hvalue] using
        (BigStep.write (σ := σ) (e := .var outputValueVar) (v := d.value)
          (by simp [Expr.eval, hvalue]))
    refine ⟨σ', 6, ?_, by omega, ?_⟩
    · simpa [Cond.size, Expr.size] using BigStep.ite_false
        (by simp [Cond.eval, Expr.eval, hactive, hz]) hw
    · simp [σ', DecoderAcc.flush, hz, hout]

/-- End-to-end semantic theorem for the concrete output codec, expressed
through the pure decoder. -/
theorem compileOutputCodec_correct (outputStack separatorCode zeroCode
    oneCode : ℕ) (σ : Env) (codes : List ℕ)
    (htop : σ.vars (topName outputStack) = codes.length)
    (hstack : (σ.arrs (stackName outputStack)).take codes.length =
      codes.reverse) :
    ∃ σ' cost,
      BigStep (compileOutputCodec outputStack separatorCode zeroCode oneCode)
        σ σ' cost ∧
      cost ≤ 29 * codes.length + 19 ∧
      σ'.out =
        (({ out := σ.out, value := 0, place := 1, active := 0 } :
          DecoderAcc).consumeCodes separatorCode zeroCode codes).flush := by
  let σ₁ := σ.setVar outputIndexVar codes.length
  have hindex : BigStep
      (.assign outputIndexVar (.var (topName outputStack))) σ σ₁ 2 := by
    apply BigStep.assign
    simp [Expr.eval, σ₁, htop]
  let σ₂ := σ₁.setVar outputValueVar 0
  have hvalue : BigStep (.assign outputValueVar (.lit 0)) σ₁ σ₂ 2 :=
    BigStep.assign rfl
  let σ₃ := σ₂.setVar outputPlaceVar 1
  have hplace : BigStep (.assign outputPlaceVar (.lit 1)) σ₂ σ₃ 2 :=
    BigStep.assign rfl
  let σ₄ := σ₃.setVar outputHaveVar 0
  have hactive : BigStep (.assign outputHaveVar (.lit 0)) σ₃ σ₄ 2 :=
    BigStep.assign rfl
  let d₀ : DecoderAcc :=
    { out := σ.out, value := 0, place := 1, active := 0 }
  have hmatch₄ : d₀.Matches σ₄ := by
    simp [d₀, DecoderAcc.Matches, σ₄, σ₃, σ₂, σ₁, Env.setVar]
  have hindex₄ : σ₄.vars outputIndexVar = codes.length := by
    simp [σ₄, σ₃, σ₂, σ₁, Env.setVar, outputIndexVar,
      outputValueVar, outputPlaceVar, outputHaveVar]
  have hstack₄ : (σ₄.arrs (stackName outputStack)).take codes.length =
      codes.reverse := by simpa [σ₄, σ₃, σ₂, σ₁] using hstack
  obtain ⟨σ₅, loopCost, hloop, hloopBound, hfinalIndex, hmatch₅⟩ :=
    outputLoop_correct outputStack separatorCode zeroCode oneCode σ₄ codes d₀
      hindex₄ hstack₄ hmatch₄
  obtain ⟨σ₆, flushCost, hflush, hflushBound, hfinalOut⟩ :=
    flushDecoder_correct σ₅
      (d₀.consumeCodes separatorCode zeroCode codes) hmatch₅
  have hrun := BigStep.seq hindex (BigStep.seq hvalue (BigStep.seq hplace
    (BigStep.seq hactive (BigStep.seq hloop
      (BigStep.seq hflush (BigStep.skip (σ := σ₆)))))))
  refine ⟨σ₆, 2 + 2 + 2 + 2 + loopCost + flushCost + 1, ?_, ?_, ?_⟩
  · convert hrun using 1 <;> simp [compileOutputCodec, seqs] <;> omega
  · omega
  · simpa [d₀] using hfinalOut

theorem compileOutputCodec_encodeWordCodes (outputStack separatorCode zeroCode
    oneCode : ℕ)
    (hsepZero : separatorCode ≠ zeroCode)
    (hsepOne : separatorCode ≠ oneCode)
    (hzeroOne : zeroCode ≠ oneCode)
    (σ : Env) (x : List ℕ)
    (hout : σ.out = [])
    (htop : σ.vars (topName outputStack) =
      (encodeWordCodes separatorCode zeroCode oneCode x).length)
    (hstack : (σ.arrs (stackName outputStack)).take
        (encodeWordCodes separatorCode zeroCode oneCode x).length =
      (encodeWordCodes separatorCode zeroCode oneCode x).reverse) :
    ∃ σ' cost,
      BigStep (compileOutputCodec outputStack separatorCode zeroCode oneCode)
        σ σ' cost ∧
      cost ≤ 29 * (encodeWordCodes separatorCode zeroCode oneCode x).length + 19 ∧
      σ'.out = x := by
  obtain ⟨σ', cost, hrun, hcost, hout'⟩ :=
    compileOutputCodec_correct outputStack separatorCode zeroCode oneCode σ
      (encodeWordCodes separatorCode zeroCode oneCode x) htop hstack
  refine ⟨σ', cost, hrun, hcost, ?_⟩
  rw [hout']
  simpa [hout] using DecoderAcc.decode_encodeWordCodes separatorCode zeroCode
    oneCode hsepZero hsepOne hzeroOne x

theorem FinTM2.outputSymbolCodes_pairwise (tm : Turing.FinTM2)
    (outputAlphabet : tm.Γ tm.k₁ ≃ Lax51.BinaryWordEncoding.Symbol) :
    FinTM2.outputSymbolCode tm outputAlphabet .separator ≠
        FinTM2.outputSymbolCode tm outputAlphabet .zero ∧
      FinTM2.outputSymbolCode tm outputAlphabet .separator ≠
        FinTM2.outputSymbolCode tm outputAlphabet .one ∧
      FinTM2.outputSymbolCode tm outputAlphabet .zero ≠
        FinTM2.outputSymbolCode tm outputAlphabet .one := by
  have hinj := FinTM2.outputSymbolCode_injective tm outputAlphabet
  constructor
  · intro h
    have := hinj h
    contradiction
  constructor
  · intro h
    have := hinj h
    contradiction
  · intro h
    have := hinj h
    contradiction

/-- The decoder consumes exactly the output stack represented by a halted
typed TM configuration. -/
theorem FinTM2.compileOutputCodec_haltList (tm : Turing.FinTM2)
    (outputAlphabet : tm.Γ tm.k₁ ≃ Lax51.BinaryWordEncoding.Symbol)
    (y : List ℕ) (σ : Env) (capacity : ℕ → ℕ)
    (hfinal : StacksWithin (FinTM2.availableSymbols tm)
      (Turing.haltList tm (List.map outputAlphabet.invFun
        (Lax51.BinaryWordEncoding.encode y))).stk)
    (hrep : NumericRep σ capacity
      (FinTM2.encodeNumericState tm
        (Turing.haltList tm (List.map outputAlphabet.invFun
          (Lax51.BinaryWordEncoding.encode y))) hfinal))
    (hout : σ.out = []) :
    ∃ σ' cost,
      BigStep (compileOutputCodec
        (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₁)
        (FinTM2.outputSymbolCode tm outputAlphabet .separator)
        (FinTM2.outputSymbolCode tm outputAlphabet .zero)
        (FinTM2.outputSymbolCode tm outputAlphabet .one)) σ σ' cost ∧
      cost ≤ 29 * (Lax51.BinaryWordEncoding.encode y).length + 19 ∧
      σ'.out = y := by
  let stack := @finCode tm.K tm.kFin tm.kDecidableEq tm.k₁
  let codes := encodeWordCodes
    (FinTM2.outputSymbolCode tm outputAlphabet .separator)
    (FinTM2.outputSymbolCode tm outputAlphabet .zero)
    (FinTM2.outputSymbolCode tm outputAlphabet .one) y
  have havail : ∀ a ∈ (Lax51.BinaryWordEncoding.encode y).map
      outputAlphabet.invFun,
      (⟨tm.k₁, a⟩ : Σ k, tm.Γ k) ∈ FinTM2.availableSymbols tm := by
    intro a ha
    exact hfinal tm.k₁ a (by simpa [Turing.haltList] using ha)
  have hcodes : FinTM2.codeStack tm tm.k₁
      ((Lax51.BinaryWordEncoding.encode y).map outputAlphabet.invFun) havail =
      codes := by
    rw [FinTM2.codeStack_map_outputAlphabet tm outputAlphabet
      (Lax51.BinaryWordEncoding.encode y) havail]
    symm
    exact encodeWordCodes_eq_outputSymbolCodes tm outputAlphabet y
  have hhaltStack :
      (Turing.haltList tm (List.map outputAlphabet.invFun
        (Lax51.BinaryWordEncoding.encode y))).stk tm.k₁ =
        List.map outputAlphabet.invFun (Lax51.BinaryWordEncoding.encode y) := by
    simp [Turing.haltList]
  have hstackRep := hrep.2.2 stack
  rw [FinTM2.encodeNumericState_stack] at hstackRep
  have hstackRep' : StackRep σ stack (capacity stack)
      (FinTM2.codeStack tm tm.k₁
        (List.map outputAlphabet.invFun (Lax51.BinaryWordEncoding.encode y))
        havail) := by
    simpa [Turing.haltList] using hstackRep
  have htop : σ.vars (topName stack) = codes.length := by
    rw [hstackRep'.1, hcodes]
  have hstack : (σ.arrs (stackName stack)).take codes.length =
      codes.reverse := by
    have hp := hstackRep'.2.2
    rw [hcodes] at hp
    exact hp
  rcases FinTM2.outputSymbolCodes_pairwise tm outputAlphabet with
    ⟨hsepZero, hsepOne, hzeroOne⟩
  obtain ⟨σ', cost, hrun, hcost, hout'⟩ :=
    compileOutputCodec_encodeWordCodes stack
      (FinTM2.outputSymbolCode tm outputAlphabet .separator)
      (FinTM2.outputSymbolCode tm outputAlphabet .zero)
      (FinTM2.outputSymbolCode tm outputAlphabet .one)
      hsepZero hsepOne hzeroOne σ y hout htop hstack
  refine ⟨σ', cost, by simpa [stack] using hrun, ?_, hout'⟩
  have hcodesLength : codes.length =
      (Lax51.BinaryWordEncoding.encode y).length := by
    dsimp [codes]
    rw [encodeWordCodes_eq_outputSymbolCodes]
    simp
  change (encodeWordCodes
      (FinTM2.outputSymbolCode tm outputAlphabet .separator)
      (FinTM2.outputSymbolCode tm outputAlphabet .zero)
      (FinTM2.outputSymbolCode tm outputAlphabet .one) y).length = _
    at hcodesLength
  rw [hcodesLength] at hcost
  exact hcost

end Lax51Proofs.TMToRam
