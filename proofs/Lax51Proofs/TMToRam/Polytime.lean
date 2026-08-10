import Lax51Proofs.TMToRam.NativeBounded
import Lax51.RamPolytime
import Lax51.TuringPolytime

namespace Lax51Proofs.TMToRam

open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime
open Lax13.Ram Lax13Proofs.Imp Lax13Proofs.Compile
open Polynomial

/-- The forward polynomial-time simulation: every finite multi-tape Turing
machine running in polynomial time compiles to one uniform word-RAM program
with polynomial time and sufficient-word-length bounds. -/
theorem turingPolytime_to_ramPolytime {f : List ℕ → List ℕ}
    (hf : TuringPolytime f) : RamPolytime f := by
  rcases hf with ⟨H⟩
  let tm := H.tm
  let inputStack := @finCode tm.K tm.kFin tm.kDecidableEq tm.k₀
  let outputStack := @finCode tm.K tm.kFin tm.kDecidableEq tm.k₁
  let separatorIn := FinTM2.inputSymbolCode tm H.inputAlphabet .separator
  let zeroIn := FinTM2.inputSymbolCode tm H.inputAlphabet .zero
  let oneIn := FinTM2.inputSymbolCode tm H.inputAlphabet .one
  let separatorOut := FinTM2.outputSymbolCode tm H.outputAlphabet .separator
  let zeroOut := FinTM2.outputSymbolCode tm H.outputAlphabet .zero
  let oneOut := FinTM2.outputSymbolCode tm H.outputAlphabet .one
  let initialStateCode := @finCode tm.σ tm.σFin (Classical.decEq tm.σ) tm.initialState
  let mainLabelCode := @finCode tm.Λ tm.ΛFin (Classical.decEq tm.Λ) tm.main
  let cmd := FinTM2.compileNativeMachine tm inputStack outputStack separatorIn zeroIn oneIn
    separatorOut zeroOut oneOut initialStateCode mainLabelCode
  let layout := comCanonicalLayout cmd
  let growth := FinTM2.nativeBitGrowth tm inputStack outputStack separatorIn zeroIn oneIn
    separatorOut zeroOut oneOut initialStateCode mainLabelCode
  let guardCost := 1 + Cond.size (.lt (.lit 0) (.var labelVar))
  let coreCoeff := guardCost + maxCost (FinTM2.compileDispatcher tm 0).com
  let push := FinTM2.machinePushBudget tm tm.k₁
  let constantCost := 22 + initializeTablesCost (FinTM2.compileDispatcher tm 0).tables +
    guardCost + 19 + 1
  let costPoly : Polynomial ℕ :=
    C constantCost + C 99 * X + C (coreCoeff + 29 * push) * H.time
  let exponentPoly : Polynomial ℕ := X + C 1 + C growth * costPoly
  let wordPoly : Polynomial ℕ := exponentPoly + C (layoutBitOverhead layout)
  let ramTimePoly : Polynomial ℕ := C layout.const * costPoly
  have hgrowthOne : 1 ≤ growth := by
    apply comOneLeBitGrowth
    simpa [growth, cmd, tm, inputStack, outputStack, separatorIn, zeroIn, oneIn,
      separatorOut, zeroOut, oneOut, initialStateCode, mainLabelCode] using
      FinTM2.compileNativeMachine_bitGrowth tm inputStack outputStack separatorIn
        zeroIn oneIn separatorOut zeroOut oneOut initialStateCode mainLabelCode
  refine ⟨compileProgram layout cmd, wordPoly, ramTimePoly, ?_⟩
  intro x
  let n := bitSize x
  have hrun := H.outputsFun x
  have houtSize : bitSize (f x) ≤ n + H.time.eval n * push := by
    have h := FinTM2.output_length_le_of_outputsInTime tm
      (List.map H.inputAlphabet.invFun (encode x))
      (List.map H.outputAlphabet.invFun (encode (f x)))
      (H.time.eval n) hrun
    simpa [n, bitSize, push] using h
  have hcost :
      (encodeInputLoopCost x + 19 * n + 18) +
        (initializeTablesCost (FinTM2.compileDispatcher tm 0).tables +
          coreCoeff * H.time.eval n + guardCost) +
        (29 * bitSize (f x) + 19) + 1 ≤ costPoly.eval n := by
    have hin := encodeInputLoopCost_le x
    simp [costPoly]
    dsimp [n, constantCost, coreCoeff, guardCost, push] at hin houtSize ⊢
    nlinarith
  have hexponent :
      n + 1 +
        ((encodeInputLoopCost x + 19 * n + 18) +
          (initializeTablesCost (FinTM2.compileDispatcher tm 0).tables +
            coreCoeff * H.time.eval n + guardCost) +
          (29 * bitSize (f x) + 19) + 1) * growth ≤ exponentPoly.eval n := by
    have hm := Nat.add_le_add_left (Nat.mul_le_mul_right growth hcost) (n + 1)
    simpa [exponentPoly, Nat.mul_comm, Nat.add_assoc] using hm
  have hwordEval : wordPoly.eval n = exponentPoly.eval n + layoutBitOverhead layout := by
    simp [wordPoly]
  constructor
  · intro a ha
    rw [List.mem_append] at ha
    rcases ha with ha | ha
    · rcases List.mem_cons.mp ha with rfl | ha
      · have hl := Lax51Proofs.Encoding.length_lt_two_pow_bitSize_add_one x
        exact hl.trans_le (pow_mono_exponent (by
          rw [hwordEval]
          simp [exponentPoly]
          omega))
      · have hv := Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one ha
        exact hv.trans_le (pow_mono_exponent (by
          rw [hwordEval]
          simp [exponentPoly]
          omega))
    · have hv := Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one ha
      have hbits : bitSize (f x) + 1 ≤ exponentPoly.eval n := by
        have hycost : bitSize (f x) ≤ costPoly.eval n := by
          have hnonneg : bitSize (f x) ≤
              (encodeInputLoopCost x + 19 * n + 18) +
                (initializeTablesCost (FinTM2.compileDispatcher tm 0).tables +
                  coreCoeff * H.time.eval n + guardCost) +
                (29 * bitSize (f x) + 19) + 1 := by omega
          exact hnonneg.trans hcost
        have hmul : costPoly.eval n ≤ growth * costPoly.eval n := by
          simpa using Nat.mul_le_mul_right (costPoly.eval n) hgrowthOne
        simp [exponentPoly]
        omega
      exact hv.trans_le (pow_mono_exponent
        (hbits.trans (by rw [hwordEval]; exact Nat.le_add_right _ _)))
  · intro w hw
    have hw' :
        (n + 1 +
          ((encodeInputLoopCost x + 19 * n + 18) +
            (initializeTablesCost (FinTM2.compileDispatcher tm 0).tables +
              coreCoeff * H.time.eval n + guardCost) +
            (29 * bitSize (f x) + 19) + 1) * growth) +
          layoutBitOverhead layout ≤ w := by
      apply (Nat.add_le_add_right hexponent (layoutBitOverhead layout)).trans
      rw [hwordEval] at hw
      simpa [n] using hw
    obtain ⟨t, ht, hram⟩ := FinTM2.compiledRam_outputsInTime tm
      H.inputAlphabet H.outputAlphabet x (f x) (H.time.eval n) w hrun hw'
    refine ⟨t, ?_, ?_⟩
    · apply ht.trans
      have hm := Nat.mul_le_mul_left layout.const hcost
      simpa [ramTimePoly, n] using hm
    · simpa [tm, inputStack, outputStack, separatorIn, zeroIn, oneIn,
        separatorOut, zeroOut, oneOut, initialStateCode, mainLabelCode,
        cmd, layout, growth, guardCost, coreCoeff, n] using hram

end Lax51Proofs.TMToRam
