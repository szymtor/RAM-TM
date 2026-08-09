import Lax20Proofs.TMToRam.NativeBounded

namespace Lax20Proofs.TMToRam

open Lax20.BinaryWordEncoding
open Lax13.Ram Lax13Proofs.Imp Lax13Proofs.Compile
open Polynomial

/-- A finite Turing machine with an arbitrary per-input numerical
running-time bound compiles to one uniform word-RAM program. The sufficient
word length and RAM running time are fixed linear polynomials in the input
bit-size plus that bound. -/
theorem turingWithInputTime_to_ramInPolynomialOverhead {f : List ℕ → List ℕ}
    (H : Turing.TM2ComputableAux Symbol Symbol) (time : List ℕ → ℕ)
    (hrun : ∀ x, Turing.TM2OutputsInTime H.tm
      (List.map H.inputAlphabet.invFun (encode x))
      (some (List.map H.outputAlphabet.invFun (encode (f x)))) (time x)) :
    ∃ (p : Program) (wordOverhead timeOverhead : Polynomial ℕ),
      ∀ (x : List ℕ) (w : ℕ),
        wordOverhead.eval (bitSize x + time x) ≤ w →
          ∃ t ≤ timeOverhead.eval (bitSize x + time x),
            RunsTo w p (x.length :: x) (f x) t := by
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
  let combinedCoeff := max 99 (coreCoeff + 29 * push)
  let costOverhead : Polynomial ℕ := C constantCost + C combinedCoeff * X
  let wordOverhead : Polynomial ℕ :=
    X + C 1 + C growth * costOverhead + C (layoutBitOverhead layout)
  let timeOverhead : Polynomial ℕ := C layout.const * costOverhead
  refine ⟨compileProgram layout cmd, wordOverhead, timeOverhead, ?_⟩
  intro x w hw
  let n := bitSize x
  let runningTime := time x
  let q := n + runningTime
  have hrun' := hrun x
  have houtSize : bitSize (f x) ≤ n + runningTime * push := by
    have h := FinTM2.output_length_le_of_outputsInTime tm
      (List.map H.inputAlphabet.invFun (encode x))
      (List.map H.outputAlphabet.invFun (encode (f x))) runningTime hrun'
    simpa [n, runningTime, bitSize, push] using h
  have hcost :
      (encodeInputLoopCost x + 19 * n + 18) +
        (initializeTablesCost (FinTM2.compileDispatcher tm 0).tables +
          coreCoeff * runningTime + guardCost) +
        (29 * bitSize (f x) + 19) + 1 ≤ costOverhead.eval q := by
    have hin := encodeInputLoopCost_le x
    have hn : 99 ≤ combinedCoeff := le_max_left _ _
    have ht : coreCoeff + 29 * push ≤ combinedCoeff := le_max_right _ _
    have hn' := Nat.mul_le_mul_right n hn
    have ht' := Nat.mul_le_mul_right runningTime ht
    simp [costOverhead]
    dsimp [n, runningTime, q, constantCost, combinedCoeff, coreCoeff, guardCost, push]
      at hin houtSize hn' ht' ⊢
    nlinarith
  have hword :
      (n + 1 +
        ((encodeInputLoopCost x + 19 * n + 18) +
          (initializeTablesCost (FinTM2.compileDispatcher tm 0).tables +
            coreCoeff * runningTime + guardCost) +
          (29 * bitSize (f x) + 19) + 1) * growth) +
        layoutBitOverhead layout ≤ wordOverhead.eval q := by
    calc
      (n + 1 +
          ((encodeInputLoopCost x + 19 * n + 18) +
            (initializeTablesCost (FinTM2.compileDispatcher tm 0).tables +
              coreCoeff * runningTime + guardCost) +
            (29 * bitSize (f x) + 19) + 1) * growth) +
          layoutBitOverhead layout ≤
        (n + 1 + costOverhead.eval q * growth) +
          layoutBitOverhead layout := by gcongr
      _ ≤ (q + 1 + costOverhead.eval q * growth) +
          layoutBitOverhead layout := by
        dsimp [q]
        omega
      _ = wordOverhead.eval q := by
        simp [wordOverhead, Nat.mul_comm, Nat.add_assoc]
  have hw' :
      (n + 1 +
        ((encodeInputLoopCost x + 19 * n + 18) +
          (initializeTablesCost (FinTM2.compileDispatcher tm 0).tables +
            coreCoeff * runningTime + guardCost) +
          (29 * bitSize (f x) + 19) + 1) * growth) +
        layoutBitOverhead layout ≤ w := by
    exact hword.trans (by simpa [n, runningTime, q] using hw)
  obtain ⟨t, ht, hram⟩ := FinTM2.compiledRam_outputsInTime tm
    H.inputAlphabet H.outputAlphabet x (f x) runningTime w hrun' hw'
  refine ⟨t, ht.trans ?_, ?_⟩
  · have hm := Nat.mul_le_mul_left layout.const hcost
    simpa [timeOverhead, n, runningTime, q] using hm
  · simpa [tm, inputStack, outputStack, separatorIn, zeroIn, oneIn,
      separatorOut, zeroOut, oneOut, initialStateCode, mainLabelCode,
      cmd, layout, growth, guardCost, coreCoeff, n, runningTime] using hram

/-- The input-length-indexed form used by the polynomial-time development. -/
theorem turingInTime_to_ramInPolynomialOverhead {f : List ℕ → List ℕ}
    (H : Turing.TM2ComputableInTime encode encode f) :
    ∃ (p : Program) (wordOverhead timeOverhead : Polynomial ℕ),
      ∀ (x : List ℕ) (w : ℕ),
        wordOverhead.eval (bitSize x + H.time (bitSize x)) ≤ w →
          ∃ t ≤ timeOverhead.eval (bitSize x + H.time (bitSize x)),
            RunsTo w p (x.length :: x) (f x) t := by
  simpa using turingWithInputTime_to_ramInPolynomialOverhead
    H.toTM2ComputableAux (fun x => H.time (bitSize x)) H.outputsFun

end Lax20Proofs.TMToRam
