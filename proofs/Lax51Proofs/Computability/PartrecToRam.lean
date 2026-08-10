import Lax51Proofs.Computability.PartrecNativeBounded
import Lax51Proofs.Encoding

namespace Lax51Proofs.Computability.PartrecNativeCodec

open Computability Turing Turing.PartrecToTM2
open Lax13.Ram Lax13Proofs.Imp Lax13Proofs.Compile
open Lax51Proofs.TMToRam Polynomial
open PartrecFiniteTM2

@[simp] theorem encodePartrecNatCodes_length
    (consCode zeroCode oneCode n : ℕ) :
    (encodePartrecNatCodes consCode zeroCode oneCode n).length =
      n.bits.length + 1 := by
  simp [encodePartrecNatCodes]

theorem encodePartrecListCodes_length
    (consCode zeroCode oneCode : ℕ) (xs : List ℕ) :
    (encodePartrecListCodes consCode zeroCode oneCode xs).length =
      Lax51.BinaryWordEncoding.bitSize xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rw [encodePartrecListCodes_cons, List.length_append,
        encodePartrecNatCodes_length, ih,
        Lax51Proofs.Encoding.bitSize_cons]

theorem trList_length (xs : List ℕ) :
    (trList xs).length = Lax51.BinaryWordEncoding.bitSize xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rw [trList, List.length_append, List.length_cons, trNat_eq_bits,
        List.length_map, ih, Lax51Proofs.Encoding.bitSize_cons]
      omega

theorem length_bits_length_le_bitSize_add_one (x : List ℕ) :
    x.length.bits.length ≤ Lax51.BinaryWordEncoding.bitSize x + 1 := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.2
    (Lax51Proofs.Encoding.length_lt_two_pow_bitSize_add_one x)

theorem bitSize_length_cons_le (x : List ℕ) :
    Lax51.BinaryWordEncoding.bitSize (x.length :: x) ≤
      2 * Lax51.BinaryWordEncoding.bitSize x + 2 := by
  rw [Lax51Proofs.Encoding.bitSize_cons]
  have h := length_bits_length_le_bitSize_add_one x
  omega

theorem encodePartrecInputLoopCost_le (x : List ℕ) :
    encodePartrecInputLoopCost x ≤
      51 * Lax51.BinaryWordEncoding.bitSize x + 4 := by
  have heq : encodePartrecInputLoopCost x = encodeInputLoopCost x := by
    induction x with
    | nil => rfl
    | cons a xs ih =>
        simp only [encodePartrecInputLoopCost, encodeInputLoopCost, ih]
  rw [heq]
  exact Lax51Proofs.TMToRam.encodeInputLoopCost_le x

/-- A `ToPartrec` finite evaluator with any numerical per-input time bound
compiles to one word-RAM program. The sufficient word width and RAM time are
fixed linear polynomials in `bitSize x + time x`; `time` itself need not be
polynomial or computable. -/
theorem partrecWithInputTime_to_ramInPolynomialOverhead
    {f : List ℕ → List ℕ} (c : ToPartrec.Code)
    (time : List ℕ → ℕ)
    (hrun : ∀ x, TM2OutputsInTime (machine c)
      (trList (x.length :: x)) (some (trList (f x))) (time x)) :
    ∃ (p : Program) (wordOverhead timeOverhead : Polynomial ℕ),
      ∀ (x : List ℕ) (w : ℕ),
        wordOverhead.eval (Lax51.BinaryWordEncoding.bitSize x + time x) ≤ w →
          ∃ t ≤ timeOverhead.eval
              (Lax51.BinaryWordEncoding.bitSize x + time x),
            RunsTo w p (x.length :: x) (f x) t := by
  let tm := machine c
  let cmd := compilePartrecNativeMachine c
  let layout := comCanonicalLayout cmd
  let growth := partrecNativeBitGrowth c
  let guardCost := 1 + Cond.size (.lt (.lit 0) (.var labelVar))
  let coreCoeff := guardCost + maxCost (FinTM2.compileDispatcher tm 0).com
  let push := FinTM2.machinePushBudget tm tm.k₀
  let constantCost := 175 +
    initializeTablesCost (FinTM2.compileDispatcher tm 0).tables + guardCost
  let combinedCoeff := max 176 (coreCoeff + 29 * push)
  let costOverhead : Polynomial ℕ := C constantCost + C combinedCoeff * X
  let wordOverhead : Polynomial ℕ :=
    X + C 1 + C growth * costOverhead + C (layoutBitOverhead layout)
  let timeOverhead : Polynomial ℕ := C layout.const * costOverhead
  refine ⟨compileProgram layout cmd, wordOverhead, timeOverhead, ?_⟩
  intro x w hw
  let n := Lax51.BinaryWordEncoding.bitSize x
  let runningTime := time x
  let q := n + runningTime
  have hrun' := hrun x
  have hprefix : Lax51.BinaryWordEncoding.bitSize (x.length :: x) ≤
      2 * n + 2 := by
    simpa [n] using bitSize_length_cons_le x
  have houtSize : Lax51.BinaryWordEncoding.bitSize (f x) ≤
      2 * n + 2 + runningTime * push := by
    have h := FinTM2.output_length_le_of_outputsInTime tm
      (trList (x.length :: x)) (trList (f x)) runningTime hrun'
    rw [trList_length, trList_length] at h
    exact h.trans (Nat.add_le_add_right hprefix _)
  have hhead := length_bits_length_le_bitSize_add_one x
  have hloop := encodePartrecInputLoopCost_le x
  have hinputCodes :
      (encodePartrecListCodes (symbolCode c .cons)
        (symbolCode c .bit0) (symbolCode c .bit1)
        (x.length :: x)).length ≤ 2 * n + 2 := by
    rw [encodePartrecListCodes_length]
    exact hprefix
  have houtputCodes :
      (encodePartrecListCodes (symbolCode c .cons)
        (symbolCode c .bit0) (symbolCode c .bit1) (f x)).length ≤
        2 * n + 2 + runningTime * push := by
    rw [encodePartrecListCodes_length]
    exact houtSize
  have hcost : partrecNativeCostBound c x (f x) runningTime ≤
      costOverhead.eval q := by
    have hn : 176 ≤ combinedCoeff := le_max_left _ _
    have ht : coreCoeff + 29 * push ≤ combinedCoeff := le_max_right _ _
    have hn' := Nat.mul_le_mul_right n hn
    have ht' := Nat.mul_le_mul_right runningTime ht
    simp [costOverhead]
    dsimp [partrecNativeCostBound, n, runningTime, q, constantCost,
      combinedCoeff, coreCoeff, guardCost, push, tm]
      at hhead hloop hinputCodes houtputCodes hn' ht' ⊢
    nlinarith
  have hword :
      (n + 1 + partrecNativeCostBound c x (f x) runningTime * growth) +
          layoutBitOverhead layout ≤ wordOverhead.eval q := by
    calc
      (n + 1 + partrecNativeCostBound c x (f x) runningTime * growth) +
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
      (n + 1 + partrecNativeCostBound c x (f x) runningTime * growth) +
          layoutBitOverhead layout ≤ w :=
    hword.trans (by simpa [n, runningTime, q] using hw)
  obtain ⟨t, htRun, hram⟩ := compiledPartrecRam_outputsInTime c
    x (f x) runningTime w hrun' (by
      simpa [cmd, layout, growth, n, runningTime] using hw')
  refine ⟨t, htRun.trans ?_, ?_⟩
  · have hm := Nat.mul_le_mul_left layout.const hcost
    simpa [timeOverhead, n, runningTime, q] using hm
  · simpa [cmd, layout] using hram

end Lax51Proofs.Computability.PartrecNativeCodec
