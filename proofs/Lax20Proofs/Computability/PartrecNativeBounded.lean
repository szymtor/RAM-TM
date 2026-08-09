import Lax20Proofs.Computability.PartrecNativeCodec
import Lax20Proofs.TMToRam.InterpreterTame

namespace Lax20Proofs.Computability.PartrecNativeCodec

open Computability Turing Turing.PartrecToTM2
open Lax13Proofs.Imp
open Lax13Proofs.Compile Lax13Proofs.Simulation Lax13.Ram
open Lax20Proofs.TMToRam
open PartrecFiniteTM2

theorem encodePartrecInputBody_tame (consCode zeroCode oneCode : ℕ) :
    comTame (encodePartrecInputBody consCode zeroCode oneCode) := by
  unfold encodePartrecInputBody
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro com (rfl | rfl | rfl | rfl | h)
  · aesop
  · exact encodeBitsLoop_tame zeroCode oneCode
  · apply appendScratch_tame
    aesop
  · aesop
  · contradiction

theorem encodePartrecInputLoop_tame (consCode zeroCode oneCode : ℕ) :
    comTame (encodePartrecInputLoop consCode zeroCode oneCode) := by
  unfold encodePartrecInputLoop
  aesop (add safe encodePartrecInputBody_tame)

theorem encodeNativePartrecInputToScratch_tame
    (consCode zeroCode oneCode : ℕ) :
    comTame (encodeNativePartrecInputToScratch consCode zeroCode oneCode) := by
  unfold encodeNativePartrecInputToScratch
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro com (rfl | rfl | rfl | rfl | rfl | rfl | h)
  · aesop
  · aesop
  · aesop
  · exact encodeBitsLoop_tame zeroCode oneCode
  · apply appendScratch_tame
    aesop
  · exact encodePartrecInputLoop_tame consCode zeroCode oneCode
  · contradiction

theorem compilePartrecInputCodec_tame
    (inputStack consCode zeroCode oneCode initialStateCode mainLabelCode : ℕ) :
    comTame (compilePartrecInputCodec inputStack consCode zeroCode oneCode
      initialStateCode mainLabelCode) := by
  unfold compilePartrecInputCodec
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro com (rfl | rfl | rfl | rfl | h)
  · exact encodeNativePartrecInputToScratch_tame consCode zeroCode oneCode
  · exact reverseScratchIntoStack_tame inputStack
  · aesop
  · aesop
  · contradiction

theorem compilePartrecOutputCodec_tame
    (outputStack consCode zeroCode oneCode : ℕ) :
    comTame (compilePartrecOutputCodec outputStack consCode zeroCode oneCode) := by
  unfold compilePartrecOutputCodec
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro com (rfl | rfl | rfl | rfl | rfl | h)
  · aesop
  · aesop
  · aesop
  · aesop
  · apply ComTame.«while»
    · aesop
    · apply seqs_tame
      simp only [List.mem_cons, List.mem_singleton]
      rintro d (rfl | rfl | rfl | h')
      · aesop
      · aesop
      · exact consumeOutputSymbol_tame consCode zeroCode oneCode
      · contradiction
  · contradiction

open PartrecFiniteTM2 in
theorem compilePartrecNativeMachine_tame (c : ToPartrec.Code) :
    comTame (compilePartrecNativeMachine c) := by
  let tm := machine c
  unfold compilePartrecNativeMachine
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro com (rfl | rfl | rfl | h)
  · exact compilePartrecInputCodec_tame _ _ _ _ _ _
  · exact FinTM2.compileMachine_tame tm
  · exact compilePartrecOutputCodec_tame _ _ _ _
  · contradiction

noncomputable def partrecNativeBitGrowth (c : ToPartrec.Code) : ℕ :=
  Classical.choose (compilePartrecNativeMachine_tame c)

theorem compilePartrecNativeMachine_bitGrowth (c : ToPartrec.Code) :
    comBitGrowth (compilePartrecNativeMachine c) =
      some (partrecNativeBitGrowth c) :=
  Classical.choose_spec (compilePartrecNativeMachine_tame c)

/-- A bounded execution of the finite `ToPartrec` evaluator yields a complete
native IMP+ execution. The numerical bound is arbitrary: it is not assumed
to be polynomial or computable. -/
theorem compilePartrecNativeMachine_outputsInTime (c : ToPartrec.Code)
    (x y : List ℕ) (bound : ℕ)
    (hrun : TM2OutputsInTime (machine c) (trList (x.length :: x))
      (some (trList y)) bound) :
    ∃ ext σ' cost,
      BigStep (compilePartrecNativeMachine c)
        (initEnv ext (x.length :: x)) σ' cost ∧
      cost ≤
        ((29 * x.length.bits.length + 18 + encodePartrecInputLoopCost x) +
          19 * (encodePartrecListCodes (symbolCode c .cons)
            (symbolCode c .bit0) (symbolCode c .bit1)
            (x.length :: x)).length + 14) +
        (initializeTablesCost (FinTM2.compileDispatcher (machine c) 0).tables +
          (1 + Cond.size (.lt (.lit 0) (.var labelVar)) +
            maxCost (FinTM2.compileDispatcher (machine c) 0).com) * bound +
          (1 + Cond.size (.lt (.lit 0) (.var labelVar)))) +
        (29 * (encodePartrecListCodes (symbolCode c .cons)
          (symbolCode c .bit0) (symbolCode c .bit1) y).length + 13) + 1 ∧
      σ'.out = y := by
  let tm := machine c
  letI := tm.ΛFin
  letI : DecidableEq tm.Λ := Classical.decEq _
  let input := trList (x.length :: x)
  let output := trList y
  let witness := FinTM2.safeRunWitness_of_outputsInTime tm input output bound hrun
  let codes := encodePartrecListCodes (symbolCode c .cons)
    (symbolCode c .bit0) (symbolCode c .bit1) (x.length :: x)
  let tables := (FinTM2.compileDispatcher tm 0).tables
  let base := baseArrayLength witness.capacity codes.length
  let ext := installArrayLengths tables base
  have hpair : List.Pairwise (fun a b => a.1 ≠ b.1) tables := by
    simpa [tables] using FinTM2.compileDispatcher_tables_pairwise tm 0
  have htableLengths : ∀ name values, (name, values) ∈ tables →
      ext name = values.length := by
    intro name values hm
    exact installArrayLengths_mem tables hpair base name values hm
  have hstackLengths : ∀ j, ext (stackName j) = witness.capacity j := by
    intro j
    rw [show ext (stackName j) = base (stackName j) by
      apply installArrayLengths_of_not_mem_names
      intro values hm
      have hname := @compileLabelList_tables_name tm tm.ΛFin
        (Classical.decEq tm.Λ) (FinTM2.labelList tm) 0
        (stackName j) values
        (by simpa [tables, FinTM2.compileDispatcher] using hm)
      obtain ⟨i, hi⟩ := hname
      exact stackName_ne_tableName j i hi]
    exact baseArrayLength_stack witness.capacity codes.length j
  have hscratch : codes.length ≤ ext scratchName := by
    rw [show ext scratchName = base scratchName by
      apply installArrayLengths_of_not_mem_names
      intro values hm
      have hname := @compileLabelList_tables_name tm tm.ΛFin
        (Classical.decEq tm.Λ) (FinTM2.labelList tm) 0
        scratchName values
        (by simpa [tables, FinTM2.compileDispatcher] using hm)
      obtain ⟨i, hi⟩ := hname
      exact scratchName_ne_tableName i hi]
    simp [base, baseArrayLength]
  have hcodesLength : codes.length = input.length := by
    simpa [codes, input] using
      (congrArg List.length (map_trList_symbolCode c (x.length :: x))).symm
  have hinputCapacity : codes.length ≤
      witness.capacity (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₀) := by
    rw [hcodesLength]
    change input.length ≤
      FinTM2.traceCapacity tm (Turing.initList tm input) hrun.steps
        (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₀)
    rw [FinTM2.traceCapacity_finCode]
    simp [Turing.initList]
  obtain ⟨σ', cost, hbig, hcost, hout⟩ :=
    compilePartrecNativeMachine_safeRun c x y witness.capacity ext witness.run
      hstackLengths (by simpa [codes] using hscratch)
      (by simpa [codes] using hinputCapacity)
      (by simpa [tables, tm] using htableLengths)
  refine ⟨ext, σ', cost, hbig, ?_, hout⟩
  rw [witness.run_steps] at hcost
  have hsteps := witness.steps_le
  have hmul := Nat.mul_le_mul_left
    (1 + Cond.size (.lt (.lit 0) (.var labelVar)) +
      maxCost (FinTM2.compileDispatcher (machine c) 0).com) hsteps
  omega

/-- The explicit IMP+ cost bound for the native evaluator simulation. -/
noncomputable def partrecNativeCostBound (c : ToPartrec.Code) (x y : List ℕ)
    (bound : ℕ) : ℕ :=
  ((29 * x.length.bits.length + 18 + encodePartrecInputLoopCost x) +
      19 * (encodePartrecListCodes (symbolCode c .cons)
        (symbolCode c .bit0) (symbolCode c .bit1)
        (x.length :: x)).length + 14) +
    (initializeTablesCost (FinTM2.compileDispatcher (machine c) 0).tables +
      (1 + Cond.size (.lt (.lit 0) (.var labelVar)) +
        maxCost (FinTM2.compileDispatcher (machine c) 0).com) * bound +
      (1 + Cond.size (.lt (.lit 0) (.var labelVar)))) +
    (29 * (encodePartrecListCodes (symbolCode c .cons)
      (symbolCode c .bit0) (symbolCode c .bit1) y).length + 13) + 1

/-- The native evaluator run is bounded at an exponent linear in its IMP+
cost. This is the interface required by the verified IMP+-to-RAM compiler. -/
theorem compilePartrecNativeMachine_outputsInTime_bounded
    (c : ToPartrec.Code) (x y : List ℕ) (bound : ℕ)
    (hrun : TM2OutputsInTime (machine c) (trList (x.length :: x))
      (some (trList y)) bound) :
    let growth := partrecNativeBitGrowth c
    let costBound := partrecNativeCostBound c x y bound
    ∃ ext σ' cost,
      BigStepB (2 ^ (Lax20.BinaryWordEncoding.bitSize x + 1 +
          costBound * growth))
        (compilePartrecNativeMachine c)
        (initEnv ext (x.length :: x)) σ' cost ∧
      cost ≤ costBound ∧ σ'.out = y := by
  dsimp only
  obtain ⟨ext, σ', cost, hbig, hcost, hout⟩ :=
    compilePartrecNativeMachine_outputsInTime c x y bound hrun
  have hgrowth := compilePartrecNativeMachine_bitGrowth c
  obtain ⟨hbounded, _⟩ := bigStepBigStepBOfBitGrowth hbig
    (initEnv_bitBounded ext x) hgrowth le_rfl
  refine ⟨ext, σ', cost, ?_, ?_, hout⟩
  · refine bigStepBMono ?_ hbounded
    apply pow_mono_exponent
    apply Nat.add_le_add_left
    exact Nat.mul_le_mul_right (partrecNativeBitGrowth c) hcost
  · simpa [partrecNativeCostBound] using hcost

/-- End-to-end compilation of a bounded `ToPartrec` evaluator run to the
word RAM. Both the sufficient word length and the RAM time are explicit in
the actual finite-TM bound; no asymptotic assumption is made on that bound. -/
theorem compiledPartrecRam_outputsInTime (c : ToPartrec.Code)
    (x y : List ℕ) (bound w : ℕ)
    (hrun : TM2OutputsInTime (machine c) (trList (x.length :: x))
      (some (trList y)) bound) :
    let cmd := compilePartrecNativeMachine c
    let layout := comCanonicalLayout cmd
    let growth := partrecNativeBitGrowth c
    let costBound := partrecNativeCostBound c x y bound
    let exponent := Lax20.BinaryWordEncoding.bitSize x + 1 +
      costBound * growth
    exponent + layoutBitOverhead layout ≤ w →
      ∃ t ≤ layout.const * costBound,
        RunsTo w (compileProgram layout cmd) (x.length :: x) y t := by
  dsimp only
  intro hw
  obtain ⟨ext, σ', cost, hbs, hcost, hout⟩ :=
    compilePartrecNativeMachine_outputsInTime_bounded c x y bound hrun
  let cmd := compilePartrecNativeMachine c
  let layout := comCanonicalLayout cmd
  let exponent := Lax20.BinaryWordEncoding.bitSize x + 1 +
    partrecNativeCostBound c x y bound * partrecNativeBitGrowth c
  have hfit : layout.FitsWords (2 ^ exponent) w :=
    layoutFitsWordsTwoPow layout (by dsimp [exponent]; omega) hw
  have hx : ∀ v ∈ x.length :: x, v < 2 ^ exponent := by
    intro v hv
    have hsmall := (initEnv_bitBounded ext x).inp v hv
    exact hsmall.trans_le (pow_mono_exponent (by dsimp [exponent]; omega))
  obtain ⟨t, ht, htRun⟩ := compileProgram_runsTo hfit
    (by simpa [layout] using comCanonicalLayoutOk cmd) hx hbs
  refine ⟨t, ht.trans ?_, ?_⟩
  · exact Nat.mul_le_mul_left layout.const hcost
  · simpa [cmd, layout, hout] using htRun

end Lax20Proofs.Computability.PartrecNativeCodec
