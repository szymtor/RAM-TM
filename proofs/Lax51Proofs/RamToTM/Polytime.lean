import Lax51Proofs.RamToTM.CombinedInterpreter
import Lax51.RamPolytime
import Lax51.TuringPolytime

namespace Lax51Proofs.RamToTM

open Turing TM2 Polynomial Lax13.Ram
open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime

noncomputable section

def ramSimulationTM (p : Program) (wordBound : Polynomial Nat) : FinTM2 where
  K := WrapperStack
  k₀ := .input
  k₁ := .output
  Γ := WrapperAlphabet
  Λ := CombinedLabel p (programArgumentBound p) wordBound
  main := .inl (.inl (.inl .scan))
  σ := WrapperState (programArgumentBound p)
  initialState := default
  m := combinedProgram p (programArgumentBound p) le_rfl wordBound

noncomputable def terminalCostPolynomial
    (wordBound timeBound : Polynomial Nat) : Polynomial Nat :=
  let w := polynomialSimpleMajorant wordBound + 1
  2 * timeBound * (12 * w + 22) + 28 * w + 65

noncomputable def middleCostPolynomial
    (wordBound timeBound : Polynomial Nat) : Polynomial Nat :=
  coreSimulationPolynomial (polynomialSimpleMajorant wordBound) timeBound +
    terminalCostPolynomial wordBound timeBound + 1

noncomputable def initialCoreSizePolynomial
    (wordBound : Polynomial Nat) : Polynomial Nat :=
  let w := polynomialSimpleMajorant wordBound + 1
  w + (X + 1) * (w + 1) + 3

noncomputable def cleanupCostPolynomial (p : Program)
    (wordBound timeBound : Polynomial Nat) : Polynomial Nat :=
  let pushes := programPushBound
    (middleProgram p (programArgumentBound p) le_rfl)
  2 * (C 13 * (initialCoreSizePolynomial wordBound +
    C pushes * middleCostPolynomial wordBound timeBound)) + 13

noncomputable def outputCostPolynomial
    (wordBound timeBound : Polynomial Nat) : Polynomial Nat :=
  let w := polynomialSimpleMajorant wordBound + 1
  4 + timeBound * (3 * w + 3)

noncomputable def ramToTMTimePolynomial (p : Program)
    (wordBound timeBound : Polynomial Nat) : Polynomial Nat :=
  fullInputCostPolynomial wordBound + 2 +
    middleCostPolynomial wordBound timeBound +
    outputCostPolynomial wordBound timeBound +
    cleanupCostPolynomial p wordBound timeBound + 1

@[simp] theorem terminalCostPolynomial_eval
    (wordBound timeBound : Polynomial Nat) (n : Nat) :
    (terminalCostPolynomial wordBound timeBound).eval n =
      2 * timeBound.eval n *
          (12 * ((polynomialSimpleMajorant wordBound).eval n + 1) + 22) +
        28 * ((polynomialSimpleMajorant wordBound).eval n + 1) + 65 := by
  simp [terminalCostPolynomial]

@[simp] theorem middleCostPolynomial_eval
    (wordBound timeBound : Polynomial Nat) (n : Nat) :
    (middleCostPolynomial wordBound timeBound).eval n =
      (coreSimulationPolynomial (polynomialSimpleMajorant wordBound) timeBound).eval n +
        (terminalCostPolynomial wordBound timeBound).eval n + 1 := by
  simp [middleCostPolynomial]

@[simp] theorem initialCoreSizePolynomial_eval
    (wordBound : Polynomial Nat) (n : Nat) :
    (initialCoreSizePolynomial wordBound).eval n =
      ((polynomialSimpleMajorant wordBound).eval n + 1) +
        (n + 1) * ((polynomialSimpleMajorant wordBound).eval n + 2) + 3 := by
  simp [initialCoreSizePolynomial]

@[simp] theorem cleanupCostPolynomial_eval (p : Program)
    (wordBound timeBound : Polynomial Nat) (n : Nat) :
    (cleanupCostPolynomial p wordBound timeBound).eval n =
      let pushes := programPushBound
        (middleProgram p (programArgumentBound p) le_rfl)
      2 * (13 * ((initialCoreSizePolynomial wordBound).eval n +
        pushes * (middleCostPolynomial wordBound timeBound).eval n)) + 13 := by
  simp [cleanupCostPolynomial]

@[simp] theorem outputCostPolynomial_eval
    (wordBound timeBound : Polynomial Nat) (n : Nat) :
    (outputCostPolynomial wordBound timeBound).eval n =
      4 + timeBound.eval n *
        (3 * ((polynomialSimpleMajorant wordBound).eval n + 1) + 3) := by
  simp [outputCostPolynomial]

@[simp] theorem ramToTMTimePolynomial_eval (p : Program)
    (wordBound timeBound : Polynomial Nat) (n : Nat) :
    (ramToTMTimePolynomial p wordBound timeBound).eval n =
      (fullInputCostPolynomial wordBound).eval n + 2 +
      (middleCostPolynomial wordBound timeBound).eval n +
      (outputCostPolynomial wordBound timeBound).eval n +
      (cleanupCostPolynomial p wordBound timeBound).eval n + 1 := by
  simp [ramToTMTimePolynomial]

theorem cleaned_output_stacks (tapes : CoreStack → List SparseSymbol)
    (output : List Nat) :
    cleanedStacks
        (outputAdapterStacks [] (encode output)
          (wrapperCoreStacks tapes [] [])) =
      wrapperCoreStacks (fun _ => []) [] (encode output) := by
  funext k
  cases k with
  | input => simp [cleanedStacks, outputAdapterStacks, wrapperCoreStacks] <;> rfl
  | output => simp [cleanedStacks, outputAdapterStacks, wrapperCoreStacks]
  | core k =>
      cases k <;>
        simp [cleanedStacks, outputAdapterStacks, wrapperCoreStacks] <;> rfl

set_option maxHeartbeats 3000000 in
theorem combined_runsTo_bounded (p : Program)
    (wordBound timeBound : Polynomial Nat) (x output : List Nat) (t : Nat)
    (hfits : FitsInWords (wordBound.eval (bitSize x))
      ((x.length :: x) ++ output))
    (ht : t ≤ timeBound.eval (bitSize x))
    (hram : RunsTo (simulationWordWidth wordBound x) p
      (x.length :: x) output t) :
    ∃ steps ≤ (ramToTMTimePolynomial p wordBound timeBound).eval (bitSize x),
      ((fun o => o.bind (TM2.step
        (combinedProgram p (programArgumentBound p) le_rfl wordBound)))^[steps])
        (some (mapLabelCfg embedInputCombined
          (fullInputCfg (.inl (.inl .scan))
            (default : WrapperState (programArgumentBound p))
            (inputWidthInitialStacks (encode x))))) =
      some ⟨none, default,
        wrapperCoreStacks (fun _ => []) [] (encode output)⟩ := by
  rcases combined_runsTo_complete p wordBound x output t hfits hram with
    ⟨ss, coreSteps, stopSteps, finalState, finalTapes,
      hmem, houtLength, hcore, hstop, hcleanup, hrun⟩
  let n := bitSize x
  let w := simulationWordWidth wordBound x
  let pushes := programPushBound
    (middleProgram p (programArgumentBound p) le_rfl)
  let middleBound := (middleCostPolynomial wordBound timeBound).eval n
  have hcorePoly : coreSteps ≤
      (coreSimulationPolynomial (polynomialSimpleMajorant wordBound) timeBound).eval n := by
    apply finiteSparseRun_steps_le_corePolynomial
      (polynomialSimpleMajorant wordBound) timeBound n w t coreSteps
    · simp [w, n, simulationWordWidth]
    · exact ht
    · exact hcore
  have hstopPoly : stopSteps ≤
      (terminalCostPolynomial wordBound timeBound).eval n := by
    apply hstop.trans
    have hw : w = (polynomialSimpleMajorant wordBound).eval n + 1 := by
      simp [w, n, simulationWordWidth]
    let widthCost := 12 * w + 22
    have hmemTime := hmem.trans ht
    have hprod := Nat.mul_le_mul_right widthCost hmemTime
    simp only [operandEvalBound, terminalCostPolynomial_eval]
    rw [← hw]
    dsimp [widthCost] at hprod
    nlinarith
  have hmiddle : coreSteps + stopSteps + 1 ≤ middleBound := by
    dsimp [middleBound]
    rw [middleCostPolynomial_eval]
    exact Nat.add_le_add_right (Nat.add_le_add hcorePoly hstopPoly) 1
  have hx := Lax51Proofs.Encoding.length_le_bitSize x
  have hinitial : coreSize w (sparseInitState (x.length :: x)) ≤
      (initialCoreSizePolynomial wordBound).eval n := by
    simp [coreSize_eq, sparseInitState, initialCoreSizePolynomial_eval,
      w, n, simulationWordWidth]
    nlinarith
  have hcleanupPoly : cleanupTotalCost
        (outputAdapterStacks [] (encode output)
          (wrapperCoreStacks finalTapes [] [])) ≤
      (cleanupCostPolynomial p wordBound timeBound).eval n := by
    apply hcleanup.trans
    rw [cleanupCostPolynomial_eval]
    dsimp only [pushes]
    have hmul : (coreSteps + stopSteps + 1) * pushes ≤
        pushes * middleBound := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left pushes hmiddle
    have hins := Nat.add_le_add hinitial hmul
    have hscaled := Nat.mul_le_mul_left 13 hins
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hscaled) 13
  have houtputPoly :
      4 + output.length * (3 * w + 3) ≤
        (outputCostPolynomial wordBound timeBound).eval n := by
    rw [outputCostPolynomial_eval]
    have hw : w = (polynomialSimpleMajorant wordBound).eval n + 1 := by
      simp [w, n, simulationWordWidth]
    rw [hw]
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_right
        (3 * ((polynomialSimpleMajorant wordBound).eval n + 1) + 3)
        (houtLength.trans ht)) 4
  let decoded := outputAdapterStacks [] (encode output)
    (wrapperCoreStacks finalTapes [] [])
  let steps := fullInputCost wordBound x + 2 +
    (coreSteps + stopSteps + 1) +
    (4 + output.length * (3 * w + 3) +
      (cleanupTotalCost decoded + 1))
  refine ⟨steps, ?_, ?_⟩
  · rw [ramToTMTimePolynomial_eval]
    have hinput := fullInputCost_le_polynomial wordBound x
    dsimp only [steps, decoded]
    calc
      fullInputCost wordBound x + 2 + (coreSteps + stopSteps + 1) +
          (4 + output.length * (3 * w + 3) +
            (cleanupTotalCost
              (outputAdapterStacks [] (encode output)
                (wrapperCoreStacks finalTapes [] [])) + 1)) ≤
        (fullInputCostPolynomial wordBound).eval (bitSize x) + 2 +
          middleBound +
          ((outputCostPolynomial wordBound timeBound).eval n +
            ((cleanupCostPolynomial p wordBound timeBound).eval n + 1)) := by
              gcongr
      _ = (fullInputCostPolynomial wordBound).eval (bitSize x) + 2 +
          middleBound + (outputCostPolynomial wordBound timeBound).eval n +
          (cleanupCostPolynomial p wordBound timeBound).eval n + 1 := by omega
  · dsimp only [steps, decoded]
    rw [cleaned_output_stacks] at hrun
    simpa [w, Nat.add_assoc] using hrun

def wrapperInputEquiv :
    (ramSimulationTM ([] : Program) 0).Γ
      (ramSimulationTM ([] : Program) 0).k₀ ≃ Symbol :=
  Equiv.refl Symbol

def wrapperOutputEquiv :
    (ramSimulationTM ([] : Program) 0).Γ
      (ramSimulationTM ([] : Program) 0).k₁ ≃ Symbol :=
  Equiv.refl Symbol

theorem ramSimulation_initList (p : Program) (wordBound : Polynomial Nat)
    (input : List Symbol) :
    Turing.initList (ramSimulationTM p wordBound) input =
      mapLabelCfg embedInputCombined
        (fullInputCfg (.inl (.inl .scan))
          (default : WrapperState (programArgumentBound p))
          (inputWidthInitialStacks input)) := by
  simp only [Turing.initList, ramSimulationTM, mapLabelCfg, fullInputCfg]
  congr 1
  funext k
  cases k with
  | input => simp [inputWidthInitialStacks]
  | output => simp [inputWidthInitialStacks]
  | core k => simp [inputWidthInitialStacks]

theorem ramSimulation_haltList (p : Program) (wordBound : Polynomial Nat)
    (output : List Symbol) :
    Turing.haltList (ramSimulationTM p wordBound) output =
      ⟨none, default,
        wrapperCoreStacks (fun _ => []) [] output⟩ := by
  simp only [Turing.haltList, ramSimulationTM]
  congr 1
  funext k
  cases k with
  | input => simp [wrapperCoreStacks] <;> rfl
  | output => simp [wrapperCoreStacks]
  | core k => simp [wrapperCoreStacks] <;> rfl

/-- The reverse polynomial-time simulation: a uniform polynomial-time word
RAM is simulated by one finite multi-stack Turing machine. -/
theorem ramPolytime_to_turingPolytime {f : List Nat → List Nat}
    (hf : RamPolytime f) : TuringPolytime f := by
  rcases hf with ⟨p, wordBound, timeBound, hram⟩
  refine ⟨{
    tm := ramSimulationTM p wordBound
    inputAlphabet := Equiv.refl Symbol
    outputAlphabet := Equiv.refl Symbol
    time := ramToTMTimePolynomial p wordBound timeBound
    outputsFun := ?_ }⟩
  intro x
  rcases hram x with ⟨hfits, hallWidths⟩
  have hw : wordBound.eval (bitSize x) ≤ simulationWordWidth wordBound x :=
    (polynomial_eval_le_simpleMajorant wordBound (bitSize x)).trans
      (by simp [simulationWordWidth])
  let witness := Classical.indefiniteDescription
    (fun t => t ≤ timeBound.eval (bitSize x) ∧
      RunsTo (simulationWordWidth wordBound x) p
        (x.length :: x) (f x) t)
    (hallWidths (simulationWordWidth wordBound x) hw)
  rcases witness with ⟨t, ht, hrun⟩
  let simulationWitness := Classical.indefiniteDescription
    (fun steps => steps ≤
        (ramToTMTimePolynomial p wordBound timeBound).eval (bitSize x) ∧
      ((fun o => o.bind (TM2.step
        (combinedProgram p (programArgumentBound p) le_rfl wordBound)))^[steps])
        (some (mapLabelCfg embedInputCombined
          (fullInputCfg (.inl (.inl .scan))
            (default : WrapperState (programArgumentBound p))
            (inputWidthInitialStacks (encode x))))) =
      some ⟨none, default,
        wrapperCoreStacks (fun _ => []) [] (encode (f x))⟩)
    (combined_runsTo_bounded p wordBound timeBound x (f x) t
      hfits ht hrun)
  rcases simulationWitness with ⟨steps, hsteps, htm⟩
  refine ⟨⟨steps, ?_⟩, hsteps⟩
  rw [ramSimulation_initList]
  simp only [Option.map_some]
  rw [ramSimulation_haltList]
  have mapSymmRefl (xs : List Symbol) :
      List.map (⇑(Equiv.refl Symbol).symm) xs = xs := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.map_cons]; rw [ih]; rfl
  have mapInvRefl (xs : List Symbol) :
      List.map (Equiv.refl Symbol).invFun xs = xs := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.map_cons]; rw [ih]; rfl
  have hstart : mapLabelCfg
      (embedInputCombined (p := p) (N := programArgumentBound p)
        (wordBound := wordBound))
      (fullInputCfg (.inl (.inl .scan))
        (default : WrapperState (programArgumentBound p))
        (inputWidthInitialStacks
          (List.map (Equiv.refl Symbol).invFun (encode x)))) =
      mapLabelCfg
        (embedInputCombined (p := p) (N := programArgumentBound p)
          (wordBound := wordBound))
        (fullInputCfg (.inl (.inl .scan)) default
          (inputWidthInitialStacks (encode x))) := by
    congr 6
    exact mapInvRefl _
  have hend : (⟨none, default,
      wrapperCoreStacks (fun _ => []) []
        (List.map (Equiv.refl Symbol).invFun (encode (f x)))⟩ :
      TM2.Cfg WrapperAlphabet
        (CombinedLabel p (programArgumentBound p) wordBound)
        (WrapperState (programArgumentBound p))) =
      ⟨none, default,
        wrapperCoreStacks (fun _ => []) [] (encode (f x))⟩ := by
    congr 6
    exact mapInvRefl _
  change ((fun o => o.bind (TM2.step
      (combinedProgram p (programArgumentBound p) le_rfl wordBound)))^[steps])
    (some (mapLabelCfg
      (embedInputCombined (p := p) (N := programArgumentBound p)
        (wordBound := wordBound))
      (fullInputCfg (.inl (.inl .scan)) default
        (inputWidthInitialStacks
          (List.map (Equiv.refl Symbol).invFun (encode x)))))) =
    some ⟨none, default,
      wrapperCoreStacks (fun _ => []) []
        (List.map (Equiv.refl Symbol).invFun (encode (f x)))⟩
  rw [hstart, hend]
  exact htm

end

end Lax51Proofs.RamToTM
