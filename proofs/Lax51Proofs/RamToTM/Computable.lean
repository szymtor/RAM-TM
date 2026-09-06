import Lax51Proofs.RamToTM.Polytime

namespace Lax51Proofs.RamToTM

open Turing TM2 Polynomial Lax51Proofs.Microcode
open Lax51.BinaryWordEncoding Lax51.RamPolytime

noncomputable section

/-- At a fixed polynomially supplied word width, an arbitrary `t`-step RAM
execution is simulated by a finite Turing machine with a fixed polynomial
overhead in the input bit-size plus `t`. No polynomial assumption is made on
the function supplying `t`. -/
theorem ramInTime_to_turingInPolynomialOverhead (p : Program)
    (wordBound : Polynomial ℕ) :
    ∃ (timeOverhead : Polynomial ℕ),
      ∀ (x output : List ℕ) (t : ℕ),
        FitsInWords (wordBound.eval (bitSize x)) ((x.length :: x) ++ output) →
        RunsTo (simulationWordWidth wordBound x) p (x.length :: x) output t →
        Nonempty (TM2OutputsInTime (ramSimulationTM p wordBound) (encode x)
          (some (encode output))
          (timeOverhead.eval (bitSize x + t))) := by
  let timeOverhead := ramToTMTimePolynomial p wordBound X
  refine ⟨timeOverhead, ?_⟩
  intro x output t hfits hram
  let n := bitSize x
  let q := n + t
  obtain ⟨steps, hsteps, htm⟩ := combined_runsTo_bounded
    p wordBound (C t) x output t hfits (by simp) hram
  have hnq : n ≤ q := by simp [q]
  have htq : t ≤ q := by simp [q]
  have hword :
      (polynomialSimpleMajorant wordBound).eval n ≤
        (polynomialSimpleMajorant wordBound).eval q :=
    polynomial_eval_mono _ hnq
  have hcore :
      (coreSimulationPolynomial (polynomialSimpleMajorant wordBound) (C t)).eval n ≤
        (coreSimulationPolynomial (polynomialSimpleMajorant wordBound) X).eval q := by
    simp only [coreSimulationPolynomial_eval, eval_C, eval_X]
    gcongr
  have hterminal :
      (terminalCostPolynomial wordBound (C t)).eval n ≤
        (terminalCostPolynomial wordBound X).eval q := by
    simp only [terminalCostPolynomial_eval, eval_C, eval_X]
    gcongr
  have hmiddle :
      (middleCostPolynomial wordBound (C t)).eval n ≤
        (middleCostPolynomial wordBound X).eval q := by
    simp only [middleCostPolynomial_eval]
    gcongr
  have houtput :
      (outputCostPolynomial wordBound (C t)).eval n ≤
        (outputCostPolynomial wordBound X).eval q := by
    simp only [outputCostPolynomial_eval, eval_C, eval_X]
    gcongr
  have hcleanup :
      (cleanupCostPolynomial p wordBound (C t)).eval n ≤
        (cleanupCostPolynomial p wordBound X).eval q := by
    simp only [cleanupCostPolynomial_eval]
    gcongr
    · exact polynomial_eval_mono _ hnq
  have htime :
      (ramToTMTimePolynomial p wordBound (C t)).eval n ≤
        timeOverhead.eval q := by
    simp only [ramToTMTimePolynomial_eval]
    dsimp [timeOverhead]
    rw [ramToTMTimePolynomial_eval]
    gcongr
    · exact polynomial_eval_mono _ hnq
  refine ⟨{
    steps := steps
    evals_in_steps := ?_
    steps_le_m := hsteps.trans (by simpa [n, q] using htime) }⟩
  rw [ramSimulation_initList]
  simp only [Option.map_some]
  rw [ramSimulation_haltList]
  simpa using htm

end

end Lax51Proofs.RamToTM
