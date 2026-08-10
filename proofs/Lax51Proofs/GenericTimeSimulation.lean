import Lax51Proofs.TMToRam.Computable
import Lax51Proofs.RamToTM.Computable
import Lax51.TuringToRamGenericTime
import Lax51.RamToTuringGenericTime

namespace Lax51Proofs.GenericTimeSimulation

open Lax13.Ram
open Lax51.BinaryWordEncoding Lax51.RamPolytime
open Polynomial Turing

open Lax51Proofs.RamToTM

private theorem map_refl_invFun (xs : List Symbol) :
    List.map (Equiv.refl Symbol).invFun xs = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      change a :: List.map (Equiv.refl Symbol).invFun xs = a :: xs
      rw [ih]

/--
---
conclusion: Lax51.TuringToRamGenericTime.turingWithInputTime_to_ramInPolynomialOverhead
---
-/
theorem turingWithInputTime_to_ramInPolynomialOverhead
    {f : List ℕ → List ℕ}
    (H : TM2ComputableAux Symbol Symbol) (time : List ℕ → ℕ)
    (hrun : ∀ x, TM2OutputsInTime H.tm
      (List.map H.inputAlphabet.invFun (encode x))
      (some (List.map H.outputAlphabet.invFun (encode (f x)))) (time x)) :
    ∃ (p : Program) (wordOverhead timeOverhead : Polynomial ℕ),
      ∀ (x : List ℕ) (w : ℕ),
        wordOverhead.eval (bitSize x + time x) ≤ w →
          ∃ t ≤ timeOverhead.eval (bitSize x + time x),
            RunsTo w p (x.length :: x) (f x) t := by
  exact Lax51Proofs.TMToRam.turingWithInputTime_to_ramInPolynomialOverhead
    H time hrun

/--
---
conclusion: Lax51.RamToTuringGenericTime.ramInTime_to_turingInPolynomialOverhead
---
-/
theorem ramInTime_to_turingInPolynomialOverhead
    (p : Program) (wordBound : Polynomial ℕ) :
    ∃ (H : TM2ComputableAux Symbol Symbol)
        (widthOverhead timeOverhead : Polynomial ℕ),
      (∀ n, wordBound.eval n ≤ widthOverhead.eval n) ∧
        ∀ (x output : List ℕ) (t : ℕ),
          FitsInWords (wordBound.eval (bitSize x))
              ((x.length :: x) ++ output) →
            RunsTo (widthOverhead.eval (bitSize x)) p
                (x.length :: x) output t →
              Nonempty (TM2OutputsInTime H.tm
                (List.map H.inputAlphabet.invFun (encode x))
                (some (List.map H.outputAlphabet.invFun (encode output)))
                (timeOverhead.eval (bitSize x + t))) := by
  obtain ⟨timeOverhead, hsim⟩ :=
    Lax51Proofs.RamToTM.ramInTime_to_turingInPolynomialOverhead p wordBound
  let widthOverhead : Polynomial ℕ :=
    polynomialSimpleMajorant wordBound + 1
  let H : TM2ComputableAux Symbol Symbol := {
    tm := ramSimulationTM p wordBound
    inputAlphabet := Equiv.refl Symbol
    outputAlphabet := Equiv.refl Symbol }
  refine ⟨H, widthOverhead, timeOverhead, ?_, ?_⟩
  · intro n
    calc
      wordBound.eval n ≤ (polynomialSimpleMajorant wordBound).eval n :=
        polynomial_eval_le_simpleMajorant wordBound n
      _ ≤ (polynomialSimpleMajorant wordBound).eval n + 1 := by omega
      _ = widthOverhead.eval n := by simp [widthOverhead]
  · intro x output t hfits hrun
    have hrun' :
        RunsTo (simulationWordWidth wordBound x) p
          (x.length :: x) output t := by
      simpa [simulationWordWidth, widthOverhead] using hrun
    have htm := hsim x output t hfits hrun'
    have hinputMap :
        List.map H.inputAlphabet.invFun (encode x) = encode x := by
      dsimp [H]
      exact map_refl_invFun (encode x)
    have houtputMap :
        List.map H.outputAlphabet.invFun (encode output) = encode output := by
      dsimp [H]
      exact map_refl_invFun (encode output)
    rw [hinputMap, houtputMap]
    exact htm

end Lax51Proofs.GenericTimeSimulation
