import Lax759944Proofs.TMToRam.Computable
import Lax759944Proofs.RamToTM.Computable
import Lax759944.TuringToRamGenericTime
import Lax759944.RamToTuringGenericTime
import Lax759944Proofs.LegacyRamBridge
import Lax759944Proofs.TapeRamNativeLowering
import Lax759944Proofs.TapeRamGenericTime

namespace Lax759944Proofs.GenericTimeSimulation

open Lax759944Proofs.Legacy.Ram
open Lax759944.BinaryWordEncoding Lax759944Proofs.Legacy.RamPolytime
open Polynomial Turing

open Lax759944Proofs.RamToTM

private theorem map_refl_invFun (xs : List Symbol) :
    List.map (Equiv.refl Symbol).invFun xs = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      change a :: List.map (Equiv.refl Symbol).invFun xs = a :: xs
      rw [ih]

/--
---
conclusion: Lax759944.TuringToRamGenericTime.turingWithInputTime_to_ramInPolynomialOverhead
---
-/
theorem turingWithInputTime_to_ramInPolynomialOverhead
    {f : List ℕ → List ℕ}
    (H : TM2ComputableAux Symbol Symbol) (time : List ℕ → ℕ)
    (hrun : ∀ x, TM2OutputsInTime H.tm
      (List.map H.inputAlphabet.invFun (encode x))
      (some (List.map H.outputAlphabet.invFun (encode (f x)))) (time x)) :
    ∃ (p : Lax808846.Ram.Program) (wordOverhead timeOverhead : Polynomial ℕ),
      ∀ (x : List ℕ) (w : ℕ),
        wordOverhead.eval (bitSize x + time x) ≤ w →
          ∃ t ≤ timeOverhead.eval (bitSize x + time x),
            Lax808846.Ram.RunsTo w p (x.length :: x) (f x) t := by
  obtain ⟨p, wordOverhead, timeOverhead, hp⟩ :=
    Lax759944Proofs.TMToRam.turingWithInputTime_to_ramInPolynomialOverhead H time hrun
  refine ⟨LegacyRamBridge.embedProgram p, wordOverhead, timeOverhead + 1, ?_⟩
  intro x w hw
  obtain ⟨t, ht, hr⟩ := hp x w hw
  obtain ⟨u, _, hu, hr'⟩ := LegacyRamBridge.runsTo hr
  refine ⟨u, ?_, hr'⟩
  simpa using hu.trans (Nat.add_le_add_right ht 1)

/-- Historical simulation helper for the sequential instruction set.
The public new-model simulation additionally needs indexed input and EOF. -/
theorem legacyRamInTime_to_turingInPolynomialOverhead
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
    Lax759944Proofs.RamToTM.ramInTime_to_turingInPolynomialOverhead
      (CellToMicrocode.compile p) wordBound
  let widthOverhead : Polynomial ℕ :=
    polynomialSimpleMajorant wordBound + 1
  let H : TM2ComputableAux Symbol Symbol := {
    tm := ramSimulationTM (CellToMicrocode.compile p) wordBound
    inputAlphabet := Equiv.refl Symbol
    outputAlphabet := Equiv.refl Symbol }
  refine ⟨H, widthOverhead, timeOverhead.comp (3 * Polynomial.X), ?_, ?_⟩
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
    obtain ⟨htm⟩ := hsim x output (3 * t) hfits (CellToMicrocode.runsTo hrun')
    have hinputMap :
        List.map H.inputAlphabet.invFun (encode x) = encode x := by
      dsimp [H]
      exact map_refl_invFun (encode x)
    have houtputMap :
        List.map H.outputAlphabet.invFun (encode output) = encode output := by
      dsimp [H]
      exact map_refl_invFun (encode output)
    rw [hinputMap, houtputMap]
    refine ⟨{ htm with steps_le_m := htm.steps_le_m.trans ?_ }⟩
    simp only [Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X]
    exact polynomial_eval_mono timeOverhead (by omega)

/--
---
conclusion: Lax759944.RamToTuringGenericTime.ramInTime_to_turingInPolynomialOverhead
---
Snapshot the exact length-prefixed input during the measured run, eliminate
the extended input instructions with the verified buffer compiler, then run
the existing Turing simulation at polynomially bounded word width.
-/
theorem ramInTime_to_turingInPolynomialOverhead
    (program : Lax808846.Ram.Program) (wordBound : Polynomial ℕ) :
    ∃ (H : TM2ComputableAux Symbol Symbol)
        (widthOverhead timeOverhead : Polynomial ℕ),
      (∀ n, wordBound.eval n ≤ widthOverhead.eval n) ∧
        ∀ (input output : List ℕ) (time : ℕ),
          Lax759944.RamPolytime.FitsInWords (wordBound.eval (bitSize input))
              ((input.length :: input) ++ output) →
            Lax808846.Ram.RunsTo (widthOverhead.eval (bitSize input)) program
                (input.length :: input) output time →
              Nonempty (TM2OutputsInTime H.tm
                (List.map H.inputAlphabet.invFun (encode input))
                (some (List.map H.outputAlphabet.invFun (encode output)))
                (timeOverhead.eval (bitSize input + time))) :=
  TapeRamGenericTime.genericTime_of_lowering TapeRamNativeLowering.lower
    TapeRamNativeLowering.runsTo Encoding.length_le_bitSize program wordBound

end Lax759944Proofs.GenericTimeSimulation
