import Lax759944Proofs.RamToTM.Computable
import Lax759944Proofs.CellToMicrocode
import Lax759944.RamToTuringGenericTime

namespace Lax759944Proofs.TapeRamGenericTime

open Lax759944.BinaryWordEncoding Polynomial Turing
open Lax759944Proofs.RamToTM

private theorem map_refl_invFun (xs : List Symbol) :
    List.map (Equiv.refl Symbol).invFun xs = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      change a :: List.map (Equiv.refl Symbol).invFun xs = a :: xs
      rw [ih]

/-- Generic-time transfer through an explicit verified input-buffer compiler.
The selected source width is polynomial; its one-bit larger legacy execution
is the width used by the existing Turing simulation. -/
theorem genericTime_of_lowering
    (lower : Lax808846.Ram.Program → Legacy.Ram.Program)
    (hlower : ∀ (p : Lax808846.Ram.Program) (v : ℕ)
        (x output : List ℕ) (t : ℕ),
      (∀ a ∈ x.length :: x, a < 2 ^ v) →
      x.length + 33 < 2 ^ v →
      Lax808846.Ram.RunsTo v p (x.length :: x) output t →
      ∃ u ≤ 18 * t + 6 * (x.length + 1) + 26,
        Legacy.Ram.RunsTo (v + 1) (lower p) (x.length :: x) output u)
    (hlength : ∀ x : List ℕ, x.length ≤ bitSize x)
    (p : Lax808846.Ram.Program) (wordBound : Polynomial ℕ) :
    ∃ (H : TM2ComputableAux Symbol Symbol)
        (widthOverhead timeOverhead : Polynomial ℕ),
      (∀ n, wordBound.eval n ≤ widthOverhead.eval n) ∧
        ∀ (x output : List ℕ) (t : ℕ),
          Lax759944.RamPolytime.FitsInWords (wordBound.eval (bitSize x))
              ((x.length :: x) ++ output) →
            Lax808846.Ram.RunsTo (widthOverhead.eval (bitSize x)) p
                (x.length :: x) output t →
              Nonempty (TM2OutputsInTime H.tm
                (List.map H.inputAlphabet.invFun (encode x))
                (some (List.map H.outputAlphabet.invFun (encode output)))
                (timeOverhead.eval (bitSize x + t))) := by
  let enlarged := wordBound + Polynomial.X + Polynomial.C 7
  let widthOverhead := polynomialSimpleMajorant enlarged
  obtain ⟨timeOverhead, hsim⟩ :=
    Lax759944Proofs.RamToTM.ramInTime_to_turingInPolynomialOverhead
      (CellToMicrocode.compile (lower p)) enlarged
  let H : TM2ComputableAux Symbol Symbol := {
    tm := ramSimulationTM (CellToMicrocode.compile (lower p)) enlarged
    inputAlphabet := Equiv.refl Symbol
    outputAlphabet := Equiv.refl Symbol }
  have hwidth (n : ℕ) : wordBound.eval n + 7 ≤ widthOverhead.eval n := by
    have h : enlarged.eval n ≤ widthOverhead.eval n :=
      polynomial_eval_le_simpleMajorant enlarged n
    apply le_trans (b := enlarged.eval n) ?_ h
    simp only [enlarged, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    omega
  refine ⟨H, widthOverhead,
    timeOverhead.comp (Polynomial.C 100 * (Polynomial.X + 1)), ?_, ?_⟩
  · intro n
    have := hwidth n
    omega
  · intro x output t hfits hrun
    let v := widthOverhead.eval (bitSize x)
    have hqv : wordBound.eval (bitSize x) + 6 ≤ v := by
      have := hwidth (bitSize x)
      dsimp [v]
      omega
    have hq : wordBound.eval (bitSize x) ≤ v := by omega
    have hinput : ∀ a ∈ x.length :: x, a < 2 ^ v := by
      intro a ha
      exact (hfits a (List.mem_append_left _ ha)).trans_le
        (Nat.pow_le_pow_right (by decide) hq)
    have hn : x.length < 2 ^ wordBound.eval (bitSize x) :=
      hfits x.length (by simp)
    have hpow : 2 ^ wordBound.eval (bitSize x) * 64 ≤ 2 ^ v := by
      simpa [Nat.pow_add] using
        (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hqv)
    have hspace : x.length + 33 < 2 ^ v := by
      have := Nat.two_pow_pos (wordBound.eval (bitSize x))
      omega
    obtain ⟨u, hu, hr⟩ := hlower p v x output t hinput hspace hrun
    have hr' : Legacy.Ram.RunsTo (simulationWordWidth enlarged x)
        (lower p) (x.length :: x) output u := by
      simpa [simulationWordWidth, v, widthOverhead] using hr
    have hfits' : Legacy.RamPolytime.FitsInWords (enlarged.eval (bitSize x))
        ((x.length :: x) ++ output) := by
      intro a ha
      apply (hfits a ha).trans_le
      apply Nat.pow_le_pow_right (by decide)
      simp only [enlarged, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      omega
    obtain ⟨htm⟩ := hsim x output (3 * u) hfits' (CellToMicrocode.runsTo hr')
    have hinputMap : List.map H.inputAlphabet.invFun (encode x) = encode x := by
      dsimp [H]
      exact map_refl_invFun (encode x)
    have houtputMap : List.map H.outputAlphabet.invFun (encode output) = encode output := by
      dsimp [H]
      exact map_refl_invFun (encode output)
    rw [hinputMap, houtputMap]
    refine ⟨{ htm with steps_le_m := htm.steps_le_m.trans ?_ }⟩
    simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    apply polynomial_eval_mono timeOverhead
    have hnbit := hlength x
    omega

end Lax759944Proofs.TapeRamGenericTime
