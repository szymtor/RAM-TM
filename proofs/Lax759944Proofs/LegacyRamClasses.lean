import Lax759944.RamPolytime
import Lax759944.TuringRamEquivalence
import Lax759944Proofs.Legacy.RamPolytime
import Lax759944Proofs.Legacy.TuringRamEquivalence
import Lax759944Proofs.LegacyRamBridge

namespace Lax759944Proofs.LegacyRamClasses

open Lax759944.BinaryWordEncoding

theorem computable_forward {f : List ℕ → List ℕ}
    (hf : Legacy.TuringRamEquivalence.RamComputable f) :
    Lax759944.TuringRamEquivalence.RamComputable f := by
  obtain ⟨p, threshold, hthreshold, hp⟩ := hf
  refine ⟨LegacyRamBridge.embedProgram p, threshold, hthreshold, ?_⟩
  intro x w hw
  obtain ⟨t, ht⟩ := hp x w hw
  obtain ⟨u, _, _, hu⟩ := LegacyRamBridge.runsTo ht
  exact ⟨u, hu⟩

theorem polytime_forward {f : List ℕ → List ℕ}
    (hf : Legacy.RamPolytime.RamPolytime f) :
    Lax759944.RamPolytime.RamPolytime f := by
  obtain ⟨p, wordBound, timeBound, hp⟩ := hf
  refine ⟨LegacyRamBridge.embedProgram p, wordBound, timeBound + 1, ?_⟩
  intro x
  refine ⟨(hp x).1, ?_⟩
  intro w hw
  obtain ⟨t, ht, hr⟩ := (hp x).2 w hw
  obtain ⟨u, _, hu, hr'⟩ := LegacyRamBridge.runsTo hr
  refine ⟨u, ?_, hr'⟩
  simpa using hu.trans (Nat.add_le_add_right ht 1)

/-- Polynomial-class transfer once a concrete input-buffer compiler has
been verified. The hypothesis covers every extended-model program and every
input in its fitting domain; it is not an instruction-set restriction. -/
theorem polytime_backward_of_lowering
    (lower : Lax808846.Ram.Program → Legacy.Ram.Program)
    (hlower : ∀ (p : Lax808846.Ram.Program) (v : ℕ)
        (x output : List ℕ) (t : ℕ),
      (∀ a ∈ x.length :: x, a < 2 ^ v) →
      x.length + 33 < 2 ^ v →
      Lax808846.Ram.RunsTo v p (x.length :: x) output t →
      ∃ u ≤ 18 * t + 6 * (x.length + 1) + 26,
        Legacy.Ram.RunsTo (v + 1) (lower p) (x.length :: x) output u)
    {f : List ℕ → List ℕ} (hf : Lax759944.RamPolytime.RamPolytime f)
    (hlength : ∀ x : List ℕ, x.length ≤ bitSize x) :
    Legacy.RamPolytime.RamPolytime f := by
  obtain ⟨p, wordBound, timeBound, hp⟩ := hf
  let newWord := wordBound + Polynomial.C 7
  let newTime := Polynomial.C 18 * timeBound + Polynomial.C 6 * Polynomial.X +
    Polynomial.C 32
  refine ⟨lower p, newWord, newTime, ?_⟩
  intro x
  have hweval : newWord.eval (bitSize x) = wordBound.eval (bitSize x) + 7 := by
    simp [newWord]
  constructor
  · intro a ha
    exact ((hp x).1 a ha).trans_le
      (Nat.pow_le_pow_right (by decide) (by rw [hweval]; omega))
  · intro w hw
    let v := w - 1
    have hv : v + 1 = w := by dsimp [v]; rw [hweval] at hw; omega
    have hqv : wordBound.eval (bitSize x) + 6 ≤ v := by
      dsimp [v]; rw [hweval] at hw; omega
    have hq : wordBound.eval (bitSize x) ≤ v := by omega
    have hfit : ∀ a ∈ x.length :: x, a < 2 ^ v := by
      intro a ha
      exact ((hp x).1 a (List.mem_append_left _ ha)).trans_le
        (Nat.pow_le_pow_right (by decide) hq)
    have hn : x.length < 2 ^ wordBound.eval (bitSize x) :=
      (hp x).1 x.length (by simp)
    have hpow : 2 ^ wordBound.eval (bitSize x) * 64 ≤ 2 ^ v := by
      simpa [Nat.pow_add] using
        (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hqv)
    have hspace : x.length + 33 < 2 ^ v := by
      have := Nat.two_pow_pos (wordBound.eval (bitSize x))
      omega
    obtain ⟨t, ht, hr⟩ := (hp x).2 v hq
    obtain ⟨u, hu, hr'⟩ := hlower p v x (f x) t hfit hspace hr
    refine ⟨u, ?_, ?_⟩
    · have hnbit := hlength x
      simp only [newTime, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      omega
    · simpa [hv] using hr'

end Lax759944Proofs.LegacyRamClasses
