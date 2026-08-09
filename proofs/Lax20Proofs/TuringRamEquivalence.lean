import Lax20.TuringRamEquivalence
import Lax20Proofs.Computability.RamEvaluator
import Lax20Proofs.Computability.PartrecRuntimeSearch
import Lax20Proofs.Computability.ToPartrecList
import Lax20Proofs.Computability.PartrecToRam

namespace Lax20Proofs.Computability

open Lax13.Ram
open Lax20.BinaryWordEncoding
open PartrecNativeCodec

theorem bitSize_primrec : Primrec bitSize := by
  exact (Primrec.list_length.comp
    (encodePartrecListCodes_primrec 0 0 0)).of_eq fun x => by
      rw [encodePartrecListCodes_length]

theorem polynomial_eval_primrec (p : Polynomial ℕ) : Primrec p.eval := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      exact (Primrec.nat_add.comp hp hq).of_eq fun x => by
        simp
  | monomial n a =>
      have hpow : Primrec fun x : ℕ => x ^ n := by
        induction n with
        | zero => simpa using (Primrec.const 1 : Primrec fun _x : ℕ => 1)
        | succ n ih =>
            exact (Primrec.nat_mul.comp ih Primrec.id).of_eq fun x => by
              simp [pow_succ]
      exact (Primrec.nat_mul.comp (Primrec.const a) hpow).of_eq fun x => by
        simp [Polynomial.eval_monomial]

theorem computable_to_ramComputable {f : List ℕ → List ℕ}
    (hf : Computable f) :
    Lax20.TuringRamEquivalence.RamComputable f := by
  let c := computableListCode f hf
  have heval : ∀ x, c.eval (x.length :: x) = pure (f x) := by
    intro x
    simpa [c] using computableListCode_eval f hf x
  let time := partrecPhysicalRunningTime c heval
  have htime : Computable time := by
    exact partrecPhysicalRunningTime_computable c heval
  obtain ⟨p, wordOverhead, _timeOverhead, hram⟩ :=
    partrecWithInputTime_to_ramInPolynomialOverhead c time
      (partrec_outputsInComputableRunningTime c heval)
  let threshold := fun x =>
    wordOverhead.eval (bitSize x + time x)
  have hthreshold : Computable threshold := by
    have harg : Computable fun x => bitSize x + time x :=
      Primrec.nat_add.to_comp.to₂.comp bitSize_primrec.to_comp htime
    exact (polynomial_eval_primrec wordOverhead).to_comp.comp harg
  refine ⟨p, threshold, hthreshold, ?_⟩
  intro x w hw
  obtain ⟨t, _ht, hrun⟩ := hram x w (by simpa [threshold] using hw)
  exact ⟨t, hrun⟩

end Lax20Proofs.Computability

namespace Lax20Proofs.TuringRamEquivalence

open Lax20.TuringRamEquivalence

/--
---
conclusion: Lax20.TuringRamEquivalence.ramComputable_iff_computable
---
**Equivalence of Turing machines and word RAMs.** -/
theorem ramComputable_iff_computable (f : List ℕ → List ℕ) :
    RamComputable f ↔ Computable f := by
  constructor
  · exact Lax20Proofs.Computability.ramComputable_to_computable
  · exact Lax20Proofs.Computability.computable_to_ramComputable

end Lax20Proofs.TuringRamEquivalence
