import Lax20.TuringRamEquivalence
import Lax20Proofs.Computability.RamCandidateBasic

namespace Lax20Proofs.Computability

open Lax13.Ram Lax20Proofs.RamToTM

set_option maxHeartbeats 2000000

def ramCandidate (p : Program) (threshold : List ℕ → ℕ)
    (x : List ℕ) (t : ℕ) : Option (List ℕ) :=
  ramCandidateAt p (threshold x) x t

theorem ramCandidate_computable₂ (p : Program) (threshold : List ℕ → ℕ)
    (hthreshold : Computable threshold) :
    Computable₂ (ramCandidate p threshold) := by
  change Computable fun q : List ℕ × ℕ => ramCandidate p threshold q.1 q.2
  exact (ramCandidateAt_primrec p).to_comp.comp
    (Computable.pair
      (Computable.pair (hthreshold.comp Computable.fst) Computable.fst)
      Computable.snd)

theorem runsTo_of_sparse_halt {w : ℕ} {p : Program} {input output : List ℕ}
    {t : ℕ} {s : SparseState}
    (hrun : sparseRun w p t (sparseInitState input) = some s)
    (hhalt : sparseStep w p s = none) (hout : s.out = output) :
    RunsTo w p input output t := by
  refine ⟨s.toState, ?_, ?_, ?_⟩
  · have h := sparseRun_toState w p t (sparseInitState input)
    simpa [hrun] using h.symm
  · have h := sparseStep_toState w p s
    simpa [hhalt] using h.symm
  · simpa [hout]

theorem runsTo_of_ramCandidate {p : Program} {threshold : List ℕ → ℕ}
    {x output : List ℕ} {t : ℕ}
    (h : ramCandidate p threshold x t = some output) :
    RunsTo (threshold x) p (x.length :: x) output t := by
  unfold ramCandidate ramCandidateAt at h
  cases hrun : sparseRun (threshold x) p t
      (sparseInitState (x.length :: x)) with
  | none => simp [hrun] at h
  | some s =>
      simp only [hrun, Option.bind_some] at h
      unfold sparseHaltOutput at h
      cases hhalt : sparseStep (threshold x) p s with
      | some s' => simp [hhalt] at h
      | none =>
          simp [hhalt] at h
          subst output
          exact runsTo_of_sparse_halt hrun hhalt rfl

theorem ramCandidate_exists_of_runsTo {p : Program} {threshold : List ℕ → ℕ}
    {x output : List ℕ} {t : ℕ}
    (h : RunsTo (threshold x) p (x.length :: x) output t) :
    ramCandidate p threshold x t = some output := by
  rcases sparse_halts_of_runsTo h with ⟨s, hrun, hhalt, hout, _⟩
  simp [ramCandidate, ramCandidateAt, hrun, sparseHaltOutput, hhalt, hout]

theorem run_add (w : ℕ) (p : Program) (m n : ℕ) (s : State) :
    run w p (m + n) s = (run w p m s).bind (run w p n) := by
  induction m generalizing s with
  | zero => simp [run]
  | succ m ih =>
      simp only [Nat.succ_add, run]
      cases hs : step w p s with
      | none => simp [hs]
      | some s' => simp [hs, ih]

theorem run_positive_of_halt {w : ℕ} {p : Program} {s : State}
    (hhalt : step w p s = none) {t : ℕ} (ht : 0 < t) :
    run w p t s = none := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  simp [run, hhalt]

theorem runsTo_output_unique {w : ℕ} {p : Program} {input y z : List ℕ}
    {t u : ℕ} (hy : RunsTo w p input y t) (hz : RunsTo w p input z u) :
    y = z := by
  rcases hy with ⟨sy, hry, hhy, hoy⟩
  rcases hz with ⟨sz, hrz, hhz, hoz⟩
  have htu : t = u := by
    rcases lt_trichotomy t u with hlt | heq | hgt
    · have hu : u = t + (u - t) := by omega
      rw [hu, run_add, hry] at hrz
      simp only [Option.bind_some] at hrz
      have hpos : 0 < u - t := by omega
      rw [run_positive_of_halt hhy hpos] at hrz
      simp at hrz
    · exact heq
    · have ht : t = u + (t - u) := by omega
      rw [ht, run_add, hrz] at hry
      simp only [Option.bind_some] at hry
      have hpos : 0 < t - u := by omega
      rw [run_positive_of_halt hhz hpos] at hry
      simp at hry
  subst u
  have hs : sy = sz := by simpa [hry] using hrz
  subst sz
  exact hoy.symm.trans hoz

theorem ramComputable_to_computable {f : List ℕ → List ℕ}
    (hf : Lax20.TuringRamEquivalence.RamComputable f) : Computable f := by
  rcases hf with ⟨p, threshold, hthreshold, hram⟩
  have hcand := ramCandidate_computable₂ p threshold hthreshold
  have hsearch : Partrec fun x : List ℕ =>
      Nat.rfindOpt (ramCandidate p threshold x) :=
    Partrec.rfindOpt hcand
  apply hsearch.of_eq_tot
  intro x
  obtain ⟨t, ht⟩ := hram x (threshold x) le_rfl
  have hcand_t : ramCandidate p threshold x t = some (f x) :=
    ramCandidate_exists_of_runsTo ht
  have hdom : (Nat.rfindOpt (ramCandidate p threshold x)).Dom :=
    Nat.rfindOpt_dom.2 ⟨t, f x, by simp [hcand_t]⟩
  refine ⟨hdom, ?_⟩
  obtain ⟨k, hk⟩ := Nat.rfindOpt_spec (Part.get_mem hdom)
  rw [Option.mem_def] at hk
  have hfound := runsTo_of_ramCandidate hk
  exact runsTo_output_unique hfound ht

end Lax20Proofs.Computability
