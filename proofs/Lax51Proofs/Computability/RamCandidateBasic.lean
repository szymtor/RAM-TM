import Lax51Proofs.Computability.SparseRam

namespace Lax51Proofs.Computability

open Lax51Proofs.Microcode Lax51Proofs.RamToTM

set_option maxHeartbeats 2000000

def sparseHaltOutput (p : Program) (w : ℕ) (s : SparseState) : Option (List ℕ) :=
  match sparseStep w p s with
  | none => some s.out
  | some _ => none

theorem sparseHaltOutput_primrec (p : Program) :
    Primrec fun q : ℕ × SparseState => sparseHaltOutput p q.1 q.2 := by
  have h := Primrec.option_casesOn (sparseStep_primrec p)
    (Primrec.option_some.comp effect_out_primrec)
    ((Primrec.const none).to₂ : Primrec₂ fun (_ : ℕ × SparseState)
      (_ : SparseState) => (none : Option (List ℕ)))
  exact h.of_eq fun q => by
    simp only [sparseHaltOutput]
    cases sparseStep q.1 p q.2 <;> rfl

def ramCandidateAt (p : Program) (w : ℕ) (x : List ℕ) (t : ℕ) :
    Option (List ℕ) :=
  (sparseRun w p t (sparseInitState (x.length :: x))).bind
    (sparseHaltOutput p w)

theorem ramCandidateAt_primrec (p : Program) :
    Primrec fun q : (ℕ × List ℕ) × ℕ =>
      ramCandidateAt p q.1.1 q.1.2 q.2 := by
  have hw : Primrec fun q : (ℕ × List ℕ) × ℕ => q.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hx : Primrec fun q : (ℕ × List ℕ) × ℕ => q.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hphysical : Primrec fun q : (ℕ × List ℕ) × ℕ =>
      q.1.2.length :: q.1.2 :=
    Primrec.list_cons.comp (Primrec.list_length.comp hx) hx
  have hinit : Primrec fun q : (ℕ × List ℕ) × ℕ =>
      sparseInitState (q.1.2.length :: q.1.2) :=
    sparseInitState_primrec.comp hphysical
  have hrun : Primrec fun q : (ℕ × List ℕ) × ℕ =>
      sparseRun q.1.1 p q.2
        (sparseInitState (q.1.2.length :: q.1.2)) :=
    (sparseRun_primrec p).comp
      (Primrec.pair (Primrec.pair hw Primrec.snd) hinit)
  have hfinish : Primrec₂ fun (q : (ℕ × List ℕ) × ℕ) (s : SparseState) =>
      sparseHaltOutput p q.1.1 s := by
    change Primrec fun z : (((ℕ × List ℕ) × ℕ) × SparseState) =>
      sparseHaltOutput p z.1.1.1 z.2
    exact (sparseHaltOutput_primrec p).comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd)
  exact (Primrec.option_bind hrun hfinish).of_eq fun _ => rfl

end Lax51Proofs.Computability
