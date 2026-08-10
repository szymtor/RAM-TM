import Lax51Proofs.Computability.PartrecRuntime

namespace Lax51Proofs.Computability

open Turing Lax51Proofs.TMToRam
open PartrecFiniteTM2

set_option maxHeartbeats 2000000

theorem partrecPhysicalHaltsAt_iff (c : ToPartrec.Code)
    (x : List ℕ) (t : ℕ) :
    PartrecPhysicalHaltsAt c x t ↔
      ∃ s : SparseNumericState,
        sparseNumericIter (machine c) t
            (partrecSparseInit c (x.length :: x)) = some s ∧
          s.label = none := by
  unfold PartrecPhysicalHaltsAt partrecPhysicalHaltedBool
  cases hs : sparseNumericIter (machine c) t
      (partrecSparseInit c (x.length :: x)) with
  | none => simp [hs, sparseNumericHalted]
  | some s =>
      cases hlabel : s.label with
      | none => simp [hs, sparseNumericHalted, hlabel]
      | some label => simp [hs, sparseNumericHalted, hlabel]

noncomputable instance partrecPhysicalHaltsAt_decidable (c : ToPartrec.Code) :
    DecidableRel (PartrecPhysicalHaltsAt c) := by
  intro x t
  unfold PartrecPhysicalHaltsAt
  infer_instance

noncomputable def partrecPhysicalRunningTime (c : ToPartrec.Code)
    {f : List ℕ → List ℕ}
    (h : ∀ x, c.eval (x.length :: x) = pure (f x))
    (x : List ℕ) : ℕ :=
  Nat.find (partrecPhysicalHaltsAt_exists h x)

theorem partrecPhysicalRunningTime_computable (c : ToPartrec.Code)
    {f : List ℕ → List ℕ}
    (h : ∀ x, c.eval (x.length :: x) = pure (f x)) :
    Computable (partrecPhysicalRunningTime c h) := by
  simpa [partrecPhysicalRunningTime] using
    Computable.find (partrecPhysicalHaltsAt_computablePred c)
      (partrecPhysicalHaltsAt_exists h)

noncomputable def partrec_outputsInComputableRunningTime (c : ToPartrec.Code)
    {f : List ℕ → List ℕ}
    (h : ∀ x, c.eval (x.length :: x) = pure (f x)) (x : List ℕ) :
    TM2OutputsInTime (machine c)
      (Turing.PartrecToTM2.trList (x.length :: x))
      (some (Turing.PartrecToTM2.trList (f x)))
      (partrecPhysicalRunningTime c h x) := by
  let found := partrecPhysicalRunningTime c h x
  have hfound : PartrecPhysicalHaltsAt c x found := by
    simpa [found, partrecPhysicalRunningTime] using
      Nat.find_spec (partrecPhysicalHaltsAt_exists h x)
  let hexFound := (partrecPhysicalHaltsAt_iff c x found).mp hfound
  let sf := Classical.choose hexFound
  have hrunFound := (Classical.choose_spec hexFound).1
  have hhaltFound := (Classical.choose_spec hexFound).2
  let typed := PartrecFiniteTM2.outputs (h x)
  let hexTyped := partrecSparseHalt_of_eval (h x)
  let st := Classical.choose hexTyped
  have hrunTyped := (Classical.choose_spec hexTyped).1
  have hhaltTyped := (Classical.choose_spec hexTyped).2
  have hstepFound : sparseNumericStep (machine c) sf = none := by
    unfold sparseNumericStep
    rw [hhaltFound]
  have hstepTyped : sparseNumericStep (machine c) st = none := by
    unfold sparseNumericStep
    rw [hhaltTyped]
  have htime : typed.steps = found := by
    exact optionIter_halt_time_unique (sparseNumericStep (machine c))
      hrunTyped hstepTyped hrunFound hstepFound
  refine ⟨typed, ?_⟩
  simpa [found] using htime.le

end Lax51Proofs.Computability
