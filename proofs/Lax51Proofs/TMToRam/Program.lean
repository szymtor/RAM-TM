import Lax13Proofs.Transfer
import Lax51.TuringPolytime

/-!
The Turing-to-RAM simulation is implemented through Lax13's verified IMP+
compiler. A finite Turing machine is first specialized to tables of natural
numbers encoding its finite stack, label, symbol, and state types. The IMP+
interpreter operates on those tables and on arrays representing the stacks;
`Lax13Proofs.Transfer` then supplies the low-level RAM program and its exact
simulation theorem.

This module fixes the numeric representation of a finite type. The concrete
interpreter and its invariant are built on this interface in subsequent
modules.
-/

namespace Lax51Proofs.TMToRam

/-- The numeric code of an element of a finite type, using its `Fintype`
enumeration. -/
noncomputable def finCode {α : Type} [Fintype α] [DecidableEq α] (a : α) : ℕ :=
  (Fintype.equivFin α a).val

theorem finCode_lt {α : Type} [Fintype α] [DecidableEq α] (a : α) :
    finCode a < Fintype.card α := by
  exact (Fintype.equivFin α a).isLt

theorem finCode_injective {α : Type} [Fintype α] [DecidableEq α] :
    Function.Injective (finCode : α → ℕ) := by
  intro a b h
  exact (Fintype.equivFin α).injective (Fin.ext h)

/-- Decode a finite enumeration code, rejecting numbers outside the finite
type's cardinality. -/
noncomputable def finDecode (α : Type) [Fintype α] (n : ℕ) : Option α :=
  if h : n < Fintype.card α then some ((Fintype.equivFin α).symm ⟨n, h⟩) else none

@[simp] theorem finDecode_finCode {α : Type} [Fintype α] [DecidableEq α] (a : α) :
    finDecode α (finCode a) = some a := by
  simp [finDecode, finCode, finCode_lt]

theorem finCode_of_finDecode_eq_some {α : Type} [Fintype α] [DecidableEq α]
    {n : ℕ} {a : α} (h : finDecode α n = some a) : finCode a = n := by
  unfold finDecode at h
  split at h
  · injection h with ha
    subst a
    simp [finCode]
  · contradiction

end Lax51Proofs.TMToRam
