import Lax20Proofs.TMToRam.ConfigEncoding

/-!
Finite control functions in a `TM2.Stmt` are compiled to literal lookup
tables. The domain enumeration code is exactly the table index, avoiding a
linear search and making each control-function evaluation one IMP+ array
read after its arguments have been flattened to a finite index.
-/

namespace Lax20Proofs.TMToRam

theorem getD_ofFn {n : ℕ} (f : Fin n → ℕ) (i d : ℕ) (hi : i < n) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem (List.ofFn f) d (by simpa using hi)]
  simp

/-- The value table of a function between finite types, ordered by the
canonical `Fintype.equivFin` enumeration of its domain. -/
noncomputable def unaryTable {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (f : α → β) : List ℕ :=
  List.ofFn fun i : Fin (Fintype.card α) => finCode (f ((Fintype.equivFin α).symm i))

@[simp] theorem unaryTable_length {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (f : α → β) :
    (unaryTable f).length = Fintype.card α := by
  simp [unaryTable]

/-- Looking up the code of an argument returns the code of its image. -/
theorem unaryTable_getElem {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (f : α → β) (a : α) :
    (unaryTable f)[finCode a]'(by rw [unaryTable_length]; exact finCode_lt a) =
      finCode (f a) := by
  simp [unaryTable, finCode]

theorem unaryTable_getD {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (f : α → β) (a : α) (d : ℕ) :
    (unaryTable f).getD (finCode a) d = finCode (f a) := by
  rw [List.getD_eq_getElem _ _ (by
    rw [unaryTable_length]
    exact finCode_lt a)]
  exact unaryTable_getElem f a

/-- Flatten a pair of finite enumeration codes to a row-major table index. -/
noncomputable def pairIndex {α β : Type} [Fintype β] [DecidableEq α] [DecidableEq β]
    [Fintype α] (a : α) (b : β) : ℕ :=
  finCode (a, b)

/-- A binary finite-control function as a row-major literal table. -/
noncomputable def binaryTable {α β γ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (f : α → β → γ) : List ℕ :=
  unaryTable (fun p : α × β => f p.1 p.2)

/-- Looking up a pair code in the binary table returns the image code. -/
theorem binaryTable_getElem {α β γ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (f : α → β → γ) (a : α) (b : β) :
    (binaryTable f)[pairIndex a b]'(by
      rw [show (binaryTable f).length = Fintype.card (α × β) by
        simp [binaryTable]]
      exact finCode_lt (a, b)) = finCode (f a b) := by
  simpa [binaryTable, pairIndex] using
    (unaryTable_getElem (fun p : α × β => f p.1 p.2) (a, b))

end Lax20Proofs.TMToRam
