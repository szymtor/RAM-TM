import Lax20Proofs.TMToRam.ReachableSymbols

/-!
Numeric representations of the finite control and reachable stack contents
of a bundled `FinTM2`. These are the semantic values represented by the
scalars and arrays of the IMP+ interpreter.
-/

namespace Lax20Proofs.TMToRam

open Turing

/-- Code an available symbol when supplied the reachability proof which
makes it an element of the finite available alphabet. -/
noncomputable def FinTM2.codeSymbol (tm : FinTM2) {k : tm.K} (a : tm.Γ k)
    (ha : (⟨k, a⟩ : Σ k, tm.Γ k) ∈ availableSymbols tm) : ℕ :=
  @finCode (AvailableAt tm k) (FinTM2.AvailableAt.instFintype tm k)
    (FinTM2.AvailableAt.instDecidableEq tm k) ⟨a, ha⟩

/-- Encode a stack whose symbols all belong to the finite available
alphabet. -/
noncomputable def FinTM2.codeStack (tm : FinTM2) (k : tm.K) (xs : List (tm.Γ k))
    (hxs : ∀ a ∈ xs, (⟨k, a⟩ : Σ k, tm.Γ k) ∈ availableSymbols tm) : List ℕ :=
  xs.attach.map fun a => codeSymbol tm a.1 (hxs a.1 a.2)

@[simp] theorem FinTM2.codeStack_nil (tm : FinTM2) (k : tm.K)
    (hxs : ∀ a ∈ ([] : List (tm.Γ k)),
      (⟨k, a⟩ : Σ k, tm.Γ k) ∈ availableSymbols tm) :
    codeStack tm k [] hxs = [] := by
  simp [codeStack]

@[simp] theorem FinTM2.codeStack_cons (tm : FinTM2) (k : tm.K) (a : tm.Γ k)
    (xs : List (tm.Γ k))
    (hxs : ∀ b ∈ a :: xs, (⟨k, b⟩ : Σ k, tm.Γ k) ∈ availableSymbols tm) :
    codeStack tm k (a :: xs) hxs =
      codeSymbol tm a (hxs a (by simp)) ::
        codeStack tm k xs (fun b hb => hxs b (by simp [hb])) := by
  simp [codeStack]

theorem FinTM2.codeStack_tail (tm : FinTM2) (k : tm.K) (xs : List (tm.Γ k))
    (hxs : ∀ a ∈ xs, (⟨k, a⟩ : Σ k, tm.Γ k) ∈ availableSymbols tm) :
    (codeStack tm k xs hxs).tail =
      codeStack tm k xs.tail (fun a ha => hxs a (List.mem_of_mem_tail ha)) := by
  cases xs <;> simp

/-- The typed head of a stack, carrying its availability certificate. -/
def FinTM2.availableHeadOption (tm : FinTM2) (k : tm.K) (xs : List (tm.Γ k))
    (hxs : ∀ a ∈ xs, (⟨k, a⟩ : Σ k, tm.Γ k) ∈ availableSymbols tm) :
    Option (AvailableAt tm k) := by
  cases xs with
  | nil => exact none
  | cons a xs => exact some ⟨a, hxs a (by simp)⟩

@[simp] theorem FinTM2.availableHeadOption_map (tm : FinTM2) (k : tm.K)
    (xs : List (tm.Γ k))
    (hxs : ∀ a ∈ xs, (⟨k, a⟩ : Σ k, tm.Γ k) ∈ availableSymbols tm) :
    (availableHeadOption tm k xs hxs).map Subtype.val = xs.head? := by
  cases xs <;> rfl

@[simp] theorem FinTM2.availableHeadOption_unattach (tm : FinTM2) (k : tm.K)
    (xs : List (tm.Γ k))
    (hxs : ∀ a ∈ xs, (⟨k, a⟩ : Σ k, tm.Γ k) ∈ availableSymbols tm) :
    (availableHeadOption tm k xs hxs).unattach = xs.head? := by
  cases xs <;> rfl

@[simp] theorem FinTM2.codeStack_length (tm : FinTM2) (k : tm.K) (xs : List (tm.Γ k))
    (hxs : ∀ a ∈ xs, (⟨k, a⟩ : Σ k, tm.Γ k) ∈ availableSymbols tm) :
    (codeStack tm k xs hxs).length = xs.length := by
  simp [codeStack]

/-- The purely numeric image of a Turing configuration. `none` is the halt
label; present labels, the internal state, stack indices, and stack symbols
use their finite-type enumeration codes. -/
structure FinTM2.NumericConfig (tm : FinTM2) where
  label : Option ℕ
  state : ℕ
  stackData : tm.K → List ℕ

/-- Encode a Turing configuration whose stacks satisfy the available-symbol
invariant. -/
noncomputable def FinTM2.encodeConfig (tm : FinTM2) (c : tm.Cfg)
    (hc : StacksWithin (availableSymbols tm) c.stk) : NumericConfig tm := by
  letI := tm.ΛFin
  letI := tm.σFin
  letI : DecidableEq tm.Λ := Classical.decEq _
  letI : DecidableEq tm.σ := Classical.decEq _
  exact {
  label := c.l.map (finCode : tm.Λ → ℕ)
  state := finCode c.var
  stackData := fun k => codeStack tm k (c.stk k) (fun a ha => hc k a ha)
  }

theorem FinTM2.encodeConfig_state_lt (tm : FinTM2) (c : tm.Cfg)
    (hc : StacksWithin (availableSymbols tm) c.stk) :
    (encodeConfig tm c hc).state < @Fintype.card tm.σ tm.σFin := by
  letI := tm.σFin
  letI : DecidableEq tm.σ := Classical.decEq _
  exact finCode_lt c.var

theorem FinTM2.encodeConfig_stack_length (tm : FinTM2) (c : tm.Cfg)
    (hc : StacksWithin (availableSymbols tm) c.stk) (k : tm.K) :
    ((encodeConfig tm c hc).stackData k).length = (c.stk k).length := by
  simp [encodeConfig, codeStack]

end Lax20Proofs.TMToRam
