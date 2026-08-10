import Lax51Proofs.TMToRam.LookupTables

/-!
A finite, untyped instruction tree obtained from `TM2.Stmt`. All dependent
stack symbols and finite-control functions have been replaced by natural
codes and literal lookup tables. This is the direct semantic input of the
IMP+ interpreter.
-/

namespace Lax51Proofs.TMToRam

open Turing

/-- Numeric option encoding: zero for `none`, and one plus the finite code
for `some`. -/
noncomputable def optionCode {α : Type} [Fintype α] [DecidableEq α] : Option α → ℕ
  | none => 0
  | some a => finCode a + 1

noncomputable def FinTM2.stateCode (tm : FinTM2) (s : tm.σ) : ℕ :=
  @finCode tm.σ tm.σFin (Classical.decEq _) s

noncomputable def FinTM2.headOptionCode (tm : FinTM2) (k : tm.K)
    (o : Option (FinTM2.AvailableAt tm k)) : ℕ :=
  @optionCode (FinTM2.AvailableAt tm k) (FinTM2.AvailableAt.instFintype tm k)
    (FinTM2.AvailableAt.instDecidableEq tm k) o

/-- Decode the zero/successor option convention inside its exact finite
range. -/
noncomputable def decodeOptionIndex (α : Type) [Fintype α]
    (i : Fin (Fintype.card α + 1)) : Option α :=
  if h : i.val = 0 then none
  else some ((Fintype.equivFin α).symm ⟨i.val - 1, by omega⟩)

theorem optionCode_lt {α : Type} [Fintype α] [DecidableEq α] (o : Option α) :
    optionCode o < Fintype.card α + 1 := by
  cases o with
  | none => simp [optionCode]
  | some a => simp [optionCode, finCode_lt]

@[simp] theorem decodeOptionIndex_optionCode {α : Type} [Fintype α] [DecidableEq α]
    (o : Option α) :
    decodeOptionIndex α ⟨optionCode o, optionCode_lt o⟩ = o := by
  cases o with
  | none => simp [decodeOptionIndex, optionCode]
  | some a => simp [decodeOptionIndex, optionCode, finCode, finCode_lt]

/-- A numeric TM2 statement. Tables are stored in semantic form here and
will become read-only IMP+ arrays in the next layer. -/
inductive NumericStmt
  | push (stack : ℕ) (symbolByState : List ℕ) (next : NumericStmt)
  | peek (stack width : ℕ) (stateByStateHead : List ℕ) (next : NumericStmt)
  | pop (stack width : ℕ) (stateByStateHead : List ℕ) (next : NumericStmt)
  | load (stateByState : List ℕ) (next : NumericStmt)
  | branch (conditionByState : List ℕ) (ifTrue ifFalse : NumericStmt)
  | goto (labelByState : List ℕ)
  | halt

/-- Numeric values of a state-indexed family of symbols on stack `k`. -/
noncomputable def symbolStateTable (tm : FinTM2) (k : tm.K)
    (f : tm.σ → tm.Γ k)
    (hf : ∀ s, (⟨k, f s⟩ : Σ k, tm.Γ k) ∈ FinTM2.availableSymbols tm) : List ℕ := by
  letI := tm.σFin
  letI : DecidableEq tm.σ := Classical.decEq _
  exact List.ofFn fun i : Fin (Fintype.card tm.σ) =>
    let s := (Fintype.equivFin tm.σ).symm i
    FinTM2.codeSymbol tm (f s) (hf s)

theorem symbolStateTable_getD (tm : FinTM2) (k : tm.K)
    (f : tm.σ → tm.Γ k)
    (hf : ∀ s, (⟨k, f s⟩ : Σ k, tm.Γ k) ∈ FinTM2.availableSymbols tm)
    (s : tm.σ) :
    (symbolStateTable tm k f hf).getD (FinTM2.stateCode tm s) 0 =
      FinTM2.codeSymbol tm (f s) (hf s) := by
  letI := tm.σFin
  letI : DecidableEq tm.σ := Classical.decEq _
  rw [symbolStateTable, FinTM2.stateCode, getD_ofFn _ _ _ (finCode_lt s)]
  simp [FinTM2.stateCode, finCode]

/-- A Boolean control function represented by zero and one. -/
noncomputable def conditionTable (tm : FinTM2) (f : tm.σ → Bool) : List ℕ := by
  letI := tm.σFin
  exact List.ofFn fun i : Fin (Fintype.card tm.σ) =>
    if f ((Fintype.equivFin tm.σ).symm i) then 1 else 0

theorem conditionTable_getD (tm : FinTM2) (f : tm.σ → Bool) (s : tm.σ) :
    (conditionTable tm f).getD (FinTM2.stateCode tm s) 0 =
      if f s then 1 else 0 := by
  letI := tm.σFin
  letI : DecidableEq tm.σ := Classical.decEq _
  rw [conditionTable, FinTM2.stateCode, getD_ofFn _ _ _ (finCode_lt s)]
  simp [FinTM2.stateCode, finCode]

/-- Table for a state-and-optional-head function at stack `k`. Values outside
the stack-specific available alphabet are absent because the reachable-stack
invariant proves they can never be queried. -/
noncomputable def headStateTable (tm : FinTM2) (k : tm.K)
    (f : tm.σ → Option (tm.Γ k) → tm.σ) : List ℕ := by
  letI := tm.σFin
  letI : DecidableEq tm.σ := Classical.decEq _
  let width := Fintype.card (FinTM2.AvailableAt tm k) + 1
  exact List.ofFn fun i : Fin (Fintype.card tm.σ * width) =>
    let si : Fin (Fintype.card tm.σ) := ⟨i.val / width, by
      apply (Nat.div_lt_iff_lt_mul (by omega)).2
      simpa [Nat.mul_comm] using i.isLt⟩
    let oi : Fin width := ⟨i.val % width, Nat.mod_lt _ (by omega)⟩
    let s := (Fintype.equivFin tm.σ).symm si
    let o := decodeOptionIndex (FinTM2.AvailableAt tm k) oi
    finCode (f s (o.map Subtype.val))

theorem headStateTable_getD (tm : FinTM2) (k : tm.K)
    (f : tm.σ → Option (tm.Γ k) → tm.σ) (s : tm.σ)
    (o : Option (FinTM2.AvailableAt tm k)) :
    (headStateTable tm k f).getD
        (FinTM2.stateCode tm s * (Fintype.card (FinTM2.AvailableAt tm k) + 1) +
          FinTM2.headOptionCode tm k o) 0 =
      FinTM2.stateCode tm (f s (o.map Subtype.val)) := by
  letI := tm.σFin
  letI : DecidableEq tm.σ := Classical.decEq _
  letI : Fintype (FinTM2.AvailableAt tm k) := FinTM2.AvailableAt.instFintype tm k
  letI : DecidableEq (FinTM2.AvailableAt tm k) :=
    FinTM2.AvailableAt.instDecidableEq tm k
  let W := Fintype.card (FinTM2.AvailableAt tm k) + 1
  have hs : FinTM2.stateCode tm s < Fintype.card tm.σ := finCode_lt s
  have ho : FinTM2.headOptionCode tm k o < W := optionCode_lt o
  have hi : FinTM2.stateCode tm s * W + FinTM2.headOptionCode tm k o <
      Fintype.card tm.σ * W := by nlinarith
  rw [headStateTable, getD_ofFn _ _ _ hi]
  simp only
  congr 2
  · have hdiv : (FinTM2.stateCode tm s * W + FinTM2.headOptionCode tm k o) / W =
        FinTM2.stateCode tm s := by
        rw [Nat.mul_comm, Nat.add_comm,
          Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt ho]
        simp
    calc
      (Fintype.equivFin tm.σ).symm ⟨_, _⟩ =
          (Fintype.equivFin tm.σ).symm (Fintype.equivFin tm.σ s) := by
            congr 1
            exact Fin.ext hdiv
      _ = s := (Fintype.equivFin tm.σ).symm_apply_apply s
  · have hmod : (FinTM2.stateCode tm s * W + FinTM2.headOptionCode tm k o) % W =
        FinTM2.headOptionCode tm k o := by
        rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt ho]
    have hoi : (⟨(FinTM2.stateCode tm s * W + FinTM2.headOptionCode tm k o) % W, by
        omega⟩ : Fin W) = ⟨FinTM2.headOptionCode tm k o, ho⟩ := Fin.ext hmod
    rw [hoi]
    exact congrArg (Option.map Subtype.val) (decodeOptionIndex_optionCode o)

/-- Translate a typed TM2 statement into its numeric finite-table form.
The generated-symbol hypothesis supplies the availability proof for every
symbol stored by a translated `push`. -/
noncomputable def numericStmt (tm : FinTM2) (q : TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hgen : ∀ z, SigmaGeneratedBy q z → z ∈ FinTM2.availableSymbols tm) : NumericStmt := by
  letI := tm.kFin
  letI := tm.σFin
  letI := tm.ΛFin
  letI : DecidableEq tm.K := tm.kDecidableEq
  letI : DecidableEq tm.σ := Classical.decEq _
  letI : DecidableEq tm.Λ := Classical.decEq _
  induction q with
  | push k f q ih =>
      exact .push (finCode k)
        (symbolStateTable tm k f (fun s => hgen _ (.push_here s)))
        (ih (fun z hz => hgen z (.push_next hz)))
  | peek k f q ih =>
      exact .peek (finCode k) (Fintype.card (FinTM2.AvailableAt tm k) + 1)
        (headStateTable tm k f)
        (ih (fun z hz => hgen z (.peek_next hz)))
  | pop k f q ih =>
      exact .pop (finCode k) (Fintype.card (FinTM2.AvailableAt tm k) + 1)
        (headStateTable tm k f)
        (ih (fun z hz => hgen z (.pop_next hz)))
  | load f q ih =>
      exact .load (unaryTable f) (ih (fun z hz => hgen z (.load_next hz)))
  | branch f q₁ q₂ ih₁ ih₂ =>
      exact .branch (conditionTable tm f)
        (ih₁ (fun z hz => hgen z (.branch_left hz)))
        (ih₂ (fun z hz => hgen z (.branch_right hz)))
  | goto f => exact .goto (unaryTable f)
  | halt => exact .halt

end Lax51Proofs.TMToRam
