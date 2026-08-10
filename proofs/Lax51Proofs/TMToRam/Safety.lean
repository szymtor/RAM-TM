import Lax51Proofs.TMToRam.MachineCompiler

/-!
Safety of the numeric interpreter on encodings of typed configurations.
Finite-control table accesses are intrinsically in range; the only genuine
resource obligation is that a stack has a free cell whenever a statement
pushes onto it.
-/

namespace Lax51Proofs.TMToRam

open Turing
open Lax13Proofs.Imp

/-- Typed formulation of the stack-capacity obligations along one atomic
statement. -/
def FinTM2.CapacitySafe (tm : FinTM2) (capacity : ℕ → ℕ) :
    TM2.Stmt tm.Γ tm.Λ tm.σ → tm.σ → (∀ k, List (tm.Γ k)) → Prop
  | .push k f q, s, S =>
      (S k).length < capacity (@finCode tm.K tm.kFin tm.kDecidableEq k) ∧
        FinTM2.CapacitySafe tm capacity q s (Function.update S k (f s :: S k))
  | .peek k f q, s, S =>
      FinTM2.CapacitySafe tm capacity q (f s (S k).head?) S
  | .pop k f q, s, S =>
      FinTM2.CapacitySafe tm capacity q (f s (S k).head?)
        (Function.update S k (S k).tail)
  | .load f q, s, S => FinTM2.CapacitySafe tm capacity q (f s) S
  | .branch f yes no, s, S =>
      if f s then FinTM2.CapacitySafe tm capacity yes s S
      else FinTM2.CapacitySafe tm capacity no s S
  | .goto _, _, _ => True
  | .halt, _, _ => True

@[simp] theorem symbolStateTable_length (tm : FinTM2) (k : tm.K)
    (f : tm.σ → tm.Γ k)
    (hf : ∀ s, (⟨k, f s⟩ : Σ k, tm.Γ k) ∈ FinTM2.availableSymbols tm) :
    (symbolStateTable tm k f hf).length = @Fintype.card tm.σ tm.σFin := by
  letI := tm.σFin
  simp [symbolStateTable]

@[simp] theorem conditionTable_length (tm : FinTM2) (f : tm.σ → Bool) :
    (conditionTable tm f).length = @Fintype.card tm.σ tm.σFin := by
  letI := tm.σFin
  simp [conditionTable]

@[simp] theorem headStateTable_length (tm : FinTM2) (k : tm.K)
    (f : tm.σ → Option (tm.Γ k) → tm.σ) :
    (headStateTable tm k f).length =
      @Fintype.card tm.σ tm.σFin *
        (@Fintype.card (FinTM2.AvailableAt tm k)
          (FinTM2.AvailableAt.instFintype tm k) + 1) := by
  letI := tm.σFin
  simp [headStateTable]

theorem FinTM2.encoded_head_index_lt (tm : FinTM2) (k : tm.K)
    (s : tm.σ) (S : ∀ j, List (tm.Γ j))
    (hS : StacksWithin (FinTM2.availableSymbols tm) S) :
    (FinTM2.encodeNumericState tm ⟨none, s, S⟩ hS).state *
          (@Fintype.card (FinTM2.AvailableAt tm k)
            (FinTM2.AvailableAt.instFintype tm k) + 1) +
        headCode ((FinTM2.encodeNumericState tm ⟨none, s, S⟩ hS).stackData
          (@finCode tm.K tm.kFin tm.kDecidableEq k)) <
      @Fintype.card tm.σ tm.σFin *
        (@Fintype.card (FinTM2.AvailableAt tm k)
          (FinTM2.AvailableAt.instFintype tm k) + 1) := by
  letI := tm.kFin
  letI := tm.σFin
  letI : DecidableEq tm.K := tm.kDecidableEq
  letI : DecidableEq tm.σ := Classical.decEq _
  rw [FinTM2.encodeNumericState_stack,
    FinTM2.headCode_codeStack tm k (S k) (fun a ha => hS k a ha)]
  have hs : FinTM2.stateCode tm s < Fintype.card tm.σ := finCode_lt s
  have hh : FinTM2.headOptionCode tm k
      (FinTM2.availableHeadOption tm k (S k) (fun a ha => hS k a ha)) <
      Fintype.card (FinTM2.AvailableAt tm k) + 1 := by
    exact optionCode_lt _
  simp only [FinTM2.encodeNumericState, FinTM2.stateCode]
  calc
    finCode s * (Fintype.card (FinTM2.AvailableAt tm k) + 1) +
          FinTM2.headOptionCode tm k
            (FinTM2.availableHeadOption tm k (S k) (fun a ha => hS k a ha)) <
        finCode s * (Fintype.card (FinTM2.AvailableAt tm k) + 1) +
          (Fintype.card (FinTM2.AvailableAt tm k) + 1) :=
      Nat.add_lt_add_left hh _
    _ = (finCode s + 1) * (Fintype.card (FinTM2.AvailableAt tm k) + 1) := by
      rw [Nat.add_mul]
      simp
    _ ≤ Fintype.card tm.σ * (Fintype.card (FinTM2.AvailableAt tm k) + 1) :=
      Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr (by
        simpa [FinTM2.stateCode] using hs))

/-- Typed capacity safety implies every bound required by the numeric
statement interpreter. -/
theorem FinTM2.numericStmt_safe_encode (tm : FinTM2)
    (q : TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hgen : ∀ z, SigmaGeneratedBy q z → z ∈ FinTM2.availableSymbols tm)
    (capacity : ℕ → ℕ) (l : Option tm.Λ) (s : tm.σ)
    (S : ∀ k, List (tm.Γ k))
    (hS : StacksWithin (FinTM2.availableSymbols tm) S)
    (hcap : FinTM2.CapacitySafe tm capacity q s S) :
    SafeExec capacity (numericStmt tm q hgen)
      (FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS) := by
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  letI : DecidableEq tm.K := tm.kDecidableEq
  letI : DecidableEq tm.Λ := Classical.decEq _
  letI : DecidableEq tm.σ := Classical.decEq _
  induction q generalizing l s S with
  | push k f q ih =>
      let S' := Function.update S k (f s :: S k)
      have hS' : StacksWithin (FinTM2.availableSymbols tm) S' := by
        intro j a ha
        dsimp [S'] at ha
        by_cases hj : j = k
        · subst j
          rw [Function.update_self] at ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact hgen _ (.push_here s)
          · exact hS k a ha
        · rw [Function.update_of_ne hj] at ha
          exact hS j a ha
      have hmid :
          { FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS with
            stackData := Function.update
              (FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).stackData (finCode k)
              ((symbolStateTable tm k f (fun t => hgen _ (.push_here t))).getD
                (FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).state 0 ::
                (FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).stackData (finCode k)) } =
            FinTM2.encodeNumericState tm ⟨l, s, S'⟩ hS' := by
        rw [show (symbolStateTable tm k f (fun t => hgen _ (.push_here t))).getD
              (FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).state 0 =
              FinTM2.codeSymbol tm (f s) (hgen _ (.push_here s)) by
          simpa [FinTM2.encodeNumericState, FinTM2.stateCode] using
            symbolStateTable_getD tm k f (fun t => hgen _ (.push_here t)) s]
        apply NumericMachineState.ext
        · rfl
        · rfl
        · rw [FinTM2.encodeNumericState_stack]
          simpa [FinTM2.encodeNumericState, FinTM2.codeStack_cons, S'] using
            FinTM2.codeStackFamily_update tm S hS k (f s :: S k)
              (fun a ha => by
                rcases List.mem_cons.mp ha with rfl | ha
                · exact hgen _ (.push_here s)
                · exact hS k a ha) hS'
      simp only [numericStmt, SafeExec]
      refine ⟨?_, ?_, ?_⟩
      · simpa [FinTM2.encodeNumericState, FinTM2.stateCode] using finCode_lt s
      · simpa [FinTM2.encodeNumericState_stack] using hcap.1
      · rw [hmid]
        exact ih (fun z hz => hgen z (.push_next hz)) l s S' hS' hcap.2
  | peek k f q ih =>
      let s' := f s (S k).head?
      have hidx := FinTM2.encoded_head_index_lt tm k s S hS
      have hlookup :
          (headStateTable tm k f).getD
              ((FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).state *
                  (Fintype.card (FinTM2.AvailableAt tm k) + 1) +
                headCode ((FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).stackData
                  (finCode k))) 0 =
            FinTM2.stateCode tm s' := by
        rw [FinTM2.encodeNumericState_stack,
          FinTM2.headCode_codeStack tm k (S k) (fun a ha => hS k a ha)]
        convert headStateTable_getD tm k f s
          (FinTM2.availableHeadOption tm k (S k) (fun a ha => hS k a ha)) using 1 <;>
          simp [FinTM2.encodeNumericState, FinTM2.stateCode, s',
            FinTM2.availableHeadOption_map, FinTM2.availableHeadOption_unattach]
      have henc :
          { FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS with
            state := (headStateTable tm k f).getD
              ((FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).state *
                (Fintype.card (FinTM2.AvailableAt tm k) + 1) +
                headCode ((FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).stackData
                  (finCode k))) 0 } =
            FinTM2.encodeNumericState tm ⟨l, s', S⟩ hS := by
        apply NumericMachineState.ext
        · rfl
        · exact hlookup
        · rfl
      simp only [numericStmt, SafeExec]
      refine ⟨by simpa [headStateTable_length] using hidx, ?_⟩
      rw [henc]
      exact ih (fun z hz => hgen z (.peek_next hz)) l s' S hS hcap
  | pop k f q ih =>
      let s' := f s (S k).head?
      let S' := Function.update S k (S k).tail
      have hS' : StacksWithin (FinTM2.availableSymbols tm) S' := by
        intro j a ha
        dsimp [S'] at ha
        by_cases hj : j = k
        · subst j
          rw [Function.update_self] at ha
          exact hS k a (List.mem_of_mem_tail ha)
        · rw [Function.update_of_ne hj] at ha
          exact hS j a ha
      have hidx := FinTM2.encoded_head_index_lt tm k s S hS
      simp only [numericStmt, SafeExec]
      refine ⟨by simpa [headStateTable_length] using hidx, ?_⟩
      have hlookup :
          (headStateTable tm k f).getD
              ((FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).state *
                  (Fintype.card (FinTM2.AvailableAt tm k) + 1) +
                headCode ((FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).stackData
                  (finCode k))) 0 = FinTM2.stateCode tm s' := by
        rw [FinTM2.encodeNumericState_stack,
          FinTM2.headCode_codeStack tm k (S k) (fun a ha => hS k a ha)]
        convert headStateTable_getD tm k f s
          (FinTM2.availableHeadOption tm k (S k) (fun a ha => hS k a ha)) using 1 <;>
          simp [FinTM2.encodeNumericState, FinTM2.stateCode, s',
            FinTM2.availableHeadOption_map, FinTM2.availableHeadOption_unattach]
      have htail := FinTM2.codeStack_tail tm k (S k) (fun a ha => hS k a ha)
      have henc :
          { { FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS with
                state := (headStateTable tm k f).getD
                  ((FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).state *
                    (Fintype.card (FinTM2.AvailableAt tm k) + 1) +
                    headCode ((FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).stackData
                      (finCode k))) 0 } with
            stackData := Function.update
              (FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).stackData (finCode k)
              ((FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).stackData
                (finCode k)).tail } =
            FinTM2.encodeNumericState tm ⟨l, s', S'⟩ hS' := by
        apply NumericMachineState.ext
        · rfl
        · exact hlookup
        · rw [FinTM2.encodeNumericState_stack, htail]
          simpa [FinTM2.encodeNumericState, S'] using
            FinTM2.codeStackFamily_update tm S hS k (S k).tail
              (fun a ha => hS k a (List.mem_of_mem_tail ha)) hS'
      have htailSafe := ih (fun z hz => hgen z (.pop_next hz)) l s' S' hS' hcap
      rw [henc]
      exact htailSafe
  | load f q ih =>
      simp only [numericStmt, SafeExec]
      refine ⟨?_, ?_⟩
      · simpa [FinTM2.encodeNumericState, unaryTable_length] using finCode_lt s
      · have hlookup : (unaryTable f).getD
            (FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).state 0 = finCode (f s) := by
          simpa [FinTM2.encodeNumericState] using unaryTable_getD f s 0
        have henc :
            { FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS with
              state := (unaryTable f).getD
                (FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).state 0 } =
              FinTM2.encodeNumericState tm ⟨l, f s, S⟩ hS := by
          apply NumericMachineState.ext
          · rfl
          · simpa [FinTM2.encodeNumericState] using hlookup
          · rfl
        rw [henc]
        exact ih (fun z hz => hgen z (.load_next hz)) l (f s) S hS hcap
  | branch f yes no ihy ihn =>
      simp only [numericStmt, SafeExec]
      refine ⟨?_, ?_⟩
      · simpa [FinTM2.encodeNumericState, conditionTable_length] using finCode_lt s
      · rw [show (conditionTable tm f).getD
            (FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).state 0 =
            (if f s then 1 else 0) by
          simpa [FinTM2.encodeNumericState] using conditionTable_getD tm f s]
        cases hf : f s
        · change (if f s then
              FinTM2.CapacitySafe tm capacity yes s S
            else FinTM2.CapacitySafe tm capacity no s S) at hcap
          rw [hf] at hcap
          simp only [Bool.false_eq_true, if_false] at hcap
          simp [hf]
          exact ihn (fun z hz => hgen z (.branch_right hz)) l s S hS hcap
        · change (if f s then
              FinTM2.CapacitySafe tm capacity yes s S
            else FinTM2.CapacitySafe tm capacity no s S) at hcap
          rw [hf] at hcap
          simp only [if_true] at hcap
          simp [hf]
          exact ihy (fun z hz => hgen z (.branch_left hz)) l s S hS hcap
  | goto f =>
      simpa [numericStmt, SafeExec, FinTM2.encodeNumericState, unaryTable_length]
        using finCode_lt s
  | halt => simp [numericStmt, SafeExec]

/-- Maximum number of pushes to one selected stack along an execution path
inside one atomic statement. -/
def FinTM2.pushBudget (tm : FinTM2) (target : tm.K) :
    TM2.Stmt tm.Γ tm.Λ tm.σ → ℕ
  | .push k _ q =>
      (if target = k then 1 else 0) + FinTM2.pushBudget tm target q
  | .peek _ _ q | .pop _ _ q | .load _ q => FinTM2.pushBudget tm target q
  | .branch _ yes no =>
      max (FinTM2.pushBudget tm target yes) (FinTM2.pushBudget tm target no)
  | .goto _ | .halt => 0

/-- A stack capacity covering the current lengths plus the syntactic push
budget implies `CapacitySafe`. -/
theorem FinTM2.capacitySafe_of_pushBudget (tm : FinTM2)
    (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (capacity : ℕ → ℕ)
    (s : tm.σ) (S : ∀ k, List (tm.Γ k))
    (hbudget : ∀ k, (S k).length + FinTM2.pushBudget tm k q ≤
      capacity (@finCode tm.K tm.kFin tm.kDecidableEq k)) :
    FinTM2.CapacitySafe tm capacity q s S := by
  induction q generalizing s S with
  | push k f q ih =>
      constructor
      · have hk := hbudget k
        simp [FinTM2.pushBudget] at hk
        omega
      · apply ih
        intro j
        have hj := hbudget j
        by_cases h : j = k
        · subst j
          simpa [FinTM2.pushBudget, Nat.add_assoc] using hj
        · simpa [FinTM2.pushBudget, h, Function.update_of_ne h] using hj
  | peek k f q ih =>
      apply ih
      simpa [FinTM2.pushBudget] using hbudget
  | pop k f q ih =>
      apply ih
      intro j
      have hj := hbudget j
      by_cases h : j = k
      · subst j
        rw [Function.update_self]
        simp only [FinTM2.pushBudget] at hj ⊢
        have hlen : (S k).tail.length ≤ (S k).length := by
          cases S k <;> simp
        omega
      · rw [Function.update_of_ne h]
        simpa [FinTM2.pushBudget] using hj
  | load f q ih =>
      apply ih
      simpa [FinTM2.pushBudget] using hbudget
  | branch f yes no ihy ihn =>
      simp only [FinTM2.CapacitySafe]
      split <;> rename_i hf
      · apply ihy
        intro k
        exact (Nat.add_le_add_left (Nat.le_max_left _ _) _).trans (hbudget k)
      · apply ihn
        intro k
        exact (Nat.add_le_add_left (Nat.le_max_right _ _) _).trans (hbudget k)
  | goto f => trivial
  | halt => trivial

/-- Worst per-transition push count for a fixed stack of a fixed machine. -/
noncomputable def FinTM2.machinePushBudget (tm : FinTM2) (k : tm.K) : ℕ := by
  letI := tm.ΛFin
  exact Finset.univ.sup fun l => FinTM2.pushBudget tm k (tm.m l)

theorem FinTM2.pushBudget_le_machinePushBudget (tm : FinTM2) (k : tm.K)
    (l : tm.Λ) :
    FinTM2.pushBudget tm k (tm.m l) ≤ FinTM2.machinePushBudget tm k := by
  letI := tm.ΛFin
  exact Finset.le_sup (f := fun l => FinTM2.pushBudget tm k (tm.m l))
    (Finset.mem_univ l)

/-- One atomic statement grows a stack by at most its syntactic push budget. -/
theorem FinTM2.stepAux_stack_length_le (tm : FinTM2)
    (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (s : tm.σ)
    (S : ∀ k, List (tm.Γ k)) (target : tm.K) :
    ((TM2.stepAux q s S).stk target).length ≤
      (S target).length + FinTM2.pushBudget tm target q := by
  letI : DecidableEq tm.K := tm.kDecidableEq
  induction q generalizing s S with
  | push k f q ih =>
      specialize ih s (Function.update S k (f s :: S k))
      by_cases h : target = k
      · subst target
        rw [Function.update_self] at ih
        simpa [FinTM2.pushBudget, Nat.add_assoc] using ih
      · rw [Function.update_of_ne h] at ih
        simpa [FinTM2.pushBudget, h] using ih
  | peek k f q ih => simpa [FinTM2.pushBudget] using ih (f s (S k).head?) S
  | pop k f q ih =>
      have htail := ih (f s (S k).head?) (Function.update S k (S k).tail)
      simp only [TM2.stepAux]
      by_cases h : target = k
      · subst target
        rw [Function.update_self] at htail
        have hlen : (S k).tail.length ≤ (S k).length := by cases S k <;> simp
        simp only [FinTM2.pushBudget]
        omega
      · rw [Function.update_of_ne h] at htail
        simpa [FinTM2.pushBudget] using htail
  | load f q ih => simpa [FinTM2.pushBudget] using ih (f s) S
  | branch f yes no ihy ihn =>
      cases hf : f s
      · have h := ihn s S
        simp [TM2.stepAux, hf, FinTM2.pushBudget]
        exact h.trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
      · have h := ihy s S
        simp [TM2.stepAux, hf, FinTM2.pushBudget]
        exact h.trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
  | goto f => simp [TM2.stepAux, FinTM2.pushBudget]
  | halt => simp [TM2.stepAux, FinTM2.pushBudget]

/-- A typed finite execution ending in a halted configuration. -/
inductive TypedRun (tm : FinTM2) : ℕ → tm.Cfg → tm.Cfg → Type
  | halt (c : tm.Cfg)
      (hc : StacksWithin (FinTM2.availableSymbols tm) c.stk)
      (hhalt : c.l = none) : TypedRun tm 0 c c
  | step (l : tm.Λ) (s : tm.σ) (S : ∀ k, List (tm.Γ k))
      (hS : StacksWithin (FinTM2.availableSymbols tm) S)
      (n : ℕ) (final : tm.Cfg)
      (tail : TypedRun tm n (TM2.stepAux (tm.m l) s S) final) :
      TypedRun tm (n + 1) ⟨some l, s, S⟩ final

/-- Along an `n`-step execution, a fixed stack grows by at most `n` times
the machine's worst one-step push budget for that stack. -/
theorem TypedRun.final_stack_length_le {tm : FinTM2} {n : ℕ}
    {c final : tm.Cfg} (run : TypedRun tm n c final) (k : tm.K) :
    (final.stk k).length ≤
      (c.stk k).length + n * FinTM2.machinePushBudget tm k := by
  induction run with
  | halt => simp
  | step l s S hS n final tail ih =>
      have hgrow := FinTM2.stepAux_stack_length_le tm (tm.m l) s S k
      have hpush := FinTM2.pushBudget_le_machinePushBudget tm k l
      calc
        (final.stk k).length ≤
            ((TM2.stepAux (tm.m l) s S).stk k).length +
              n * FinTM2.machinePushBudget tm k := ih
        _ ≤ ((S k).length + FinTM2.machinePushBudget tm k) +
              n * FinTM2.machinePushBudget tm k :=
          Nat.add_le_add_right
            (hgrow.trans (Nat.add_le_add_left hpush _)) _
        _ = (S k).length +
              (n + 1) * FinTM2.machinePushBudget tm k := by
          rw [Nat.add_mul, Nat.one_mul]
          omega

/-- A global capacity covering the initial lengths plus the machine push
constant times the remaining number of transitions makes a typed run safe. -/
noncomputable def TypedRun.toSafeRun {tm : FinTM2} {n : ℕ} {c final : tm.Cfg}
    (run : TypedRun tm n c final) (capacity : ℕ → ℕ)
    (hroom : ∀ k, (c.stk k).length + n * FinTM2.machinePushBudget tm k ≤
      capacity (@finCode tm.K tm.kFin tm.kDecidableEq k)) :
    SafeRun tm capacity c final := by
  induction run with
  | halt c hc hhalt => exact .halt c hc hhalt
  | step l s S hS n final tail ih =>
      have hcap : FinTM2.CapacitySafe tm capacity (tm.m l) s S := by
        apply FinTM2.capacitySafe_of_pushBudget
        intro k
        have hpush := FinTM2.pushBudget_le_machinePushBudget tm k l
        have hr := hroom k
        change (S k).length + (n + 1) * FinTM2.machinePushBudget tm k ≤
          capacity (@finCode tm.K tm.kFin tm.kDecidableEq k) at hr
        rw [Nat.add_mul, Nat.one_mul] at hr
        omega
      have hsafe := FinTM2.numericStmt_safe_encode tm (tm.m l)
        (FinTM2.generatedBy_main_available tm l) capacity (some l) s S hS hcap
      apply SafeRun.step l s S hS final hsafe
      apply ih
      intro k
      have hgrow := FinTM2.stepAux_stack_length_le tm (tm.m l) s S k
      have hpush := FinTM2.pushBudget_le_machinePushBudget tm k l
      have hr := hroom k
      change (S k).length + (n + 1) * FinTM2.machinePushBudget tm k ≤
        capacity (@finCode tm.K tm.kFin tm.kDecidableEq k) at hr
      rw [Nat.add_mul, Nat.one_mul] at hr
      omega

/-- Extract the typed transition chain from an exact iterator equation whose
endpoint is halted. -/
noncomputable def TypedRun.of_iterate (tm : FinTM2) (n : ℕ) (c final : tm.Cfg)
    (hc : StacksWithin (FinTM2.availableSymbols tm) c.stk)
    (hrun : ((fun o : Option tm.Cfg => o.bind tm.step)^[n]) (some c) = some final)
    (hhalt : final.l = none) : TypedRun tm n c final := by
  induction n generalizing c with
  | zero =>
      simp only [Function.iterate_zero_apply] at hrun
      injection hrun with h
      subst c
      exact .halt final hc hhalt
  | succ n ih =>
      rcases c with ⟨l, s, S⟩
      cases l with
      | none =>
          rw [Function.iterate_succ_apply] at hrun
          change ((fun o : Option tm.Cfg => o.bind tm.step)^[n]) none = some final at hrun
          rw [iterate_bind_none] at hrun
          contradiction
      | some l =>
          have htail :
              ((fun o : Option tm.Cfg => o.bind tm.step)^[n])
                  (some (TM2.stepAux (tm.m l) s S)) = some final := by
            rw [Function.iterate_succ_apply] at hrun
            exact hrun
          have hnext : StacksWithin (FinTM2.availableSymbols tm)
              (TM2.stepAux (tm.m l) s S).stk :=
            stepAux_stacksWithin _ _ _ _ hc
              (FinTM2.generatedBy_main_available tm l)
          exact .step l s S hc n final (ih _ hnext htail)

/-- Canonical numeric stack capacity for an `n`-step run from `c`. -/
noncomputable def FinTM2.traceCapacity (tm : FinTM2) (c : tm.Cfg) (n : ℕ) :
    ℕ → ℕ := fun i =>
  match @finDecode tm.K tm.kFin i with
  | none => 0
  | some k => (c.stk k).length + n * FinTM2.machinePushBudget tm k

@[simp] theorem FinTM2.traceCapacity_finCode (tm : FinTM2) (c : tm.Cfg)
    (n : ℕ) (k : tm.K) :
    FinTM2.traceCapacity tm c n
        (@finCode tm.K tm.kFin tm.kDecidableEq k) =
      (c.stk k).length + n * FinTM2.machinePushBudget tm k := by
  letI := tm.kFin
  letI : DecidableEq tm.K := tm.kDecidableEq
  simp [FinTM2.traceCapacity]

/-- Every exact halted typed run is safe at its canonical capacity. -/
noncomputable def TypedRun.toCanonicalSafeRun {tm : FinTM2} {n : ℕ}
    {c final : tm.Cfg} (run : TypedRun tm n c final) :
    SafeRun tm (FinTM2.traceCapacity tm c n) c final :=
  run.toSafeRun _ (fun k => by simp)

@[simp] theorem TypedRun.steps_toSafeRun {tm : FinTM2} {n : ℕ}
    {c final : tm.Cfg} (run : TypedRun tm n c final) (capacity : ℕ → ℕ)
    (hroom : ∀ k, (c.stk k).length + n * FinTM2.machinePushBudget tm k ≤
      capacity (@finCode tm.K tm.kFin tm.kDecidableEq k)) :
    (run.toSafeRun capacity hroom).steps = n := by
  induction run with
  | halt => rfl
  | step l s S hS n final tail ih =>
      simp only [TypedRun.toSafeRun, SafeRun.steps]
      apply congrArg (· + 1)
      apply ih

structure SafeRunWitness (tm : FinTM2) (c final : tm.Cfg) (bound : ℕ) where
  steps : ℕ
  steps_le : steps ≤ bound
  capacity : ℕ → ℕ
  run : SafeRun tm capacity c final
  run_steps : run.steps = steps

/-- `TM2OutputsInTime` supplies a safe compiled-interpreter run without any
additional capacity assumption. -/
noncomputable def FinTM2.safeRunWitness_of_outputsInTime (tm : FinTM2)
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (bound : ℕ)
    (hrun : TM2OutputsInTime tm input (some output) bound) :
    SafeRunWitness tm (initList tm input) (haltList tm output) bound := by
  let typed := TypedRun.of_iterate tm hrun.steps (initList tm input)
    (haltList tm output) (FinTM2.initList_stacksWithin tm input)
    (by simpa only using hrun.evals_in_steps) (by simp [haltList])
  let safe := typed.toCanonicalSafeRun
  exact {
    steps := hrun.steps
    steps_le := hrun.steps_le_m
    capacity := FinTM2.traceCapacity tm (initList tm input) hrun.steps
    run := safe
    run_steps := by
      dsimp [safe, TypedRun.toCanonicalSafeRun]
      apply TypedRun.steps_toSafeRun
  }

/-- A machine running for at most `bound` steps can place only linearly many
symbols on its output stack. -/
theorem FinTM2.output_length_le_of_outputsInTime (tm : FinTM2)
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (bound : ℕ)
    (hrun : TM2OutputsInTime tm input (some output) bound) :
    output.length ≤
      input.length + bound * FinTM2.machinePushBudget tm tm.k₁ := by
  let typed := TypedRun.of_iterate tm hrun.steps (initList tm input)
    (haltList tm output) (FinTM2.initList_stacksWithin tm input)
    (by simpa only using hrun.evals_in_steps) (by simp [haltList])
  have hlen := typed.final_stack_length_le tm.k₁
  have hsteps := hrun.steps_le_m
  have hmul : hrun.steps * FinTM2.machinePushBudget tm tm.k₁ ≤
      bound * FinTM2.machinePushBudget tm tm.k₁ :=
    Nat.mul_le_mul_right _ hsteps
  have init_stack_length_le (k : tm.K) :
      ((initList tm input).stk k).length ≤ input.length := by
    simp only [Turing.initList]
    split
    · rename_i h
      subst k
      rfl
    · simp
  have hinit := init_stack_length_le tm.k₁
  have hmid := Nat.add_le_add hinit hmul
  simpa [typed, Turing.haltList] using hlen.trans hmid

/-- End-to-end core interpreter theorem: a bounded TM2 output run gives a
linearly bounded IMP+ loop run.  Initialization and output decoding are kept
outside this theorem, so its hypotheses are precisely the representation of
the encoded initial configuration and the immutable transition tables. -/
theorem FinTM2.compileLoop_outputsInTime (tm : FinTM2)
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (bound : ℕ)
    (hrun : TM2OutputsInTime tm input (some output) bound)
    (σ : Env)
    (hrep : NumericRep σ
      (FinTM2.traceCapacity tm (initList tm input) hrun.steps)
      (FinTM2.encodeNumericState tm (initList tm input)
        (FinTM2.initList_stacksWithin tm input)))
    (htables : TablesRep σ (FinTM2.compileDispatcher tm 0).tables) :
    ∃ σ' cost, BigStep (FinTM2.compileLoop tm) σ σ' cost ∧
      cost ≤
        (1 + Cond.size (.lt (.lit 0) (.var labelVar)) +
          maxCost (FinTM2.compileDispatcher tm 0).com) * bound +
          (1 + Cond.size (.lt (.lit 0) (.var labelVar))) ∧
      ∃ hfinal : StacksWithin (FinTM2.availableSymbols tm) (haltList tm output).stk,
        NumericRep σ'
          (FinTM2.traceCapacity tm (initList tm input) hrun.steps)
          (FinTM2.encodeNumericState tm (haltList tm output) hfinal) := by
  let witness := FinTM2.safeRunWitness_of_outputsInTime tm input output bound hrun
  have hcap : witness.capacity =
      FinTM2.traceCapacity tm (initList tm input) hrun.steps := rfl
  obtain ⟨σ', cost, hloop, hcost, hfinal, hrepFinal, _⟩ :=
    FinTM2.compileLoop_safeRun tm witness.capacity (initList tm input)
      (haltList tm output) (FinTM2.initList_stacksWithin tm input)
      witness.run σ (by simpa [hcap] using hrep) htables
  refine ⟨σ', cost, hloop, ?_, hfinal, ?_⟩
  · rw [witness.run_steps] at hcost
    exact hcost.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left _ witness.steps_le) _)
  · simpa [hcap] using hrepFinal

end Lax51Proofs.TMToRam
