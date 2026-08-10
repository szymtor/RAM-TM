import Lax51Proofs.TMToRam.NumericSemantics

namespace Lax51Proofs.TMToRam

open Turing

/-- Executing the numeric specialization of a typed statement gives exactly
the encoding of `TM2.stepAux`. -/
theorem numericStmt_exec_encode (tm : FinTM2) (q : TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hgen : ∀ z, SigmaGeneratedBy q z → z ∈ FinTM2.availableSymbols tm)
    (l : Option tm.Λ) (s : tm.σ) (S : ∀ k, List (tm.Γ k))
    (hS : StacksWithin (FinTM2.availableSymbols tm) S) :
    (numericStmt tm q hgen).exec (FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS) =
      FinTM2.encodeNumericState tm (TM2.stepAux q s S)
        (stepAux_stacksWithin _ _ _ _ hS hgen) := by
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
                · exact hS k a ha)
              hS'
      simp only [numericStmt, NumericStmt.exec]
      rw [hmid]
      exact ih (fun z hz => hgen z (.push_next hz)) l s S' hS'
  | peek k f q ih =>
      let o := FinTM2.availableHeadOption tm k (S k) (fun a ha => hS k a ha)
      have hlookup :
          (headStateTable tm k f).getD
              ((FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).state *
                  (Fintype.card (FinTM2.AvailableAt tm k) + 1) +
                headCode ((FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).stackData
                  (finCode k))) 0 =
            FinTM2.stateCode tm (f s (S k).head?) := by
        rw [FinTM2.encodeNumericState_stack,
          FinTM2.headCode_codeStack tm k (S k) (fun a ha => hS k a ha)]
        convert headStateTable_getD tm k f s o using 1 <;>
          simp [FinTM2.encodeNumericState, FinTM2.stateCode, o,
            FinTM2.availableHeadOption_map, FinTM2.availableHeadOption_unattach]
      simp only [numericStmt, NumericStmt.exec]
      rw [hlookup]
      have henc :
          { FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS with
              state := FinTM2.stateCode tm (f s (S k).head?) } =
            FinTM2.encodeNumericState tm ⟨l, f s (S k).head?, S⟩ hS := by
        ext <;> simp [FinTM2.encodeNumericState, FinTM2.stateCode]
      rw [henc]
      exact ih (fun z hz => hgen z (.peek_next hz)) l (f s (S k).head?) S hS
  | pop k f q ih =>
      let o := FinTM2.availableHeadOption tm k (S k) (fun a ha => hS k a ha)
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
      have hlookup :
          (headStateTable tm k f).getD
              ((FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).state *
                  (Fintype.card (FinTM2.AvailableAt tm k) + 1) +
                headCode ((FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).stackData
                  (finCode k))) 0 =
            FinTM2.stateCode tm (f s (S k).head?) := by
        rw [FinTM2.encodeNumericState_stack,
          FinTM2.headCode_codeStack tm k (S k) (fun a ha => hS k a ha)]
        convert headStateTable_getD tm k f s o using 1 <;>
          simp [FinTM2.encodeNumericState, FinTM2.stateCode, o,
            FinTM2.availableHeadOption_map, FinTM2.availableHeadOption_unattach]
      simp only [numericStmt, NumericStmt.exec]
      rw [hlookup]
      have htail := FinTM2.codeStack_tail tm k (S k) (fun a ha => hS k a ha)
      have henc :
          { { FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS with
                state := FinTM2.stateCode tm (f s (S k).head?) } with
            stackData := Function.update
              (FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).stackData (finCode k)
              ((FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).stackData
                (finCode k)).tail } =
            FinTM2.encodeNumericState tm ⟨l, f s (S k).head?, S'⟩ hS' := by
        apply NumericMachineState.ext
        · rfl
        · rfl
        · rw [FinTM2.encodeNumericState_stack, htail]
          simpa [FinTM2.encodeNumericState, S'] using
            FinTM2.codeStackFamily_update tm S hS k (S k).tail
              (fun a ha => hS k a (List.mem_of_mem_tail ha)) hS'
      rw [henc]
      exact ih (fun z hz => hgen z (.pop_next hz)) l (f s (S k).head?) S' hS'
  | load f q ih =>
      simp only [numericStmt, NumericStmt.exec]
      rw [show (unaryTable f).getD
          (FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).state 0 = finCode (f s) by
        simpa [FinTM2.encodeNumericState] using unaryTable_getD f s 0]
      have henc :
          { FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS with state := finCode (f s) } =
            FinTM2.encodeNumericState tm ⟨l, f s, S⟩ hS := by
        ext <;> simp [FinTM2.encodeNumericState]
      rw [henc]
      exact ih (fun z hz => hgen z (.load_next hz)) l (f s) S hS
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [numericStmt, NumericStmt.exec]
      rw [show (conditionTable tm f).getD
          (FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).state 0 =
          (if f s then 1 else 0) by
        simpa [FinTM2.encodeNumericState] using conditionTable_getD tm f s]
      cases hf : f s
      · simp [hf]
        exact ih₂ (fun z hz => hgen z (.branch_right hz)) l s S hS
      · simp [hf]
        exact ih₁ (fun z hz => hgen z (.branch_left hz)) l s S hS
  | goto f => exact numericStmt_exec_goto tm f l s S hS hgen
  | halt => exact numericStmt_exec_halt tm l s S hS hgen

end Lax51Proofs.TMToRam
