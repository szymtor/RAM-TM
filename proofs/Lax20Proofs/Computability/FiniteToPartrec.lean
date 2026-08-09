import Lax20Proofs.Computability.ToPartrecList
import Mathlib.Computability.TuringMachine.Computable

namespace Lax20Proofs.Computability

open Computability StateTransition Turing

namespace FiniteSupportTM2

variable {K : Type} [DecidableEq K] {Γ : K → Type}
  {Λ σ : Type} (S : Finset Λ)

/-- Replace every target of a supported statement by the corresponding
element of the finite subtype of supported labels. -/
def restrictStmt : (q : TM2.Stmt Γ Λ σ) → TM2.SupportsStmt S q →
    TM2.Stmt Γ {q // q ∈ S} σ
  | .push k f q, h => .push k f (restrictStmt q h)
  | .peek k f q, h => .peek k f (restrictStmt q h)
  | .pop k f q, h => .pop k f (restrictStmt q h)
  | .load f q, h => .load f (restrictStmt q h)
  | .branch f q₁ q₂, h =>
      .branch f (restrictStmt q₁ h.1) (restrictStmt q₂ h.2)
  | .goto f, h => .goto fun v => ⟨f v, h v⟩
  | .halt, _ => .halt

/-- Forget that the current label lies in the selected finite support. -/
def liftCfg (c : TM2.Cfg Γ {q // q ∈ S} σ) : TM2.Cfg Γ Λ σ where
  l := c.l.map Subtype.val
  var := c.var
  stk := c.stk

@[simp] theorem liftCfg_l (c : TM2.Cfg Γ {q // q ∈ S} σ) :
    (liftCfg S c).l = c.l.map Subtype.val := rfl

@[simp] theorem liftCfg_var (c : TM2.Cfg Γ {q // q ∈ S} σ) :
    (liftCfg S c).var = c.var := rfl

@[simp] theorem liftCfg_stk (c : TM2.Cfg Γ {q // q ∈ S} σ) :
    (liftCfg S c).stk = c.stk := rfl

theorem liftCfg_injective : Function.Injective (liftCfg S :
    TM2.Cfg Γ {q // q ∈ S} σ → TM2.Cfg Γ Λ σ) := by
  intro a b h
  have hlift := congrArg TM2.Cfg.l h
  have hvar := congrArg TM2.Cfg.var h
  have hstk := congrArg TM2.Cfg.stk h
  have hl : a.l = b.l := by
    apply Option.map_injective Subtype.val_injective
    simpa [liftCfg] using hlift
  cases a
  cases b
  simp only at hl hvar hstk
  subst_vars
  rfl

theorem liftCfg_stepAux (q : TM2.Stmt Γ Λ σ)
    (h : TM2.SupportsStmt S q) (v : σ) (stk : ∀ k, List (Γ k)) :
    liftCfg S (TM2.stepAux (restrictStmt S q h) v stk) =
      TM2.stepAux q v stk := by
  induction q generalizing v stk with
  | push k f q ih => exact ih _ _ _
  | peek k f q ih => exact ih _ _ _
  | pop k f q ih => exact ih _ _ _
  | load f q ih => exact ih _ _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [TM2.SupportsStmt] at h
      cases e : f v
      · simpa [restrictStmt, TM2.stepAux, e] using ih₂ h.2 v stk
      · simpa [restrictStmt, TM2.stepAux, e] using ih₁ h.1 v stk
  | goto f => simp [restrictStmt, liftCfg]
  | halt => rfl

variable [Inhabited Λ]

/-- The finite restriction takes exactly the same step after forgetting the
subtype proof on labels. -/
theorem liftCfg_step (M : Λ → TM2.Stmt Γ Λ σ)
    (hM : ∀ q ∈ S, TM2.SupportsStmt S (M q))
    (c : TM2.Cfg Γ {q // q ∈ S} σ) :
    Option.map (liftCfg S)
        (TM2.step (fun q => restrictStmt S (M q) (hM q q.property)) c) =
      TM2.step M (liftCfg S c) := by
  cases c with
  | mk l v stk =>
    cases l with
    | none => rfl
    | some q =>
        simp only [TM2.step, Option.map_some]
        exact congrArg some (liftCfg_stepAux S (M q) (hM q q.property) v stk)

theorem restrict_respects (M : Λ → TM2.Stmt Γ Λ σ)
    (hM : ∀ q ∈ S, TM2.SupportsStmt S (M q)) :
    Respects
      (TM2.step (fun q => restrictStmt S (M q) (hM q q.property)))
      (TM2.step M)
      (fun a b => liftCfg S a = b) := by
  rw [StateTransition.fun_respects]
  intro c
  have hcomm := liftCfg_step S M hM c
  cases hstep : TM2.step
      (fun q => restrictStmt S (M q) (hM q q.property)) c with
  | none =>
      simp only [hstep, Option.map_none] at hcomm
      simpa [StateTransition.FRespects] using hcomm.symm
  | some c' =>
      simp only [hstep, Option.map_some] at hcomm
      simp only [hstep, StateTransition.FRespects]
      exact Relation.TransGen.single hcomm.symm

end FiniteSupportTM2

namespace PartrecFiniteTM2

open ToPartrec Turing.PartrecToTM2

deriving instance Fintype for K'

private theorem cfg_ext {K Γ Λ σ} {a b : TM2.Cfg (K := K) Γ Λ σ}
    (hl : a.l = b.l) (hv : a.var = b.var) (hs : a.stk = b.stk) : a = b := by
  cases a
  cases b
  simp_all

noncomputable def support (c : Code) : Finset Λ' :=
  codeSupp c Cont'.halt

theorem main_mem_support (c : Code) : trNormal c Cont'.halt ∈ support c := by
  exact codeSupp_self c Cont'.halt (trStmts₁_self _)

noncomputable abbrev machine (c : Code) : Turing.FinTM2 where
  K := K'
  k₀ := K'.main
  k₁ := K'.main
  Γ _ := Γ'
  Λ := {q // q ∈ support c}
  main := ⟨trNormal c Cont'.halt, main_mem_support c⟩
  σ := Option Γ'
  initialState := none
  m q := FiniteSupportTM2.restrictStmt (support c) (tr q)
    ((tr_supports c Cont'.halt).2 q q.property)

noncomputable def liftCfg (c : Code) : (machine c).Cfg → Cfg' :=
  FiniteSupportTM2.liftCfg (support c)

theorem liftCfg_step (c : Code) (q : (machine c).Cfg) :
    Option.map (liftCfg c) ((machine c).step q) =
      TM2.step tr (liftCfg c q) := by
  exact FiniteSupportTM2.liftCfg_step (support c) tr
    (tr_supports c Cont'.halt).2 q

theorem liftCfg_initList (c : Code) (v : List ℕ) :
    liftCfg c (Turing.initList (machine c) (trList v)) = init c v := by
  apply cfg_ext
    (a := liftCfg c (Turing.initList (machine c) (trList v)))
    (b := init c v) rfl rfl
  funext k
  cases k <;> simp [liftCfg, FiniteSupportTM2.liftCfg, Turing.initList,
    PartrecToTM2.init]

theorem liftCfg_haltList (c : Code) (v : List ℕ) :
    liftCfg c (Turing.haltList (machine c) (trList v)) = halt v := by
  apply cfg_ext
    (a := liftCfg c (Turing.haltList (machine c) (trList v)))
    (b := halt v) rfl rfl
  funext k
  cases k <;> simp [liftCfg, FiniteSupportTM2.liftCfg, Turing.haltList,
    PartrecToTM2.halt]

theorem liftCfg_injective (c : Code) : Function.Injective (liftCfg c) :=
  FiniteSupportTM2.liftCfg_injective (support c)

theorem restrict_respects (c : Code) :
    Respects (machine c).step (TM2.step tr)
      (fun a b => liftCfg c a = b) :=
  FiniteSupportTM2.restrict_respects (support c) tr
    (tr_supports c Cont'.halt).2

private theorem eval_mem_of_code_eval {c : Code} {v out : List ℕ}
    (h : c.eval v = pure out) :
    PartrecToTM2.halt out ∈ StateTransition.eval (TM2.step tr) (init c v) := by
  rw [PartrecToTM2.tr_eval, h]
  change PartrecToTM2.halt out ∈ Part.some (PartrecToTM2.halt out)
  exact Part.mem_some _

/-- The finite restriction of the universal `ToPartrec` evaluator terminates
with exactly the same semantic output as its infinite ambient presentation. -/
theorem eval_mem {c : Code} {v out : List ℕ}
    (h : c.eval v = pure out) :
    Turing.haltList (machine c) (trList out) ∈
      StateTransition.eval (machine c).step
        (Turing.initList (machine c) (trList v)) := by
  have horig := eval_mem_of_code_eval h
  have heval := StateTransition.tr_eval'
    (machine c).step (TM2.step tr) (liftCfg c)
    (restrict_respects c)
    (Turing.initList (machine c) (trList v))
  rw [liftCfg_initList] at heval
  rw [heval] at horig
  rcases (Part.mem_map_iff _).1 horig with ⟨q, hq, hqLift⟩
  have htarget : q = Turing.haltList (machine c) (trList out) := by
    apply liftCfg_injective c
    rw [liftCfg_haltList]
    exact hqLift
  simpa [htarget] using hq

private theorem reaches_has_steps {α : Type} {step : α → Option α}
    {a b : α} (h : StateTransition.Reaches step a b) :
    ∃ n, (flip bind step)^[n] a = some b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail hreach hstep ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨1 + n, ?_⟩
      rw [Function.iterate_add_apply, hn]
      simpa using hstep

private noncomputable def reaches_to_evalsTo_some {α : Type}
    {step : α → Option α} {a b : α}
    (h : StateTransition.Reaches step a b) :
    StateTransition.EvalsTo step a (some b) :=
  ⟨Classical.choose (reaches_has_steps h),
    Classical.choose_spec (reaches_has_steps h)⟩

private noncomputable def eval_mem_to_evalsTo_some {α : Type}
    {step : α → Option α} {a b : α}
    (h : b ∈ StateTransition.eval step a) :
    StateTransition.EvalsTo step a (some b) :=
  reaches_to_evalsTo_some (StateTransition.mem_eval.1 h).1

noncomputable def outputs {c : Code} {v out : List ℕ}
    (h : c.eval v = pure out) :
    Turing.TM2Outputs (machine c) (trList v) (some (trList out)) := by
  exact eval_mem_to_evalsTo_some (eval_mem h)

/-- Every terminating evaluator execution has a (not necessarily computable)
exact numerical step bound. -/
noncomputable def runningTime (c : Code) (v out : List ℕ)
    (h : c.eval v = pure out) : ℕ :=
  (outputs h).steps

noncomputable def outputsInRunningTime {c : Code} {v out : List ℕ}
    (h : c.eval v = pure out) :
    Turing.TM2OutputsInTime (machine c) (trList v) (some (trList out))
      (runningTime c v out h) := by
  exact ⟨outputs h, le_rfl⟩

end PartrecFiniteTM2

end Lax20Proofs.Computability
