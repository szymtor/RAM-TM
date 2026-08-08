import Lax20Proofs.RamToTM.MultiExitPhase

namespace Lax20Proofs.RamToTM

open Turing TM2

theorem chain_iterations {X : Type} (step : X -> X)
    {a b c : X} {m n : Nat}
    (h₁ : (step^[m]) a = b) (h₂ : (step^[n]) b = c) :
    (step^[m + n]) a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, h₁, h₂]

@[simp] theorem mapLabelStmt_id
    {K Λ σ : Type} {α : K → Type} [DecidableEq K]
    (stmt : TM2.Stmt α Λ σ) :
    mapLabelStmt id stmt = stmt := by
  induction stmt <;> simp [mapLabelStmt, *]

theorem mapLabelStmt_comp
    {K Λ Λ' Λ'' σ : Type} {α : K → Type} [DecidableEq K]
    (second : Λ' -> Λ'') (first : Λ -> Λ')
    (stmt : TM2.Stmt α Λ σ) :
    mapLabelStmt second (mapLabelStmt first stmt) =
      mapLabelStmt (second ∘ first) stmt := by
  induction stmt <;> simp [mapLabelStmt, Function.comp_def, *]

@[simp] theorem mapLabelCfg_id
    {K Λ σ : Type} {α : K → Type} (cfg : TM2.Cfg α Λ σ) :
    mapLabelCfg id cfg = cfg := by
  cases cfg <;> simp [mapLabelCfg]

theorem mapLabelCfg_comp
    {K Λ Λ' Λ'' σ : Type} {α : K → Type} (second : Λ' -> Λ'')
    (first : Λ -> Λ') (cfg : TM2.Cfg α Λ σ) :
    mapLabelCfg second (mapLabelCfg first cfg) =
      mapLabelCfg (second ∘ first) cfg := by
  cases cfg <;> simp [mapLabelCfg, Function.comp_def]

theorem step_mapLabelProgram_of_nonhalt
    {K Λ Λ' σ : Type} {α : K → Type} [DecidableEq K]
    (source : Λ -> TM2.Stmt α Λ σ)
    (target : Λ' -> TM2.Stmt α Λ' σ)
    (encode : Λ -> Λ')
    (c : TM2.Cfg α Λ σ)
    (hnonhalt : ∀ l, c.l = some l -> source l ≠ .halt)
    (hprogram : ∀ l, source l ≠ .halt ->
      target (encode l) = mapLabelStmt encode (source l)) :
    TM2.step target (mapLabelCfg encode c) =
      (TM2.step source c).map (mapLabelCfg encode) := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => rfl
  | some label =>
      have hn := hnonhalt label rfl
      simp only [TM2.step, mapLabelCfg, Option.map_some]
      rw [hprogram label hn]
      exact congrArg some
        (stepAux_mapLabelStmt encode (source label) state tapes)

theorem step_mapLabelProgram
    {K Λ Λ' σ : Type} {α : K → Type} [DecidableEq K]
    (source : Λ -> TM2.Stmt α Λ σ)
    (target : Λ' -> TM2.Stmt α Λ' σ)
    (encode : Λ -> Λ')
    (hprogram : ∀ l, target (encode l) = mapLabelStmt encode (source l))
    (c : TM2.Cfg α Λ σ) :
    TM2.step target (mapLabelCfg encode c) =
      (TM2.step source c).map (mapLabelCfg encode) := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => rfl
  | some label =>
      simp only [TM2.step, mapLabelCfg, Option.map_some]
      rw [hprogram label]
      exact congrArg some
        (stepAux_mapLabelStmt encode (source label) state tapes)

theorem iterate_mapLabelProgram
    {K Λ Λ' σ : Type} {α : K → Type} [DecidableEq K]
    (source : Λ -> TM2.Stmt α Λ σ)
    (target : Λ' -> TM2.Stmt α Λ' σ)
    (encode : Λ -> Λ')
    (hprogram : ∀ l, target (encode l) = mapLabelStmt encode (source l))
    (n : Nat) (c : TM2.Cfg α Λ σ) :
    ((fun x => x.bind (TM2.step target))^[n])
        (some (mapLabelCfg encode c)) =
      (((fun x => x.bind (TM2.step source))^[n]) (some c)).map
        (mapLabelCfg encode) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [Option.bind_some]
      rw [step_mapLabelProgram source target encode hprogram]
      cases hs : TM2.step source c with
      | none =>
          simp only [hs, Option.map_none]
          rw [iterate_optionBind_none, iterate_optionBind_none]
          rfl
      | some c' => simp only [hs, Option.map_some, Option.bind_some]; exact ih c'

theorem iterate_mapLabelProgram_until_exit
    {K Λ Λ' σ : Type} {α : K → Type} [DecidableEq K]
    (source : Λ -> TM2.Stmt α Λ σ)
    (target : Λ' -> TM2.Stmt α Λ' σ)
    (encode : Λ -> Λ')
    (hprogram : ∀ l, source l ≠ .halt ->
      target (encode l) = mapLabelStmt encode (source l))
    {n : Nat} {c d : TM2.Cfg α Λ σ}
    (hrun : ((fun x => x.bind (TM2.step source))^[n]) (some c) = some d)
    (hd : d.l.isSome) :
    ((fun x => x.bind (TM2.step target))^[n])
      (some (mapLabelCfg encode c)) =
    some (mapLabelCfg encode d) := by
  have hAvoid := avoidsHalts_of_reaches_labeled source hrun hd
  induction n generalizing c with
  | zero =>
      simp only [Function.iterate_zero_apply] at hrun ⊢
      exact congrArg (fun q => q.map (mapLabelCfg encode)) hrun
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some] at hrun ⊢
      rw [step_mapLabelProgram_of_nonhalt source target encode c hAvoid.1 hprogram]
      cases hs : TM2.step source c with
      | none =>
          simp only [hs, Option.map_none, Option.bind_none] at hrun ⊢
          rw [iterate_optionBind_none] at hrun
          contradiction
      | some c' =>
          simp only [hs, Option.map_some, Option.bind_some] at hrun ⊢
          have hAvoid' : AvoidsHalts source n c' := by
            simpa [hs] using hAvoid.2
          exact ih hrun hAvoid'

end Lax20Proofs.RamToTM
