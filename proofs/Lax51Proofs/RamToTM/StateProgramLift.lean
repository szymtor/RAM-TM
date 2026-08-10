import Lax51Proofs.RamToTM.LiteralOperandPipeline

namespace Lax51Proofs.RamToTM

open Turing TM2

/-! Change only the finite control state of a TM program through a lawful
lens.  Unlike `lensRenameStmt`, this construction leaves both stack and label
types unchanged, which is exactly what is needed to install the already
verified arithmetic pipelines in `FullInterpreterState`. -/

def liftStateStmt {alpha K L small big : Type} [DecidableEq K]
    (lens : StateLens small big) :
    TM2.Stmt (fun _ : K => alpha) L small ->
      TM2.Stmt (fun _ : K => alpha) L big
  | .push k f q => .push k (fun s => f (lens.get s)) (liftStateStmt lens q)
  | .peek k f q => .peek k
      (fun s a => lens.put s (f (lens.get s) a)) (liftStateStmt lens q)
  | .pop k f q => .pop k
      (fun s a => lens.put s (f (lens.get s) a)) (liftStateStmt lens q)
  | .load f q => .load (fun s => lens.put s (f (lens.get s)))
      (liftStateStmt lens q)
  | .branch f q1 q2 => .branch (fun s => f (lens.get s))
      (liftStateStmt lens q1) (liftStateStmt lens q2)
  | .goto f => .goto (fun s => f (lens.get s))
  | .halt => .halt

def liftStateCfg {alpha K L small big : Type}
    (lens : StateLens small big)
    (c : TM2.Cfg (fun _ : K => alpha) L small) (ambient : big) :
    TM2.Cfg (fun _ : K => alpha) L big where
  l := c.l
  var := lens.put ambient c.var
  stk := c.stk

theorem stepAux_liftStateStmt {alpha K L small big : Type} [DecidableEq K]
    (lens : StateLens small big)
    (q : TM2.Stmt (fun _ : K => alpha) L small)
    (localState : small) (ambient : big) (tapes : K -> List alpha) :
    TM2.stepAux (liftStateStmt lens q) (lens.put ambient localState) tapes =
      liftStateCfg lens (TM2.stepAux q localState tapes) ambient := by
  induction q generalizing localState tapes with
  | push k f q ih =>
      simp only [liftStateStmt, TM2.stepAux, lens.get_put]
      exact ih _ _
  | peek k f q ih =>
      simp only [liftStateStmt, TM2.stepAux, lens.get_put, lens.put_put]
      exact ih _ _
  | pop k f q ih =>
      simp only [liftStateStmt, TM2.stepAux, lens.get_put, lens.put_put]
      exact ih _ _
  | load f q ih =>
      simp only [liftStateStmt, TM2.stepAux, lens.get_put, lens.put_put]
      exact ih _ _
  | branch f q1 q2 ih1 ih2 =>
      simp only [liftStateStmt, TM2.stepAux, lens.get_put]
      cases h : f localState <;> simp [h]
      · exact ih2 _ _
      · exact ih1 _ _
  | goto f => simp [liftStateStmt, TM2.stepAux, liftStateCfg, lens.get_put]
  | halt => simp [liftStateStmt, TM2.stepAux, liftStateCfg]

def liftStateProgram {alpha K L small big : Type} [DecidableEq K]
    (lens : StateLens small big)
    (program : L -> TM2.Stmt (fun _ : K => alpha) L small) :
    L -> TM2.Stmt (fun _ : K => alpha) L big :=
  fun l => liftStateStmt lens (program l)

theorem step_liftStateProgram {alpha K L small big : Type} [DecidableEq K]
    (lens : StateLens small big)
    (program : L -> TM2.Stmt (fun _ : K => alpha) L small)
    (c : TM2.Cfg (fun _ : K => alpha) L small) (ambient : big) :
    TM2.step (liftStateProgram lens program) (liftStateCfg lens c ambient) =
      (TM2.step program c).map (fun d => liftStateCfg lens d ambient) := by
  rcases c with ⟨l, localState, tapes⟩
  cases l with
  | none => rfl
  | some l =>
      simp only [liftStateCfg, Option.map_some, TM2.step, liftStateProgram]
      rw [stepAux_liftStateStmt]
      rfl

theorem iterate_liftStateProgram {alpha K L small big : Type} [DecidableEq K]
    (lens : StateLens small big)
    (program : L -> TM2.Stmt (fun _ : K => alpha) L small)
    (n : Nat) (c : TM2.Cfg (fun _ : K => alpha) L small) (ambient : big) :
    ((fun o => o.bind (TM2.step (liftStateProgram lens program)))^[n])
        (some (liftStateCfg lens c ambient)) =
      (((fun o => o.bind (TM2.step program))^[n]) (some c)).map
        (fun d => liftStateCfg lens d ambient) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [Option.bind_some, step_liftStateProgram]
      cases h : TM2.step program c with
      | none =>
          simp only [Option.map_none, Option.bind_none]
          rw [iterate_optionBind_none, iterate_optionBind_none]
          rfl
      | some d =>
          simp only [Option.map_some, Option.bind_some]
          exact ih d

theorem transport_iterate_liftStateProgram
    {alpha K L small big : Type} [DecidableEq K]
    (lens : StateLens small big)
    (program : L -> TM2.Stmt (fun _ : K => alpha) L small)
    {n : Nat} {c d : TM2.Cfg (fun _ : K => alpha) L small}
    (h : ((fun o => o.bind (TM2.step program))^[n]) (some c) = some d)
    (ambient : big) :
    ((fun o => o.bind (TM2.step (liftStateProgram lens program)))^[n])
      (some (liftStateCfg lens c ambient)) =
        some (liftStateCfg lens d ambient) := by
  rw [iterate_liftStateProgram, h]
  rfl

end Lax51Proofs.RamToTM
