import Lax51Proofs.RamToTM.ShiftMacro
import Lax51Proofs.RamToTM.WordOperations

namespace Lax51Proofs.RamToTM

open Turing TM2

inductive ShiftRightLabel | discard | prepend | first | second | done
  deriving DecidableEq, Fintype, Inhabited

def shiftRightMachine : Turing.FinTM2 where
  K := ShiftStack
  k₀ := .source
  k₁ := .result
  Γ _ := Bool
  Λ := ShiftRightLabel
  main := .discard
  σ := MoveControl
  initialState := default
  m
    | .discard =>
        .pop .source (fun _ _ => default) (.goto fun _ => .prepend)
    | .prepend =>
        .push .result (fun _ => false) (.goto fun _ => .first)
    | .first => moveIteration .source .temp .first .second
    | .second => moveIteration .temp .result .second .done
    | .done => .halt

def shiftRightCfg (l : ShiftRightLabel) (source temp result : List Bool) :
    shiftRightMachine.Cfg where
  l := some l
  var := default
  stk := shiftStacks source temp result

@[simp] theorem shiftRight_step_discard (a : Bool) (as temp result : List Bool) :
    shiftRightMachine.step (shiftRightCfg .discard (a :: as) temp result) =
      some (shiftRightCfg .prepend as temp result) := by
  change some (TM2.stepAux
    (.pop ShiftStack.source (fun _ _ => (default : MoveControl))
      (.goto fun _ => ShiftRightLabel.prepend))
    default (shiftStacks (a :: as) temp result)) = _
  simp [shiftRightCfg, shiftStacks, Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem shiftRight_step_prepend (source temp result : List Bool) :
    shiftRightMachine.step (shiftRightCfg .prepend source temp result) =
      some (shiftRightCfg .first source temp (false :: result)) := by
  change some (TM2.stepAux
    (.push ShiftStack.result (fun _ : MoveControl => false)
      (.goto fun _ => ShiftRightLabel.first))
    default (shiftStacks source temp result)) = _
  simp [shiftRightCfg, shiftStacks, Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem shiftRight_step_first_cons (a : Bool)
    (as temp result : List Bool) :
    shiftRightMachine.step (shiftRightCfg .first (a :: as) temp result) =
      some (shiftRightCfg .first as (a :: temp) result) := by
  change some (TM2.stepAux
    (moveIteration ShiftStack.source ShiftStack.temp ShiftRightLabel.first
      ShiftRightLabel.second)
    default (shiftStacks (a :: as) temp result)) = _
  simp [moveIteration, shiftRightCfg, shiftStacks, Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem shiftRight_step_first_nil (temp result : List Bool) :
    shiftRightMachine.step (shiftRightCfg .first [] temp result) =
      some (shiftRightCfg .second [] temp result) := by
  change some (TM2.stepAux
    (moveIteration ShiftStack.source ShiftStack.temp ShiftRightLabel.first
      ShiftRightLabel.second)
    default (shiftStacks [] temp result)) = _
  simp [moveIteration, shiftRightCfg, shiftStacks]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem shiftRight_step_second_cons (source result : List Bool)
    (a : Bool) (temp : List Bool) :
    shiftRightMachine.step (shiftRightCfg .second source (a :: temp) result) =
      some (shiftRightCfg .second source temp (a :: result)) := by
  change some (TM2.stepAux
    (moveIteration ShiftStack.temp ShiftStack.result ShiftRightLabel.second
      ShiftRightLabel.done)
    default (shiftStacks source (a :: temp) result)) = _
  simp [moveIteration, shiftRightCfg, shiftStacks, Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem shiftRight_step_second_nil (source result : List Bool) :
    shiftRightMachine.step (shiftRightCfg .second source [] result) =
      some (shiftRightCfg .done source [] result) := by
  change some (TM2.stepAux
    (moveIteration ShiftStack.temp ShiftStack.result ShiftRightLabel.second
      ShiftRightLabel.done)
    default (shiftStacks source [] result)) = _
  simp [moveIteration, shiftRightCfg, shiftStacks]
  congr 2
  funext k
  cases k <;> rfl

theorem shiftRight_first_iterate (source temp result : List Bool) :
    ((fun o : Option shiftRightMachine.Cfg =>
      o.bind shiftRightMachine.step)^[source.length])
      (some (shiftRightCfg .first source temp result)) =
    some (shiftRightCfg .first [] (source.reverse ++ temp) result) := by
  induction source generalizing temp with
  | nil => rfl
  | cons a as ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, shiftRight_step_first_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem shiftRight_second_iterate (source temp result : List Bool) :
    ((fun o : Option shiftRightMachine.Cfg =>
      o.bind shiftRightMachine.step)^[temp.length])
      (some (shiftRightCfg .second source temp result)) =
    some (shiftRightCfg .second source [] (temp.reverse ++ result)) := by
  induction temp generalizing result with
  | nil => rfl
  | cons a temp ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, shiftRight_step_second_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem shiftRightMachine_correct_nonempty (a : Bool) (as : List Bool) :
    ((fun o : Option shiftRightMachine.Cfg =>
      o.bind shiftRightMachine.step)^[2 * (a :: as).length + 2])
      (some (shiftRightCfg .discard (a :: as) [] [])) =
    some (shiftRightCfg .done [] [] (shiftRightBits (a :: as))) := by
  let stepO := fun o : Option shiftRightMachine.Cfg =>
    o.bind shiftRightMachine.step
  have chain {m n : Nat} {x y z : Option shiftRightMachine.Cfg}
      (h₁ : (stepO^[m]) x = y) (h₂ : (stepO^[n]) y = z) :
      (stepO^[m + n]) x = z := by
    rw [Nat.add_comm, Function.iterate_add_apply, h₁, h₂]
  have hd : (stepO^[1])
      (some (shiftRightCfg .discard (a :: as) [] [])) =
      some (shiftRightCfg .prepend as [] []) := by
    simpa [stepO] using shiftRight_step_discard a as [] []
  have hp : (stepO^[1]) (some (shiftRightCfg .prepend as [] [])) =
      some (shiftRightCfg .first as [] [false]) := by
    simpa [stepO] using shiftRight_step_prepend as [] []
  have hfirst := shiftRight_first_iterate as [] [false]
  simp only [List.append_nil] at hfirst
  have hf : (stepO^[1])
      (some (shiftRightCfg .first [] as.reverse [false])) =
      some (shiftRightCfg .second [] as.reverse [false]) := by
    simpa [stepO] using shiftRight_step_first_nil as.reverse [false]
  have hsecond := shiftRight_second_iterate [] as.reverse [false]
  simp only [List.reverse_reverse] at hsecond
  have hs : (stepO^[1])
      (some (shiftRightCfg .second [] [] (as ++ [false]))) =
      some (shiftRightCfg .done [] [] (as ++ [false])) := by
    simpa [stepO] using shiftRight_step_second_nil [] (as ++ [false])
  have hall := chain (chain (chain (chain (chain hd hp) hfirst) hf) hsecond) hs
  simp only [List.length_reverse] at hall
  have ht : 1 + 1 + as.length + 1 + as.length + 1 =
      2 * (a :: as).length + 2 := by simp; omega
  rw [ht] at hall
  simpa [stepO, shiftRightBits] using hall

end Lax51Proofs.RamToTM
