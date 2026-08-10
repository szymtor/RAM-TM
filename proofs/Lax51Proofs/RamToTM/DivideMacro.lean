import Lax51Proofs.RamToTM.MultiplyMacro

namespace Lax51Proofs.RamToTM

open Turing TM2

/-! A width-uniform restoring divider.  The dividend is supplied most
significant bit first, while divisor and remainder words are little endian.
Each round shifts one dividend bit into the remainder and performs one ripple
subtraction.  A borrow restores the old remainder; otherwise the difference
is retained.  Thus the number of machine steps is quadratic in the word
width, independently of the numeric values. -/

structure DivControl where
  held : Option Bool
  selected : Bool
  left : Option Bool
  right : Option Bool
  borrow : Bool
  divisorNonzero : Bool
  deriving DecidableEq, Fintype, Inhabited

def DivControl.clearHeld (s : DivControl) : DivControl := { s with held := none }

def DivControl.diffBit (s : DivControl) : Bool :=
  (fullSubtractor (s.left.getD false) (s.right.getD false) s.borrow).1

def DivControl.subAdvance (s : DivControl) : DivControl :=
  { s with
    borrow := (fullSubtractor (s.left.getD false) (s.right.getD false) s.borrow).2,
    left := none, right := none }

inductive DivStack
  | dividend | divisor | remainder | quotient
  | divisorBackup | remainderBackup | differenceReverse | shiftTemp
  deriving DecidableEq, Fintype, Inhabited

inductive DivLabel
  | inspectDivisor | restoreInspectedDivisor | dispatch
  | zeroLoop | outer
  | shiftFirst | shiftDiscard | shiftSecond | shiftPrepend
  | subtract | restoreDivisor | choose
  | discardDifference | restoreRemainder
  | discardOldRemainder | restoreDifference | emit
  | done
  deriving DecidableEq, Fintype, Inhabited

def divMoveIteration (source target : DivStack) (loop done : DivLabel) :
    TM2.Stmt (fun _ : DivStack => Bool) DivLabel DivControl :=
  .pop source (fun s a => { s with held := a }) <|
    .branch (fun s => s.held.isNone)
      (.load DivControl.clearHeld <| .goto fun _ => done)
      (.push target (fun s => s.held.getD false) <|
        .load DivControl.clearHeld <| .goto fun _ => loop)

def divDiscardIteration (source : DivStack) (loop done : DivLabel) :
    TM2.Stmt (fun _ : DivStack => Bool) DivLabel DivControl :=
  .pop source (fun s a => { s with held := a }) <|
    .branch (fun s => s.held.isNone)
      (.load DivControl.clearHeld <| .goto fun _ => done)
      (.load DivControl.clearHeld <| .goto fun _ => loop)

def divMachine : Turing.FinTM2 where
  K := DivStack
  k₀ := .dividend
  k₁ := .quotient
  Γ _ := Bool
  Λ := DivLabel
  main := .inspectDivisor
  σ := DivControl
  initialState := default
  m
    | .inspectDivisor =>
        .pop .divisor (fun s a =>
          { s with
            held := a,
            divisorNonzero := s.divisorNonzero || a.getD false }) <|
          .branch (fun s => s.held.isNone)
            (.load DivControl.clearHeld <| .goto fun _ => .restoreInspectedDivisor)
            (.push .divisorBackup (fun s => s.held.getD false) <|
              .load DivControl.clearHeld <| .goto fun _ => .inspectDivisor)
    | .restoreInspectedDivisor =>
        divMoveIteration .divisorBackup .divisor .restoreInspectedDivisor .dispatch
    | .dispatch => .branch DivControl.divisorNonzero
        (.goto fun _ => .outer) (.goto fun _ => .zeroLoop)
    | .zeroLoop =>
        .pop .dividend (fun s a => { s with held := a }) <|
          .branch (fun s => s.held.isNone)
            (.load DivControl.clearHeld <| .goto fun _ => .done)
            (.push .quotient (fun _ => false) <|
              .load DivControl.clearHeld <| .goto fun _ => .zeroLoop)
    | .outer =>
        .pop .dividend (fun s a => { s with held := a }) <|
          .branch (fun s => s.held.isNone)
            (.load DivControl.clearHeld <| .goto fun _ => .done)
            (.load (fun s => { s with selected := s.held.getD false, held := none }) <|
              .goto fun _ => .shiftFirst)
    | .shiftFirst => divMoveIteration .remainder .shiftTemp .shiftFirst .shiftDiscard
    | .shiftDiscard =>
        .pop .shiftTemp (fun s _ => DivControl.clearHeld s) <|
          .goto fun _ => .shiftSecond
    | .shiftSecond => divMoveIteration .shiftTemp .remainder .shiftSecond .shiftPrepend
    | .shiftPrepend =>
        .push .remainder DivControl.selected <|
          .load (fun s => { s with borrow := false, left := none, right := none }) <|
            .goto fun _ => .subtract
    | .subtract =>
        .pop .remainder (fun s a => { s with left := a }) <|
          .branch (fun s => s.left.isNone)
            (.goto fun _ => .restoreDivisor)
            (.pop .divisor (fun s b => { s with right := b }) <|
              .push .remainderBackup (fun s => s.left.getD false) <|
                .push .divisorBackup (fun s => s.right.getD false) <|
                  .push .differenceReverse DivControl.diffBit <|
                    .load DivControl.subAdvance <| .goto fun _ => .subtract)
    | .restoreDivisor =>
        divMoveIteration .divisorBackup .divisor .restoreDivisor .choose
    | .choose => .branch DivControl.borrow
        (.goto fun _ => .discardDifference) (.goto fun _ => .discardOldRemainder)
    | .discardDifference =>
        divDiscardIteration .differenceReverse .discardDifference .restoreRemainder
    | .restoreRemainder =>
        divMoveIteration .remainderBackup .remainder .restoreRemainder .emit
    | .discardOldRemainder =>
        divDiscardIteration .remainderBackup .discardOldRemainder .restoreDifference
    | .restoreDifference =>
        divMoveIteration .differenceReverse .remainder .restoreDifference .emit
    | .emit =>
        .push .quotient (fun s => !s.borrow) <|
          .load (fun s =>
            { s with
              held := none, selected := false, left := none, right := none,
              borrow := false }) <|
            .goto fun _ => .outer
    | .done => .halt

def divStacks (dividend divisor remainder quotient divisorBackup remainderBackup
    differenceReverse shiftTemp : List Bool) : DivStack → List Bool
  | .dividend => dividend
  | .divisor => divisor
  | .remainder => remainder
  | .quotient => quotient
  | .divisorBackup => divisorBackup
  | .remainderBackup => remainderBackup
  | .differenceReverse => differenceReverse
  | .shiftTemp => shiftTemp

def divCfg (label : DivLabel) (state : DivControl)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp : List Bool) : divMachine.Cfg where
  l := some label
  var := state
  stk := divStacks dividend divisor remainder quotient divisorBackup remainderBackup
    differenceReverse shiftTemp

def divInitialCfg (dividend divisor remainder : List Bool) : divMachine.Cfg :=
  divCfg .inspectDivisor default dividend divisor remainder [] [] [] [] []

def divCleanCfg (label : DivLabel) (divisorNonzero : Bool)
    (dividend divisor remainder quotient divisorBackup : List Bool) :
    divMachine.Cfg :=
  divCfg label { (default : DivControl) with divisorNonzero := divisorNonzero }
    dividend divisor remainder quotient divisorBackup [] [] []

def divDoneCfg (divisorNonzero : Bool) (divisor remainder quotient : List Bool) :
    divMachine.Cfg :=
  divCfg .done { (default : DivControl) with divisorNonzero := divisorNonzero }
    [] divisor remainder quotient [] [] [] []

def divPhaseCfg (label : DivLabel) (selected borrow : Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp : List Bool) : divMachine.Cfg :=
  divCfg label
    { (default : DivControl) with
      selected := selected, borrow := borrow,
      divisorNonzero := true }
    dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp

def divSubCfg (selected borrow : Bool) (left right : Option Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse : List Bool) : divMachine.Cfg :=
  divCfg .subtract
    { (default : DivControl) with
      selected := selected, borrow := borrow, left := left, right := right,
      divisorNonzero := true }
    dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse []

def containsTrue : List Bool → Bool
  | [] => false
  | b :: bs => b || containsTrue bs

@[simp] theorem containsTrue_append (xs ys : List Bool) :
    containsTrue (xs ++ ys) = (containsTrue xs || containsTrue ys) := by
  induction xs with
  | nil => simp [containsTrue]
  | cons x xs ih => simp [containsTrue, ih, Bool.or_assoc]

@[simp] theorem containsTrue_reverse (bits : List Bool) :
    containsTrue bits.reverse = containsTrue bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
      simp [containsTrue, List.reverse_cons, ih, Bool.or_comm]

theorem containsTrue_false_bitsValue_zero {bits : List Bool}
    (h : containsTrue bits = false) : bitsValue bits = 0 := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
      simp [containsTrue] at h
      simp [bitsValue, h.1, ih h.2]

@[simp] theorem div_step_inspect_cons (nz b : Bool)
    (dividend divisor remainder backup : List Bool) :
    divMachine.step
        (divCleanCfg .inspectDivisor nz dividend (b :: divisor) remainder [] backup) =
      some (divCleanCfg .inspectDivisor (nz || b) dividend divisor remainder []
        (b :: backup)) := by
  simp [divMachine, divCleanCfg, divCfg, divStacks, DivControl.clearHeld,
    Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem div_step_inspect_nil (nz : Bool)
    (dividend remainder backup : List Bool) :
    divMachine.step
        (divCleanCfg .inspectDivisor nz dividend [] remainder [] backup) =
      some (divCleanCfg .restoreInspectedDivisor nz dividend [] remainder [] backup) := by
  simp [divMachine, divCleanCfg, divCfg, divStacks, DivControl.clearHeld]
  congr 2
  funext k
  cases k <;> rfl

theorem div_inspect_iterate (nz : Bool)
    (dividend divisor remainder backup : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[divisor.length])
        (some (divCleanCfg .inspectDivisor nz dividend divisor remainder [] backup)) =
      some (divCleanCfg .inspectDivisor (nz || containsTrue divisor) dividend []
        remainder [] (divisor.reverse ++ backup)) := by
  induction divisor generalizing nz backup with
  | nil => simp [containsTrue]
  | cons b divisor ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_inspect_cons]
      rw [ih]
      simp [containsTrue, List.reverse_cons, List.append_assoc, Bool.or_assoc]

@[simp] theorem div_step_restore_inspected_cons (nz b : Bool)
    (dividend divisor remainder quotient backup : List Bool) :
    divMachine.step (divCleanCfg .restoreInspectedDivisor nz dividend divisor remainder
        quotient (b :: backup)) =
      some (divCleanCfg .restoreInspectedDivisor nz dividend (b :: divisor) remainder
        quotient backup) := by
  simp [divMachine, divMoveIteration, divCleanCfg, divCfg, divStacks,
    DivControl.clearHeld, Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem div_step_restore_inspected_nil (nz : Bool)
    (dividend divisor remainder quotient : List Bool) :
    divMachine.step (divCleanCfg .restoreInspectedDivisor nz dividend divisor remainder
        quotient []) =
      some (divCleanCfg .dispatch nz dividend divisor remainder quotient []) := by
  simp [divMachine, divMoveIteration, divCleanCfg, divCfg, divStacks,
    DivControl.clearHeld]
  congr 2
  funext k
  cases k <;> rfl

theorem div_restore_inspected_iterate (nz : Bool)
    (dividend divisor remainder quotient backup : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[backup.length])
        (some (divCleanCfg .restoreInspectedDivisor nz dividend divisor remainder
          quotient backup)) =
      some (divCleanCfg .restoreInspectedDivisor nz dividend
        (backup.reverse ++ divisor) remainder quotient []) := by
  induction backup generalizing divisor with
  | nil => rfl
  | cons b backup ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_restore_inspected_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

@[simp] theorem div_step_dispatch_false
    (dividend divisor remainder quotient : List Bool) :
    divMachine.step (divCleanCfg .dispatch false dividend divisor remainder quotient []) =
      some (divCleanCfg .zeroLoop false dividend divisor remainder quotient []) := by
  rfl

@[simp] theorem div_step_dispatch_true
    (dividend divisor remainder quotient : List Bool) :
    divMachine.step (divCleanCfg .dispatch true dividend divisor remainder quotient []) =
      some (divCleanCfg .outer true dividend divisor remainder quotient []) := by
  rfl

@[simp] theorem div_step_outer_nil
    (divisor remainder quotient : List Bool) :
    divMachine.step (divCleanCfg .outer true [] divisor remainder quotient []) =
      some (divDoneCfg true divisor remainder quotient) := by
  simp [divMachine, divCleanCfg, divDoneCfg, divCfg, divStacks,
    DivControl.clearHeld]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem div_step_zero_cons (b : Bool)
    (dividend divisor remainder quotient : List Bool) :
    divMachine.step
        (divCleanCfg .zeroLoop false (b :: dividend) divisor remainder quotient []) =
      some (divCleanCfg .zeroLoop false dividend divisor remainder
        (false :: quotient) []) := by
  simp [divMachine, divCleanCfg, divCfg, divStacks, DivControl.clearHeld,
    Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem div_step_zero_nil
    (divisor remainder quotient : List Bool) :
    divMachine.step (divCleanCfg .zeroLoop false [] divisor remainder quotient []) =
      some (divDoneCfg false divisor remainder quotient) := by
  simp [divMachine, divCleanCfg, divDoneCfg, divCfg, divStacks,
    DivControl.clearHeld]
  congr 2
  funext k
  cases k <;> rfl

theorem div_zero_iterate (dividend divisor remainder quotient : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[dividend.length])
        (some (divCleanCfg .zeroLoop false dividend divisor remainder quotient [])) =
      some (divCleanCfg .zeroLoop false [] divisor remainder
        ((dividend.map fun _ => false).reverse ++ quotient) []) := by
  induction dividend generalizing quotient with
  | nil => rfl
  | cons b dividend ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_zero_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

@[simp] theorem div_step_outer_cons (b : Bool)
    (dividend divisor remainder quotient : List Bool) :
    divMachine.step
        (divCleanCfg .outer true (b :: dividend) divisor remainder quotient []) =
      some (divPhaseCfg .shiftFirst b false dividend divisor remainder quotient
        [] [] [] []) := by
  simp [divMachine, divCleanCfg, divPhaseCfg, divCfg, divStacks,
    Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem div_step_shiftFirst_cons (selected borrow x : Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp : List Bool) :
    divMachine.step (divPhaseCfg .shiftFirst selected borrow dividend divisor
        (x :: remainder) quotient divisorBackup remainderBackup differenceReverse
        shiftTemp) =
      some (divPhaseCfg .shiftFirst selected borrow dividend divisor remainder quotient
        divisorBackup remainderBackup differenceReverse (x :: shiftTemp)) := by
  simp [divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
    DivControl.clearHeld, Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem div_step_shiftFirst_nil (selected borrow : Bool)
    (dividend divisor quotient divisorBackup remainderBackup differenceReverse
      shiftTemp : List Bool) :
    divMachine.step (divPhaseCfg .shiftFirst selected borrow dividend divisor []
        quotient divisorBackup remainderBackup differenceReverse shiftTemp) =
      some (divPhaseCfg .shiftDiscard selected borrow dividend divisor [] quotient
        divisorBackup remainderBackup differenceReverse shiftTemp) := by
  simp [divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
    DivControl.clearHeld]
  congr 2
  funext k
  cases k <;> rfl

theorem div_shiftFirst_iterate (selected borrow : Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[remainder.length])
      (some (divPhaseCfg .shiftFirst selected borrow dividend divisor remainder quotient
        divisorBackup remainderBackup differenceReverse shiftTemp)) =
      some (divPhaseCfg .shiftFirst selected borrow dividend divisor [] quotient
        divisorBackup remainderBackup differenceReverse
        (remainder.reverse ++ shiftTemp)) := by
  induction remainder generalizing shiftTemp with
  | nil => rfl
  | cons x remainder ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_shiftFirst_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

@[simp] theorem div_step_shiftDiscard_cons (selected borrow x : Bool)
    (dividend divisor quotient divisorBackup remainderBackup differenceReverse
      shiftTemp : List Bool) :
    divMachine.step (divPhaseCfg .shiftDiscard selected borrow dividend divisor []
        quotient divisorBackup remainderBackup differenceReverse (x :: shiftTemp)) =
      some (divPhaseCfg .shiftSecond selected borrow dividend divisor [] quotient
        divisorBackup remainderBackup differenceReverse shiftTemp) := by
  simp [divMachine, divPhaseCfg, divCfg, divStacks, DivControl.clearHeld,
    Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem div_step_shiftSecond_cons (selected borrow x : Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp : List Bool) :
    divMachine.step (divPhaseCfg .shiftSecond selected borrow dividend divisor remainder
        quotient divisorBackup remainderBackup differenceReverse (x :: shiftTemp)) =
      some (divPhaseCfg .shiftSecond selected borrow dividend divisor (x :: remainder)
        quotient divisorBackup remainderBackup differenceReverse shiftTemp) := by
  simp [divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
    DivControl.clearHeld, Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem div_step_shiftSecond_nil (selected borrow : Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse : List Bool) :
    divMachine.step (divPhaseCfg .shiftSecond selected borrow dividend divisor remainder
        quotient divisorBackup remainderBackup differenceReverse []) =
      some (divPhaseCfg .shiftPrepend selected borrow dividend divisor remainder quotient
        divisorBackup remainderBackup differenceReverse []) := by
  simp [divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
    DivControl.clearHeld]
  congr 2
  funext k
  cases k <;> rfl

theorem div_shiftSecond_iterate (selected borrow : Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[shiftTemp.length])
      (some (divPhaseCfg .shiftSecond selected borrow dividend divisor remainder quotient
        divisorBackup remainderBackup differenceReverse shiftTemp)) =
      some (divPhaseCfg .shiftSecond selected borrow dividend divisor
        (shiftTemp.reverse ++ remainder) quotient divisorBackup remainderBackup
        differenceReverse []) := by
  induction shiftTemp generalizing remainder with
  | nil => rfl
  | cons x shiftTemp ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_shiftSecond_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

@[simp] theorem div_step_shiftPrepend (selected borrow : Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse : List Bool) :
    divMachine.step (divPhaseCfg .shiftPrepend selected borrow dividend divisor remainder
        quotient divisorBackup remainderBackup differenceReverse []) =
      some (divPhaseCfg .subtract selected false dividend divisor (selected :: remainder)
        quotient divisorBackup remainderBackup differenceReverse []) := by
  simp [divMachine, divPhaseCfg, divCfg, divStacks, Function.update]
  congr 2
  funext k
  cases k <;> rfl

theorem div_shift_pipeline (b x : Bool)
    (dividend divisor remainder quotient : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
      2 * (x :: remainder).length + 4])
      (some (divCleanCfg .outer true (b :: dividend) divisor (x :: remainder)
        quotient [])) =
      some (divPhaseCfg .subtract b false dividend divisor
        (shiftInBit b (x :: remainder)) quotient [] [] [] []) := by
  let stepO := fun o : Option divMachine.Cfg => o.bind divMachine.step
  have chain {m n : ℕ} {a c d : Option divMachine.Cfg}
      (h₁ : (stepO^[m]) a = c) (h₂ : (stepO^[n]) c = d) :
      (stepO^[n + m]) a = d := by
    rw [Function.iterate_add_apply, h₁, h₂]
  have houter : (stepO^[1])
      (some (divCleanCfg .outer true (b :: dividend) divisor (x :: remainder)
        quotient [])) =
      some (divPhaseCfg .shiftFirst b false dividend divisor (x :: remainder)
        quotient [] [] [] []) := by
    simpa [stepO] using div_step_outer_cons b dividend divisor (x :: remainder) quotient
  have hfirst := div_shiftFirst_iterate b false dividend divisor (x :: remainder)
    quotient [] [] [] []
  simp only [List.append_nil] at hfirst
  have hfirst0 : (stepO^[1])
      (some (divPhaseCfg .shiftFirst b false dividend divisor [] quotient [] [] []
        (x :: remainder).reverse)) =
      some (divPhaseCfg .shiftDiscard b false dividend divisor [] quotient [] [] []
        (x :: remainder).reverse) := by
    simpa [stepO] using div_step_shiftFirst_nil b false dividend divisor quotient
      [] [] [] (x :: remainder).reverse
  have hdiscard : (stepO^[1])
      (some (divPhaseCfg .shiftDiscard b false dividend divisor [] quotient [] [] []
        (x :: remainder).reverse)) =
      some (divPhaseCfg .shiftSecond b false dividend divisor [] quotient [] [] []
        (x :: remainder).reverse.tail) := by
    cases hrev : (x :: remainder).reverse with
    | nil => simp at hrev
    | cons y ys =>
        simpa [stepO, hrev] using
          div_step_shiftDiscard_cons b false y dividend divisor quotient [] [] [] ys
  have hsecond := div_shiftSecond_iterate b false dividend divisor [] quotient [] [] []
    (x :: remainder).reverse.tail
  simp only [List.append_nil] at hsecond
  have hsecond0 : (stepO^[1])
      (some (divPhaseCfg .shiftSecond b false dividend divisor
        ((x :: remainder).reverse.tail.reverse) quotient [] [] [] [])) =
      some (divPhaseCfg .shiftPrepend b false dividend divisor
        ((x :: remainder).reverse.tail.reverse) quotient [] [] [] []) := by
    simpa [stepO] using div_step_shiftSecond_nil b false dividend divisor
      ((x :: remainder).reverse.tail.reverse) quotient [] [] []
  have hprepend : (stepO^[1])
      (some (divPhaseCfg .shiftPrepend b false dividend divisor
        ((x :: remainder).reverse.tail.reverse) quotient [] [] [] [])) =
      some (divPhaseCfg .subtract b false dividend divisor
        (b :: (x :: remainder).reverse.tail.reverse) quotient [] [] [] []) := by
    simpa [stepO] using div_step_shiftPrepend b false dividend divisor
      ((x :: remainder).reverse.tail.reverse) quotient [] [] []
  have h := chain (chain (chain (chain (chain (chain houter hfirst) hfirst0)
    hdiscard) hsecond) hsecond0) hprepend
  have htime :
      1 + (1 + ((x :: remainder).reverse.tail.length +
        (1 + (1 + ((x :: remainder).length + 1))))) =
        2 * (x :: remainder).length + 4 := by
    simp
    omega
  rw [htime] at h
  have hout : (x :: remainder).reverse.tail.reverse =
      (x :: remainder).take remainder.length := by
    rw [List.tail_reverse, List.reverse_reverse, List.dropLast_eq_take]
    simp
  rw [hout] at h
  simpa [stepO, shiftInBit] using h

@[simp] theorem div_step_subtract_cons (selected borrow x y : Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse : List Bool) :
    divMachine.step (divSubCfg selected borrow none none dividend (y :: divisor)
        (x :: remainder) quotient divisorBackup remainderBackup differenceReverse) =
      some (divSubCfg selected (fullSubtractor x y borrow).2 none none dividend divisor
        remainder quotient (y :: divisorBackup) (x :: remainderBackup)
        ((fullSubtractor x y borrow).1 :: differenceReverse)) := by
  simp [divMachine, divSubCfg, divCfg, divStacks, DivControl.diffBit,
    DivControl.subAdvance, Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem div_step_subtract_nil (selected borrow : Bool)
    (dividend quotient divisorBackup remainderBackup differenceReverse : List Bool) :
    divMachine.step (divSubCfg selected borrow none none dividend [] [] quotient
        divisorBackup remainderBackup differenceReverse) =
      some (divPhaseCfg .restoreDivisor selected borrow dividend [] [] quotient
        divisorBackup remainderBackup differenceReverse []) := by
  simp [divMachine, divSubCfg, divPhaseCfg, divCfg, divStacks]
  congr 2
  funext k
  cases k <;> rfl

theorem div_subtract_iterate (selected borrow : Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse : List Bool) (hlen : remainder.length = divisor.length) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[remainder.length])
      (some (divSubCfg selected borrow none none dividend divisor remainder quotient
        divisorBackup remainderBackup differenceReverse)) =
      some (divSubCfg selected (subBorrowOut remainder divisor borrow) none none dividend
        [] [] quotient (divisor.reverse ++ divisorBackup)
        (remainder.reverse ++ remainderBackup)
        ((subBits remainder divisor borrow).reverse ++ differenceReverse)) := by
  induction remainder generalizing divisor borrow divisorBackup remainderBackup
      differenceReverse with
  | nil =>
      cases divisor with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons x remainder ih =>
      cases divisor with
      | nil => simp at hlen
      | cons y divisor =>
          simp at hlen
          rw [List.length_cons, Function.iterate_succ_apply]
          simp only [Option.bind_some, div_step_subtract_cons]
          rw [ih (borrow := (fullSubtractor x y borrow).2)
            (divisor := divisor) (hlen := hlen)]
          simp [subBorrowOut, subBits, List.reverse_cons, List.append_assoc]

@[simp] theorem div_step_restoreDivisor_cons (selected borrow y : Bool)
    (dividend divisor quotient divisorBackup remainderBackup differenceReverse :
      List Bool) :
    divMachine.step (divPhaseCfg .restoreDivisor selected borrow dividend divisor []
        quotient (y :: divisorBackup) remainderBackup differenceReverse []) =
      some (divPhaseCfg .restoreDivisor selected borrow dividend (y :: divisor) []
        quotient divisorBackup remainderBackup differenceReverse []) := by
  simp [divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
    DivControl.clearHeld, Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem div_step_restoreDivisor_nil (selected borrow : Bool)
    (dividend divisor quotient remainderBackup differenceReverse : List Bool) :
    divMachine.step (divPhaseCfg .restoreDivisor selected borrow dividend divisor []
        quotient [] remainderBackup differenceReverse []) =
      some (divPhaseCfg .choose selected borrow dividend divisor [] quotient []
        remainderBackup differenceReverse []) := by
  simp [divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
    DivControl.clearHeld]
  congr 2
  funext k
  cases k <;> rfl

theorem div_restoreDivisor_iterate (selected borrow : Bool)
    (dividend divisor quotient divisorBackup remainderBackup differenceReverse :
      List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[divisorBackup.length])
      (some (divPhaseCfg .restoreDivisor selected borrow dividend divisor [] quotient
        divisorBackup remainderBackup differenceReverse [])) =
      some (divPhaseCfg .restoreDivisor selected borrow dividend
        (divisorBackup.reverse ++ divisor) [] quotient [] remainderBackup
        differenceReverse []) := by
  induction divisorBackup generalizing divisor with
  | nil => rfl
  | cons y divisorBackup ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_restoreDivisor_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

@[simp] theorem div_step_choose_true (selected : Bool)
    (dividend divisor quotient remainderBackup differenceReverse : List Bool) :
    divMachine.step (divPhaseCfg .choose selected true dividend divisor [] quotient []
        remainderBackup differenceReverse []) =
      some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
        remainderBackup differenceReverse []) := by
  rfl

@[simp] theorem div_step_choose_false (selected : Bool)
    (dividend divisor quotient remainderBackup differenceReverse : List Bool) :
    divMachine.step (divPhaseCfg .choose selected false dividend divisor [] quotient []
        remainderBackup differenceReverse []) =
      some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
        remainderBackup differenceReverse []) := by
  rfl

@[simp] theorem div_step_discardDifference_cons (selected x : Bool)
    (dividend divisor quotient remainderBackup differenceReverse : List Bool) :
    divMachine.step (divPhaseCfg .discardDifference selected true dividend divisor []
        quotient [] remainderBackup (x :: differenceReverse) []) =
      some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
        remainderBackup differenceReverse []) := by
  simp [divMachine, divDiscardIteration, divPhaseCfg, divCfg, divStacks,
    DivControl.clearHeld, Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem div_step_discardDifference_nil (selected : Bool)
    (dividend divisor quotient remainderBackup : List Bool) :
    divMachine.step (divPhaseCfg .discardDifference selected true dividend divisor []
        quotient [] remainderBackup [] []) =
      some (divPhaseCfg .restoreRemainder selected true dividend divisor [] quotient []
        remainderBackup [] []) := by
  simp [divMachine, divDiscardIteration, divPhaseCfg, divCfg, divStacks,
    DivControl.clearHeld]
  congr 2
  funext k
  cases k <;> rfl

theorem div_discardDifference_iterate (selected : Bool)
    (dividend divisor quotient remainderBackup differenceReverse : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[differenceReverse.length])
      (some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
        remainderBackup differenceReverse [])) =
      some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
        remainderBackup [] []) := by
  induction differenceReverse with
  | nil => rfl
  | cons x differenceReverse ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_discardDifference_cons, ih]

@[simp] theorem div_step_restoreRemainder_cons (selected x : Bool)
    (dividend divisor remainder quotient remainderBackup : List Bool) :
    divMachine.step (divPhaseCfg .restoreRemainder selected true dividend divisor
        remainder quotient [] (x :: remainderBackup) [] []) =
      some (divPhaseCfg .restoreRemainder selected true dividend divisor
        (x :: remainder) quotient [] remainderBackup [] []) := by
  simp [divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
    DivControl.clearHeld, Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem div_step_restoreRemainder_nil (selected : Bool)
    (dividend divisor remainder quotient : List Bool) :
    divMachine.step (divPhaseCfg .restoreRemainder selected true dividend divisor
        remainder quotient [] [] [] []) =
      some (divPhaseCfg .emit selected true dividend divisor remainder quotient
        [] [] [] []) := by
  simp [divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
    DivControl.clearHeld]
  congr 2
  funext k
  cases k <;> rfl

theorem div_restoreRemainder_iterate (selected : Bool)
    (dividend divisor remainder quotient remainderBackup : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[remainderBackup.length])
      (some (divPhaseCfg .restoreRemainder selected true dividend divisor remainder
        quotient [] remainderBackup [] [])) =
      some (divPhaseCfg .restoreRemainder selected true dividend divisor
        (remainderBackup.reverse ++ remainder) quotient [] [] [] []) := by
  induction remainderBackup generalizing remainder with
  | nil => rfl
  | cons x remainderBackup ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_restoreRemainder_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

@[simp] theorem div_step_discardOldRemainder_cons (selected x : Bool)
    (dividend divisor quotient remainderBackup differenceReverse : List Bool) :
    divMachine.step (divPhaseCfg .discardOldRemainder selected false dividend divisor []
        quotient [] (x :: remainderBackup) differenceReverse []) =
      some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
        remainderBackup differenceReverse []) := by
  simp [divMachine, divDiscardIteration, divPhaseCfg, divCfg, divStacks,
    DivControl.clearHeld, Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem div_step_discardOldRemainder_nil (selected : Bool)
    (dividend divisor quotient differenceReverse : List Bool) :
    divMachine.step (divPhaseCfg .discardOldRemainder selected false dividend divisor []
        quotient [] [] differenceReverse []) =
      some (divPhaseCfg .restoreDifference selected false dividend divisor [] quotient []
        [] differenceReverse []) := by
  simp [divMachine, divDiscardIteration, divPhaseCfg, divCfg, divStacks,
    DivControl.clearHeld]
  congr 2
  funext k
  cases k <;> rfl

theorem div_discardOldRemainder_iterate (selected : Bool)
    (dividend divisor quotient remainderBackup differenceReverse : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[remainderBackup.length])
      (some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
        remainderBackup differenceReverse [])) =
      some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
        [] differenceReverse []) := by
  induction remainderBackup with
  | nil => rfl
  | cons x remainderBackup ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_discardOldRemainder_cons, ih]

@[simp] theorem div_step_restoreDifference_cons (selected x : Bool)
    (dividend divisor remainder quotient differenceReverse : List Bool) :
    divMachine.step (divPhaseCfg .restoreDifference selected false dividend divisor
        remainder quotient [] [] (x :: differenceReverse) []) =
      some (divPhaseCfg .restoreDifference selected false dividend divisor
        (x :: remainder) quotient [] [] differenceReverse []) := by
  simp [divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
    DivControl.clearHeld, Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem div_step_restoreDifference_nil (selected : Bool)
    (dividend divisor remainder quotient : List Bool) :
    divMachine.step (divPhaseCfg .restoreDifference selected false dividend divisor
        remainder quotient [] [] [] []) =
      some (divPhaseCfg .emit selected false dividend divisor remainder quotient
        [] [] [] []) := by
  simp [divMachine, divMoveIteration, divPhaseCfg, divCfg, divStacks,
    DivControl.clearHeld]
  congr 2
  funext k
  cases k <;> rfl

theorem div_restoreDifference_iterate (selected : Bool)
    (dividend divisor remainder quotient differenceReverse : List Bool) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[differenceReverse.length])
      (some (divPhaseCfg .restoreDifference selected false dividend divisor remainder
        quotient [] [] differenceReverse [])) =
      some (divPhaseCfg .restoreDifference selected false dividend divisor
        (differenceReverse.reverse ++ remainder) quotient [] [] [] []) := by
  induction differenceReverse generalizing remainder with
  | nil => rfl
  | cons x differenceReverse ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, div_step_restoreDifference_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

@[simp] theorem div_step_emit (selected borrow : Bool)
    (dividend divisor remainder quotient : List Bool) :
    divMachine.step (divPhaseCfg .emit selected borrow dividend divisor remainder quotient
        [] [] [] []) =
      some (divCleanCfg .outer true dividend divisor remainder
        ((!borrow) :: quotient) []) := by
  simp [divMachine, divPhaseCfg, divCleanCfg, divCfg, divStacks, Function.update]
  congr 2
  funext k
  cases k <;> rfl

theorem div_finalize_true (selected : Bool)
    (dividend divisor quotient remainderBackup differenceReverse : List Bool)
    (hlen : differenceReverse.length = remainderBackup.length) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
      2 * remainderBackup.length + 4])
      (some (divPhaseCfg .choose selected true dividend divisor [] quotient []
        remainderBackup differenceReverse [])) =
      some (divCleanCfg .outer true dividend divisor remainderBackup.reverse
        (false :: quotient) []) := by
  let stepO := fun o : Option divMachine.Cfg => o.bind divMachine.step
  have chain {m n : ℕ} {a c d : Option divMachine.Cfg}
      (h₁ : (stepO^[m]) a = c) (h₂ : (stepO^[n]) c = d) :
      (stepO^[n + m]) a = d := by
    rw [Function.iterate_add_apply, h₁, h₂]
  have hc : (stepO^[1])
      (some (divPhaseCfg .choose selected true dividend divisor [] quotient []
        remainderBackup differenceReverse [])) =
      some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
        remainderBackup differenceReverse []) := by
    simpa [stepO] using div_step_choose_true selected dividend divisor quotient
      remainderBackup differenceReverse
  have hd := div_discardDifference_iterate selected dividend divisor quotient
    remainderBackup differenceReverse
  have hd0 : (stepO^[1])
      (some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
        remainderBackup [] [])) =
      some (divPhaseCfg .restoreRemainder selected true dividend divisor [] quotient []
        remainderBackup [] []) := by
    simpa [stepO] using div_step_discardDifference_nil selected dividend divisor quotient
      remainderBackup
  have hr := div_restoreRemainder_iterate selected dividend divisor [] quotient
    remainderBackup
  simp only [List.append_nil] at hr
  have hr0 : (stepO^[1])
      (some (divPhaseCfg .restoreRemainder selected true dividend divisor
        remainderBackup.reverse quotient [] [] [] [])) =
      some (divPhaseCfg .emit selected true dividend divisor remainderBackup.reverse
        quotient [] [] [] []) := by
    simpa [stepO] using div_step_restoreRemainder_nil selected dividend divisor
      remainderBackup.reverse quotient
  have he : (stepO^[1])
      (some (divPhaseCfg .emit selected true dividend divisor remainderBackup.reverse
        quotient [] [] [] [])) =
      some (divCleanCfg .outer true dividend divisor remainderBackup.reverse
        (false :: quotient) []) := by
    simpa [stepO] using div_step_emit selected true dividend divisor
      remainderBackup.reverse quotient
  have h := chain (chain (chain (chain (chain hc hd) hd0) hr) hr0) he
  have htime :
      1 + (1 + (remainderBackup.length +
        (1 + (differenceReverse.length + 1)))) =
        2 * remainderBackup.length + 4 := by omega
  rw [htime] at h
  simpa [stepO] using h

theorem div_finalize_false (selected : Bool)
    (dividend divisor quotient remainderBackup differenceReverse : List Bool)
    (hlen : remainderBackup.length = differenceReverse.length) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
      2 * remainderBackup.length + 4])
      (some (divPhaseCfg .choose selected false dividend divisor [] quotient []
        remainderBackup differenceReverse [])) =
      some (divCleanCfg .outer true dividend divisor differenceReverse.reverse
        (true :: quotient) []) := by
  let stepO := fun o : Option divMachine.Cfg => o.bind divMachine.step
  have chain {m n : ℕ} {a c d : Option divMachine.Cfg}
      (h₁ : (stepO^[m]) a = c) (h₂ : (stepO^[n]) c = d) :
      (stepO^[n + m]) a = d := by
    rw [Function.iterate_add_apply, h₁, h₂]
  have hc : (stepO^[1])
      (some (divPhaseCfg .choose selected false dividend divisor [] quotient []
        remainderBackup differenceReverse [])) =
      some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
        remainderBackup differenceReverse []) := by
    simpa [stepO] using div_step_choose_false selected dividend divisor quotient
      remainderBackup differenceReverse
  have hd := div_discardOldRemainder_iterate selected dividend divisor quotient
    remainderBackup differenceReverse
  have hd0 : (stepO^[1])
      (some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
        [] differenceReverse [])) =
      some (divPhaseCfg .restoreDifference selected false dividend divisor [] quotient []
        [] differenceReverse []) := by
    simpa [stepO] using div_step_discardOldRemainder_nil selected dividend divisor quotient
      differenceReverse
  have hr := div_restoreDifference_iterate selected dividend divisor [] quotient
    differenceReverse
  simp only [List.append_nil] at hr
  have hr0 : (stepO^[1])
      (some (divPhaseCfg .restoreDifference selected false dividend divisor
        differenceReverse.reverse quotient [] [] [] [])) =
      some (divPhaseCfg .emit selected false dividend divisor differenceReverse.reverse
        quotient [] [] [] []) := by
    simpa [stepO] using div_step_restoreDifference_nil selected dividend divisor
      differenceReverse.reverse quotient
  have he : (stepO^[1])
      (some (divPhaseCfg .emit selected false dividend divisor differenceReverse.reverse
        quotient [] [] [] [])) =
      some (divCleanCfg .outer true dividend divisor differenceReverse.reverse
        (true :: quotient) []) := by
    simpa [stepO] using div_step_emit selected false dividend divisor
      differenceReverse.reverse quotient
  have h := chain (chain (chain (chain (chain hc hd) hd0) hr) hr0) he
  have htime :
      1 + (1 + (differenceReverse.length +
        (1 + (remainderBackup.length + 1)))) =
        2 * remainderBackup.length + 4 := by omega
  rw [htime] at h
  simpa [stepO] using h

theorem div_subtract_pipeline (selected : Bool)
    (dividend divisor candidate quotient : List Bool)
    (hlen : candidate.length = divisor.length) :
    let borrow := subBorrowOut candidate divisor false
    let nextRemainder := if borrow then candidate else subBits candidate divisor false
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
      4 * candidate.length + 6])
      (some (divPhaseCfg .subtract selected false dividend divisor candidate quotient
        [] [] [] [])) =
      some (divCleanCfg .outer true dividend divisor nextRemainder
        ((!borrow) :: quotient) []) := by
  let stepO := fun o : Option divMachine.Cfg => o.bind divMachine.step
  let borrow := subBorrowOut candidate divisor false
  let difference := subBits candidate divisor false
  have chain {m n : ℕ} {a c d : Option divMachine.Cfg}
      (h₁ : (stepO^[m]) a = c) (h₂ : (stepO^[n]) c = d) :
      (stepO^[n + m]) a = d := by
    rw [Function.iterate_add_apply, h₁, h₂]
  have hs := div_subtract_iterate selected false dividend divisor candidate quotient
    [] [] [] hlen
  change (stepO^[candidate.length])
      (some (divPhaseCfg .subtract selected false dividend divisor candidate quotient
        [] [] [] [])) = _ at hs
  simp only [List.append_nil] at hs
  change _ = some (divSubCfg selected borrow none none dividend [] [] quotient
    divisor.reverse candidate.reverse difference.reverse) at hs
  have hs0 : (stepO^[1])
      (some (divSubCfg selected borrow none none dividend [] [] quotient
        divisor.reverse candidate.reverse difference.reverse)) =
      some (divPhaseCfg .restoreDivisor selected borrow dividend [] [] quotient
        divisor.reverse candidate.reverse difference.reverse []) := by
    simpa [stepO] using div_step_subtract_nil selected borrow dividend quotient
      divisor.reverse candidate.reverse difference.reverse
  have hr := div_restoreDivisor_iterate selected borrow dividend [] quotient
    divisor.reverse candidate.reverse difference.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  have hr0 : (stepO^[1])
      (some (divPhaseCfg .restoreDivisor selected borrow dividend divisor [] quotient
        [] candidate.reverse difference.reverse [])) =
      some (divPhaseCfg .choose selected borrow dividend divisor [] quotient []
        candidate.reverse difference.reverse []) := by
    simpa [stepO] using div_step_restoreDivisor_nil selected borrow dividend divisor
      quotient candidate.reverse difference.reverse
  have hp : (stepO^[2 * candidate.length + 4])
      (some (divPhaseCfg .choose selected borrow dividend divisor [] quotient []
        candidate.reverse difference.reverse [])) =
      some (divCleanCfg .outer true dividend divisor
        (if borrow then candidate else difference) ((!borrow) :: quotient) []) := by
    cases hb : borrow with
    | false =>
        have hdlen : candidate.reverse.length = difference.reverse.length := by
          simp [difference, subBits_length_of_eq false hlen]
        simpa [hb] using div_finalize_false selected dividend divisor quotient
          candidate.reverse difference.reverse hdlen
    | true =>
        have hdlen : difference.reverse.length = candidate.reverse.length := by
          simp [difference, subBits_length_of_eq false hlen]
        simpa [hb] using div_finalize_true selected dividend divisor quotient
          candidate.reverse difference.reverse hdlen
  have h := chain (chain (chain (chain hs hs0) hr) hr0) hp
  have htime :
      2 * candidate.length + 4 +
        (1 + (divisor.length + (1 + candidate.length))) =
        4 * candidate.length + 6 := by omega
  rw [htime] at h
  simpa [stepO, borrow, difference] using h

theorem div_round (b x : Bool)
    (dividend divisor remainder quotient : List Bool)
    (hlen : (x :: remainder).length = divisor.length) :
    let candidate := shiftInBit b (x :: remainder)
    let borrow := subBorrowOut candidate divisor false
    let nextRemainder := if borrow then candidate else subBits candidate divisor false
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
      6 * (x :: remainder).length + 10])
      (some (divCleanCfg .outer true (b :: dividend) divisor (x :: remainder)
        quotient [])) =
      some (divCleanCfg .outer true dividend divisor nextRemainder
        ((!borrow) :: quotient) []) := by
  let stepO := fun o : Option divMachine.Cfg => o.bind divMachine.step
  let candidate := shiftInBit b (x :: remainder)
  let borrow := subBorrowOut candidate divisor false
  have hs := div_shift_pipeline b x dividend divisor remainder quotient
  change (stepO^[2 * (x :: remainder).length + 4]) _ = _ at hs
  change _ = some (divPhaseCfg .subtract b false dividend divisor candidate quotient
    [] [] [] []) at hs
  have hcandidate : candidate.length = divisor.length := by
    simp [candidate, hlen]
  have hd := div_subtract_pipeline b dividend divisor candidate quotient hcandidate
  change (stepO^[4 * candidate.length + 6]) _ = _ at hd
  have chain {m n : ℕ} {a c d : Option divMachine.Cfg}
      (h₁ : (stepO^[m]) a = c) (h₂ : (stepO^[n]) c = d) :
      (stepO^[n + m]) a = d := by
    rw [Function.iterate_add_apply, h₁, h₂]
  have h := chain hs hd
  have htime :
      4 * candidate.length + 6 + (2 * (x :: remainder).length + 4) =
        6 * (x :: remainder).length + 10 := by
    simp [candidate]
    omega
  rw [htime] at h
  simpa [stepO, candidate, borrow] using h

theorem div_round_fixed (w d : ℕ) (s : DivisionScan) (b : Bool)
    (bits : List Bool)
    (hd : d < 2 ^ w) (hr : s.remainder < d) :
    let s' := divisionScanStep d s b
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
      6 * (w + 1) + 10])
      (some (divCleanCfg .outer true (b :: bits) (fixedBits (w + 1) d)
        (fixedBits (w + 1) s.remainder) s.quotient [])) =
      some (divCleanCfg .outer true bits (fixedBits (w + 1) d)
        (fixedBits (w + 1) s'.remainder) s'.quotient []) := by
  let candidate := 2 * s.remainder + b.toNat
  have hc : candidate < 2 ^ (w + 1) :=
    divisionScan_candidate_lt_extra_bit b hd hr
  have hdextra : d < 2 ^ (w + 1) := by
    rw [pow_succ]
    omega
  have hround := div_round b s.remainder.bodd bits (fixedBits (w + 1) d)
    (fixedBits w s.remainder.div2) s.quotient (by simp)
  dsimp only at hround
  simp only [fixedBits_length, List.length_cons] at hround
  change ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
      6 * (w + 1) + 10])
      (some (divCleanCfg .outer true (b :: bits) (fixedBits (w + 1) d)
        (fixedBits (w + 1) s.remainder) s.quotient [])) = _ at hround
  rw [show s.remainder.bodd :: fixedBits w s.remainder.div2 =
    fixedBits (w + 1) s.remainder by rfl] at hround
  rw [shiftInBit_fixed] at hround
  change _ = some (divCleanCfg .outer true bits (fixedBits (w + 1) d)
    (if subBorrowOut (fixedBits (w + 1) candidate) (fixedBits (w + 1) d) false
      then fixedBits (w + 1) candidate
      else subBits (fixedBits (w + 1) candidate) (fixedBits (w + 1) d) false)
    ((!subBorrowOut (fixedBits (w + 1) candidate) (fixedBits (w + 1) d) false) ::
      s.quotient) []) at hround
  rw [subBorrowOut_fixed_eq_decide_lt (w + 1) candidate d hc hdextra] at hround
  by_cases hle : d ≤ candidate
  · have hnlt : ¬ candidate < d := by omega
    have hsub := fixedBits_sub_of_le (w + 1) hle
    simp [divisionScanStep, candidate, hle, hnlt, hsub] at hround ⊢
    exact hround
  · have hlt : candidate < d := by omega
    simp [divisionScanStep, candidate, hle, hlt] at hround ⊢
    exact hround

theorem div_rounds_fixed (w d : ℕ) (bits : List Bool) (s : DivisionScan)
    (hd0 : 0 < d) (hd : d < 2 ^ w) (hr : s.remainder < d) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
      bits.length * (6 * (w + 1) + 10)])
      (some (divCleanCfg .outer true bits (fixedBits (w + 1) d)
        (fixedBits (w + 1) s.remainder) s.quotient [])) =
      some (divCleanCfg .outer true [] (fixedBits (w + 1) d)
        (fixedBits (w + 1) (divisionScan d s bits).remainder)
        (divisionScan d s bits).quotient []) := by
  induction bits generalizing s with
  | nil => simp [divisionScan]
  | cons b bits ih =>
      let s' := divisionScanStep d s b
      have hr' : s'.remainder < d :=
        (divisionScanStep_invariant hd0 s b hr).2
      have hround := div_round_fixed w d s b bits hd hr
      have htail := ih s' hr'
      have hchain :
          ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
            bits.length * (6 * (w + 1) + 10) + (6 * (w + 1) + 10)])
            (some (divCleanCfg .outer true (b :: bits) (fixedBits (w + 1) d)
              (fixedBits (w + 1) s.remainder) s.quotient [])) =
            some (divCleanCfg .outer true [] (fixedBits (w + 1) d)
              (fixedBits (w + 1) (divisionScan d s' bits).remainder)
              (divisionScan d s' bits).quotient []) := by
        rw [Function.iterate_add_apply, hround, htail]
      simpa [divisionScan, s', List.length_cons, Nat.add_mul, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hchain

/-- Exact intended cost of the zero-divisor execution on `w` dividend bits.
The divisor and remainder have the required extra bit. -/
def divZeroRunTime (w : ℕ) : ℕ := 2 * (w + 1) + 3 + (w + 1)

/-- Exact intended cost of a nonzero restoring-division execution.  Every
one of the `w` rounds scans only `w+1`-bit work words. -/
def divPositiveRunTime (w : ℕ) : ℕ :=
  2 * (w + 1) + 3 + w * (6 * (w + 1) + 10) + 1

/-- A single quadratic bound covering both branches. -/
def divRunTimeBound (w : ℕ) : ℕ :=
  (w + 1) * (6 * (w + 1) + 14) + 5

theorem divZeroRunTime_le_bound (w : ℕ) :
    divZeroRunTime w ≤ divRunTimeBound w := by
  simp [divZeroRunTime, divRunTimeBound]
  nlinarith

theorem divPositiveRunTime_le_bound (w : ℕ) :
    divPositiveRunTime w ≤ divRunTimeBound w := by
  simp [divPositiveRunTime, divRunTimeBound]
  nlinarith

theorem divMachine_zero_correct (w a : ℕ) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[divZeroRunTime w])
        (some (divInitialCfg (fixedBits w a).reverse (fixedBits (w + 1) 0)
          (fixedBits (w + 1) 0))) =
      some (divDoneCfg false (fixedBits (w + 1) 0) (fixedBits (w + 1) 0)
        (fixedBits w 0)) := by
  let stepO := fun o : Option divMachine.Cfg => o.bind divMachine.step
  have chain {m n : ℕ} {x y z : Option divMachine.Cfg}
      (h₁ : (stepO^[m]) x = y) (h₂ : (stepO^[n]) y = z) :
      (stepO^[n + m]) x = z := by
    rw [Function.iterate_add_apply, h₁, h₂]
  let dividend := (fixedBits w a).reverse
  let divisor := fixedBits (w + 1) 0
  let remainder := fixedBits (w + 1) 0
  have hfalse : containsTrue divisor = false := by
    simp [divisor, fixedBits_zero]
    induction w with
    | zero => decide
    | succ w ih => simpa [List.replicate_succ, containsTrue] using ih
  have hi := div_inspect_iterate false dividend divisor remainder []
  simp only [Bool.false_or, hfalse, List.append_nil] at hi
  have hi0 : (stepO^[1])
      (some (divCleanCfg .inspectDivisor false dividend [] remainder []
        divisor.reverse)) =
      some (divCleanCfg .restoreInspectedDivisor false dividend [] remainder []
        divisor.reverse) := by
    simpa [stepO] using
      div_step_inspect_nil false dividend remainder divisor.reverse
  have hr := div_restore_inspected_iterate false dividend [] remainder [] divisor.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  have hr0 : (stepO^[1])
      (some (divCleanCfg .restoreInspectedDivisor false dividend divisor remainder [] [])) =
      some (divCleanCfg .dispatch false dividend divisor remainder [] []) := by
    simpa [stepO] using
      div_step_restore_inspected_nil false dividend divisor remainder ([] : List Bool)
  have hd : (stepO^[1])
      (some (divCleanCfg .dispatch false dividend divisor remainder [] [])) =
      some (divCleanCfg .zeroLoop false dividend divisor remainder [] []) := by
    simpa [stepO] using div_step_dispatch_false dividend divisor remainder []
  have hz := div_zero_iterate dividend divisor remainder []
  simp only [List.append_nil] at hz
  have hz0 : (stepO^[1])
      (some (divCleanCfg .zeroLoop false [] divisor remainder
        (dividend.map fun _ => false).reverse [])) =
      some (divDoneCfg false divisor remainder
        (dividend.map fun _ => false).reverse) := by
    simpa [stepO] using div_step_zero_nil divisor remainder
      (dividend.map fun _ => false).reverse
  have h := chain (chain (chain (chain (chain (chain hi hi0) hr) hr0) hd) hz) hz0
  have htime :
      1 + (dividend.length + (1 + (1 + (divisor.length +
        (1 + divisor.length))))) = divZeroRunTime w := by
    simp [dividend, divisor, divZeroRunTime]
    omega
  rw [htime] at h
  have hquot : (dividend.map fun _ => false).reverse = fixedBits w 0 := by
    simp [dividend, fixedBits_zero]
  simpa [stepO, divInitialCfg, divCleanCfg, dividend, divisor, remainder, hquot] using h

theorem divMachine_positive_correct (w a d : ℕ)
    (ha : a < 2 ^ w) (hd0 : 0 < d) (hd : d < 2 ^ w) :
    ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[
      divPositiveRunTime w])
      (some (divInitialCfg (fixedBits w a).reverse (fixedBits (w + 1) d)
        (fixedBits (w + 1) 0))) =
      some (divDoneCfg true (fixedBits (w + 1) d) (fixedBits (w + 1) (a % d))
        (fixedBits w (a / d))) := by
  let stepO := fun o : Option divMachine.Cfg => o.bind divMachine.step
  have chain {m n : ℕ} {x y z : Option divMachine.Cfg}
      (h₁ : (stepO^[m]) x = y) (h₂ : (stepO^[n]) y = z) :
      (stepO^[n + m]) x = z := by
    rw [Function.iterate_add_apply, h₁, h₂]
  let dividend := (fixedBits w a).reverse
  let divisor := fixedBits (w + 1) d
  let remainder := fixedBits (w + 1) 0
  let initialScan : DivisionScan := ⟨[], 0⟩
  let finalScan := divisionScan d initialScan dividend
  have hdextra : d < 2 ^ (w + 1) := by
    rw [pow_succ]
    omega
  have htrue : containsTrue divisor = true := by
    cases hc : containsTrue divisor with
    | false =>
        have hz := containsTrue_false_bitsValue_zero hc
        rw [bitsValue_fixedBits_of_lt hdextra] at hz
        omega
    | true => rfl
  have hi := div_inspect_iterate false dividend divisor remainder []
  simp only [Bool.false_or, htrue, List.append_nil] at hi
  have hi0 : (stepO^[1])
      (some (divCleanCfg .inspectDivisor true dividend [] remainder [] divisor.reverse)) =
      some (divCleanCfg .restoreInspectedDivisor true dividend [] remainder []
        divisor.reverse) := by
    simpa [stepO] using div_step_inspect_nil true dividend remainder divisor.reverse
  have hr := div_restore_inspected_iterate true dividend [] remainder [] divisor.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  have hr0 : (stepO^[1])
      (some (divCleanCfg .restoreInspectedDivisor true dividend divisor remainder [] [])) =
      some (divCleanCfg .dispatch true dividend divisor remainder [] []) := by
    simpa [stepO] using
      div_step_restore_inspected_nil true dividend divisor remainder ([] : List Bool)
  have hdsp : (stepO^[1])
      (some (divCleanCfg .dispatch true dividend divisor remainder [] [])) =
      some (divCleanCfg .outer true dividend divisor remainder [] []) := by
    simpa [stepO] using div_step_dispatch_true dividend divisor remainder []
  have hlo := div_rounds_fixed w d dividend initialScan hd0 hd hd0
  change (stepO^[dividend.length * (6 * (w + 1) + 10)])
      (some (divCleanCfg .outer true dividend divisor remainder [] [])) =
      some (divCleanCfg .outer true [] divisor
        (fixedBits (w + 1) finalScan.remainder) finalScan.quotient []) at hlo
  have hdone : (stepO^[1])
      (some (divCleanCfg .outer true [] divisor
        (fixedBits (w + 1) finalScan.remainder) finalScan.quotient [])) =
      some (divDoneCfg true divisor (fixedBits (w + 1) finalScan.remainder)
        finalScan.quotient) := by
    simpa [stepO] using div_step_outer_nil divisor
      (fixedBits (w + 1) finalScan.remainder) finalScan.quotient
  have h := chain (chain (chain (chain (chain (chain hi hi0) hr) hr0) hdsp) hlo) hdone
  have htime :
      1 + (dividend.length * (6 * (w + 1) + 10) +
        (1 + (1 + (divisor.length + (1 + divisor.length))))) =
        divPositiveRunTime w := by
    simp [dividend, divisor, divPositiveRunTime]
    omega
  rw [htime] at h
  have hscan := divisionScan_fixed_correct w a d ha hd0
  change bitsValue finalScan.quotient = a / d ∧ finalScan.remainder = a % d at hscan
  have hlen : finalScan.quotient.length = w := by
    dsimp [finalScan, initialScan, dividend]
    rw [divisionScan_quotient_length]
    simp
  have hquot : finalScan.quotient = fixedBits w (a / d) := by
    calc
      finalScan.quotient = fixedBits finalScan.quotient.length
          (bitsValue finalScan.quotient) := (fixedBits_bitsValue _).symm
      _ = fixedBits w (a / d) := by rw [hlen, hscan.1]
  rw [hscan.2, hquot] at h
  simpa [stepO, divInitialCfg, divCleanCfg, dividend, divisor, remainder] using h

end Lax51Proofs.RamToTM
