import Lax51Proofs.RamToTM.DivideMacro

namespace Lax51Proofs.RamToTM

open Turing TM2

inductive CountdownStack | count | temp
  deriving DecidableEq, Fintype, Inhabited

inductive CountdownLabel | scan | restore | zero | positive
  deriving DecidableEq, Fintype, Inhabited

structure CountdownControl where
  held : Option Bool := none
  borrow : Bool := true
  positiveSeen : Bool := false
  deriving DecidableEq, Fintype

instance : Inhabited CountdownControl :=
  ⟨{ held := none, borrow := true, positiveSeen := false }⟩

def countdownOutput (s : CountdownControl) : Bool :=
  (fullSubtractor (s.held.getD false) false s.borrow).1

def countdownAdvance (s : CountdownControl) : CountdownControl :=
  let bit := s.held.getD false
  { held := none
    borrow := (fullSubtractor bit false s.borrow).2
    positiveSeen := s.positiveSeen || bit }

def countdownClearHeld (s : CountdownControl) : CountdownControl :=
  { s with held := none }

def countdownMachine : Turing.FinTM2 where
  K := CountdownStack
  k₀ := .count
  k₁ := .temp
  Γ _ := Bool
  Λ := CountdownLabel
  main := .scan
  σ := CountdownControl
  initialState := default
  m
    | .scan =>
        .pop .count (fun s a => { s with held := a }) <|
        .branch (fun s => s.held.isNone)
          (.branch (fun s => s.positiveSeen)
            (.goto fun _ => .restore) (.goto fun _ => .zero))
          (.push .temp countdownOutput <|
            .load countdownAdvance <| .goto fun _ => .scan)
    | .restore =>
        .pop .temp (fun s a => { s with held := a }) <|
        .branch (fun s => s.held.isNone)
          (.goto fun _ => .positive)
          (.push .count (fun s => s.held.getD false) <|
            .load countdownClearHeld <| .goto fun _ => .restore)
    | .zero | .positive => .halt

def countdownStacks (count temp : List Bool) : CountdownStack -> List Bool
  | .count => count
  | .temp => temp

def countdownCfg (label : CountdownLabel) (state : CountdownControl)
    (count temp : List Bool) : countdownMachine.Cfg where
  l := some label
  var := state
  stk := countdownStacks count temp

def countdownBits : Bool -> List Bool -> List Bool
  | _, [] => []
  | borrow, bit :: bits =>
      let r := fullSubtractor bit false borrow
      r.1 :: countdownBits r.2 bits

@[simp] theorem countdownBits_length (borrow : Bool) (bits : List Bool) :
    (countdownBits borrow bits).length = bits.length := by
  induction bits generalizing borrow with
  | nil => rfl
  | cons bit bits ih => simp [countdownBits, ih]

theorem countdownBits_eq_subBits_zero (borrow : Bool) (bits : List Bool) :
    countdownBits borrow bits =
      subBits bits (List.replicate bits.length false) borrow := by
  induction bits generalizing borrow with
  | nil => rfl
  | cons bit bits ih =>
      simp [countdownBits, subBits, ih, List.replicate_succ]

@[simp] theorem countdown_step_scan_cons (state : CountdownControl)
    (bit : Bool) (bits temp : List Bool) :
    countdownMachine.step (countdownCfg .scan state (bit :: bits) temp) =
      some (countdownCfg .scan
        { held := none
          borrow := (fullSubtractor bit false state.borrow).2
          positiveSeen := state.positiveSeen || bit }
        bits ((fullSubtractor bit false state.borrow).1 :: temp)) := by
  rcases state with ⟨held, borrow, positiveSeen⟩
  cases bit <;> cases borrow <;>
    simp [countdownMachine, countdownCfg, countdownStacks,
      countdownOutput, countdownAdvance, fullSubtractor, Function.update]
  all_goals
    congr 2
    funext k
    cases k <;> rfl

@[simp] theorem countdown_step_scan_nil (state : CountdownControl)
    (temp : List Bool) :
    countdownMachine.step (countdownCfg .scan state [] temp) =
      some (countdownCfg
        (if state.positiveSeen then .restore else .zero)
        { state with held := none } [] temp) := by
  cases h : state.positiveSeen <;>
    simp [countdownMachine, countdownCfg, countdownStacks, h]
  all_goals
    congr 2
    funext k
    cases k <;> rfl

theorem countdown_scan_iterate (state : CountdownControl)
    (bits temp : List Bool) (hheld : state.held = none) :
    ((fun x : Option countdownMachine.Cfg =>
      x.bind countdownMachine.step)^[bits.length])
      (some (countdownCfg .scan state bits temp)) =
    some (countdownCfg .scan
      { held := none
        borrow := (subBorrowOut bits
          (List.replicate bits.length false) state.borrow)
        positiveSeen := state.positiveSeen || containsTrue bits }
      [] ((countdownBits state.borrow bits).reverse ++ temp)) := by
  induction bits generalizing state temp with
  | nil =>
      cases state
      simp_all [countdownBits, subBorrowOut, containsTrue]
  | cons bit bits ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, countdown_step_scan_cons]
      rw [ih _ _ rfl]
      cases bit <;> cases state.borrow <;>
        simp [countdownBits, subBorrowOut, containsTrue, List.replicate_succ,
          List.reverse_cons,
          List.append_assoc, fullSubtractor, Bool.or_assoc]

@[simp] theorem countdown_step_restore_cons (state : CountdownControl)
    (count : List Bool) (bit : Bool) (bits : List Bool) :
    countdownMachine.step
      (countdownCfg .restore state count (bit :: bits)) =
    some (countdownCfg .restore { state with held := none }
      (bit :: count) bits) := by
  cases bit <;>
    simp [countdownMachine, countdownCfg, countdownStacks,
      countdownClearHeld, Function.update]
  all_goals
    congr 2
    funext k
    cases k <;> rfl

@[simp] theorem countdown_step_restore_nil (state : CountdownControl)
    (count : List Bool) :
    countdownMachine.step (countdownCfg .restore state count []) =
      some (countdownCfg .positive { state with held := none } count []) := by
  simp [countdownMachine, countdownCfg, countdownStacks]
  congr 2
  funext k
  cases k <;> rfl

theorem countdown_restore_iterate (state : CountdownControl)
    (count temp : List Bool) (hheld : state.held = none) :
    ((fun x : Option countdownMachine.Cfg =>
      x.bind countdownMachine.step)^[temp.length])
      (some (countdownCfg .restore state count temp)) =
    some (countdownCfg .restore { state with held := none }
      (temp.reverse ++ count) []) := by
  induction temp generalizing state count with
  | nil =>
      cases state
      simp_all
  | cons bit bits ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, countdown_step_restore_cons]
      rw [ih _ _ rfl]
      simp [List.reverse_cons, List.append_assoc]

@[simp] theorem countdownBits_zero_word (w : Nat) :
    countdownBits true (List.replicate w false) = List.replicate w true := by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ, countdownBits, fullSubtractor, ih]

@[simp] theorem subBorrowOut_zero_word (w : Nat) :
    subBorrowOut (List.replicate w false) (List.replicate w false) true = true := by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ, subBorrowOut, fullSubtractor, ih]

@[simp] theorem containsTrue_zero_word (w : Nat) :
    containsTrue (List.replicate w false) = false := by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ, containsTrue, ih]

theorem countdownMachine_zero_correct (w : Nat) :
    ((fun x : Option countdownMachine.Cfg =>
      x.bind countdownMachine.step)^[w + 1])
      (some (countdownCfg .scan default (fixedBits w 0) [])) =
    some (countdownCfg .zero
      { held := none, borrow := true, positiveSeen := false }
      [] (List.replicate w true)) := by
  have hscan := countdown_scan_iterate default (fixedBits w 0) [] rfl
  simp only [fixedBits_length] at hscan
  simp only [show (default : CountdownControl).borrow = true by rfl,
    show (default : CountdownControl).positiveSeen = false by rfl,
    Bool.false_or] at hscan
  have hstep := countdown_step_scan_nil
    ({ held := none, borrow := true, positiveSeen := false } : CountdownControl)
    (List.replicate w true)
  rw [Nat.add_comm, Function.iterate_add_apply]
  have hscan' :
      ((fun x : Option countdownMachine.Cfg =>
        x.bind countdownMachine.step)^[w])
        (some (countdownCfg .scan default (fixedBits w 0) [])) =
      some (countdownCfg .scan
        { held := none, borrow := true, positiveSeen := false }
        [] (List.replicate w true)) := by
    simpa [fixedBits_zero] using hscan
  rw [hscan']
  simpa using hstep

theorem countdownMachine_positive_correct (w d : Nat)
    (hd0 : 0 < d) (hd : d < 2 ^ w) :
    ∃ finalState,
      ((fun x : Option countdownMachine.Cfg =>
        x.bind countdownMachine.step)^[2 * w + 2])
        (some (countdownCfg .scan default (fixedBits w d) [])) =
      some (countdownCfg .positive finalState (fixedBits w (d - 1)) []) := by
  have htrue : containsTrue (fixedBits w d) = true := by
    cases h : containsTrue (fixedBits w d) with
    | true => rfl
    | false =>
        have hz := containsTrue_false_bitsValue_zero h
        rw [bitsValue_fixedBits_of_lt hd] at hz
        omega
  have hscan := countdown_scan_iterate default (fixedBits w d) [] rfl
  simp only [List.append_nil, htrue, Bool.false_or, List.length_replicate,
    fixedBits_length,
    show (default : CountdownControl).borrow = true by rfl,
    show (default : CountdownControl).positiveSeen = false by rfl] at hscan
  let scanState : CountdownControl :=
    { held := none
      borrow := subBorrowOut (fixedBits w d) (List.replicate w false) true
      positiveSeen := true }
  have htoRestore := countdown_step_scan_nil scanState
    (countdownBits true (fixedBits w d)).reverse
  have hrestore := countdown_restore_iterate { scanState with held := none } []
    (countdownBits true (fixedBits w d)).reverse rfl
  simp only [List.length_reverse, countdownBits_length,
    fixedBits_length, List.reverse_reverse, List.append_nil] at hrestore
  have hdone := countdown_step_restore_nil
    { scanState with held := none }
    (countdownBits true (fixedBits w d))
  let stepO := fun x : Option countdownMachine.Cfg =>
    x.bind countdownMachine.step
  have hchain {m n : Nat} {a b c : Option countdownMachine.Cfg}
      (h₁ : (stepO^[m]) a = b) (h₂ : (stepO^[n]) b = c) :
      (stepO^[m + n]) a = c := by
    rw [Nat.add_comm, Function.iterate_add_apply, h₁, h₂]
  have hall := hchain (hchain (hchain hscan
    (show (stepO^[1]) _ = _ by simpa [stepO, scanState] using htoRestore))
    hrestore) (show (stepO^[1]) _ = _ by simpa [stepO] using hdone)
  have hbits : countdownBits true (fixedBits w d) = fixedBits w (d - 1) := by
    rw [countdownBits_eq_subBits_zero]
    simp only [fixedBits_length]
    rw [← fixedBits_zero w]
    rw [← fixedBits_sub_borrow w d 0 true
      (show 0 + true.toNat ≤ d by simpa using hd0)]
    simp
  refine ⟨{ scanState with held := none }, ?_⟩
  have ht : w + 1 + w + 1 = 2 * w + 2 := by omega
  rw [ht] at hall
  simpa [hbits] using hall

end Lax51Proofs.RamToTM
