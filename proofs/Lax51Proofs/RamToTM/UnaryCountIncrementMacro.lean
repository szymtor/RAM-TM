import Lax51Proofs.RamToTM.IncrementWordMacro

namespace Lax51Proofs.RamToTM

open Turing TM2

inductive CountIncrementStack | count | word | temp
  deriving DecidableEq, Fintype, Inhabited

inductive CountIncrementOuterLabel | loop | done
  deriving DecidableEq, Fintype, Inhabited

abbrev CountIncrementLabel := Sum IncrementLabel CountIncrementOuterLabel

def incrementCountRenaming : StackRenaming IncrementStack CountIncrementStack where
  encode
    | .word => .word
    | .temp => .temp
  decode
    | .word => some .word
    | .temp => some .temp
    | .count => none
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;> simp_all

def incrementControlLens : StateLens IncrementControl IncrementControl where
  get := id
  put := fun _ inner => inner
  get_put := by intros; rfl
  put_get := by intros; rfl
  put_put := by intros; rfl

def countIncrementOuterProgram : CountIncrementOuterLabel →
    TM2.Stmt (fun _ : CountIncrementStack => SparseSymbol)
      CountIncrementLabel IncrementControl
  | .loop =>
      .pop .count (fun s a => {s with held := a}) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .inr .done)
        (.load (fun _ => default) <| .goto fun _ => .inl .scan)
  | .done => .halt

def countIncrementProgram : CountIncrementLabel →
    TM2.Stmt (fun _ : CountIncrementStack => SparseSymbol)
      CountIncrementLabel IncrementControl :=
  lensSpliceProgram incrementCountRenaming incrementControlLens
    incrementProgram .done CountIncrementOuterLabel.loop
    countIncrementOuterProgram

def countIncrementStacks (count word temp : List SparseSymbol) :
    CountIncrementStack → List SparseSymbol
  | .count => count
  | .word => word
  | .temp => temp

def countIncrementCfg (label : CountIncrementLabel)
    (count word temp : List SparseSymbol) :
    TM2.Cfg (fun _ : CountIncrementStack => SparseSymbol)
      CountIncrementLabel IncrementControl :=
  ⟨some label, default, countIncrementStacks count word temp⟩

def countIncrementCfgState (label : CountIncrementLabel) (control : IncrementControl)
    (count word temp : List SparseSymbol) :
    TM2.Cfg (fun _ : CountIncrementStack => SparseSymbol)
      CountIncrementLabel IncrementControl :=
  ⟨some label, control, countIncrementStacks count word temp⟩

@[simp] theorem countIncrement_outer_cons_from (control : IncrementControl)
    (count word : List SparseSymbol) :
    TM2.step countIncrementProgram
      (countIncrementCfgState (.inr .loop) control (.wordEnd :: count) word []) =
    some (countIncrementCfg (.inl .scan) count word []) := by
  simp [countIncrementProgram, lensSpliceProgram, countIncrementOuterProgram,
    countIncrementCfgState, countIncrementCfg, countIncrementStacks, TM2.step]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem countIncrement_outer_nil_from (control : IncrementControl)
    (word : List SparseSymbol) :
    TM2.step countIncrementProgram
      (countIncrementCfgState (.inr .loop) control [] word []) =
    some (countIncrementCfg (.inr .done) [] word []) := by
  simp [countIncrementProgram, lensSpliceProgram, countIncrementOuterProgram,
    countIncrementCfgState, countIncrementCfg, countIncrementStacks, TM2.step]

@[simp] theorem countIncrement_outer_cons (count word : List SparseSymbol) :
    TM2.step countIncrementProgram
      (countIncrementCfg (.inr .loop) (.wordEnd :: count) word []) =
    some (countIncrementCfg (.inl .scan) count word []) := by
  simp [countIncrementProgram, lensSpliceProgram, countIncrementOuterProgram,
    countIncrementCfg, countIncrementStacks, TM2.step]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem countIncrement_outer_nil (word : List SparseSymbol) :
    TM2.step countIncrementProgram
      (countIncrementCfg (.inr .loop) [] word []) =
    some (countIncrementCfg (.inr .done) [] word []) := by
  simp [countIncrementProgram, lensSpliceProgram, countIncrementOuterProgram,
    countIncrementCfg, countIncrementStacks, TM2.step]

theorem countIncrement_one {count : List SparseSymbol} (w n : Nat) :
    ((fun o => o.bind (TM2.step countIncrementProgram))^[2 * w + 4])
      (some (countIncrementCfg (.inr .loop) (.wordEnd :: count)
        ((fixedBits w n).map SparseSymbol.bit) [])) =
    some (countIncrementCfg (.inr .loop) count
      ((fixedBits w (n + 1)).map SparseSymbol.bit) []) := by
  have houter :
      ((fun o => o.bind (TM2.step countIncrementProgram))^[1])
        (some (countIncrementCfg (.inr .loop) (.wordEnd :: count)
          ((fixedBits w n).map SparseSymbol.bit) [])) =
      some (countIncrementCfg (.inl .scan) count
        ((fixedBits w n).map SparseSymbol.bit) []) := by
    simpa using countIncrement_outer_cons count
      ((fixedBits w n).map SparseSymbol.bit)
  have hlocal := transport_lensHaltingMacro_and_return
    incrementCountRenaming incrementControlLens incrementProgram .done (by rfl)
    CountIncrementOuterLabel.loop countIncrementOuterProgram
    (increment_fixed_correct w n) rfl default
    (countIncrementStacks count [] [])
  have hlocal' :
      ((fun o => o.bind (TM2.step countIncrementProgram))^[2 * w + 3])
        (some (countIncrementCfg (.inl .scan) count
          ((fixedBits w n).map SparseSymbol.bit) [])) =
      some (countIncrementCfg (.inr .loop) count
        ((fixedBits w (n + 1)).map SparseSymbol.bit) []) := by
    convert hlocal using 1
    case h.e'_2 =>
      unfold countIncrementProgram
      rw [show 2 * w + 3 = 2 * w + 2 + 1 by omega]
      congr 2
      simp [countIncrementCfg, lensRenamedCfg, incrementCfg,
        incrementStacks, renamedStacks, incrementCountRenaming,
        incrementControlLens, countIncrementStacks]
      constructor
      · change (default : IncrementControl) = ⟨true, none⟩
        rfl
      · funext k
        cases k <;> rfl
    case h.e'_3 =>
      congr 1
      simp [countIncrementCfg, lensReturnCfg, incrementCfg,
        incrementStacks, renamedStacks, incrementCountRenaming,
        incrementControlLens, countIncrementStacks]
      constructor
      · change (default : IncrementControl) = ⟨true, none⟩
        rfl
      · funext k
        cases k <;> rfl
  have h := chain_iterations _ houter hlocal'
  rw [show 1 + (2 * w + 3) = 2 * w + 4 by omega] at h
  exact h

theorem countIncrement_iterate (count w n : Nat) :
    ((fun o => o.bind (TM2.step countIncrementProgram))^[count * (2 * w + 4)])
      (some (countIncrementCfg (.inr .loop) (unaryMarkers count)
        ((fixedBits w n).map SparseSymbol.bit) [])) =
    some (countIncrementCfg (.inr .loop) []
      ((fixedBits w (n + count)).map SparseSymbol.bit) []) := by
  induction count generalizing n with
  | zero => simp [unaryMarkers]
  | succ count ih =>
      rw [Nat.add_mul count 1 (2 * w + 4), one_mul,
        Nat.add_comm (count * (2 * w + 4)) (2 * w + 4)]
      have hone := countIncrement_one (count := unaryMarkers count) w n
      have h := chain_iterations _ hone (ih (n + 1))
      simpa only [unaryMarkers, List.replicate_succ, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using h

theorem countIncrement_correct (count w : Nat) :
    ((fun o => o.bind (TM2.step countIncrementProgram))^[
        count * (2 * w + 4) + 1])
      (some (countIncrementCfg (.inr .loop) (unaryMarkers count)
        ((fixedBits w 0).map SparseSymbol.bit) [])) =
    some (countIncrementCfg (.inr .done) []
      ((fixedBits w count).map SparseSymbol.bit) []) := by
  rw [Nat.add_comm, Function.iterate_add_apply, countIncrement_iterate]
  simp only [zero_add, Function.iterate_one, Option.bind_some,
    countIncrement_outer_nil]

theorem countIncrement_correct_from (control : IncrementControl)
    (count w : Nat) :
    ((fun o => o.bind (TM2.step countIncrementProgram))^[
        count * (2 * w + 4) + 1])
      (some (countIncrementCfgState (.inr .loop) control (unaryMarkers count)
        ((fixedBits w 0).map SparseSymbol.bit) [])) =
    some (countIncrementCfg (.inr .done) []
      ((fixedBits w count).map SparseSymbol.bit) []) := by
  cases count with
  | zero =>
      simpa [unaryMarkers] using countIncrement_outer_nil_from control
        ((fixedBits w 0).map SparseSymbol.bit)
  | succ count =>
      have htail := countIncrement_correct (count + 1) w
      have hcost : (count + 1) * (2 * w + 4) + 1 =
        1 + ((2 * w + 3) + count * (2 * w + 4) + 1) := by
          rw [Nat.add_mul count 1 (2 * w + 4), one_mul]
          omega
      rw [hcost, Function.iterate_add_apply] at htail ⊢
      simp only [Function.iterate_one, Option.bind_some,
        countIncrement_outer_cons_from, countIncrement_outer_cons] at htail ⊢
      simpa [unaryMarkers, List.replicate_succ] using htail

end Lax51Proofs.RamToTM
