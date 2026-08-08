import Lax20Proofs.RamToTM.InputWidthAdapter

namespace Lax20Proofs.RamToTM

open Turing TM2

def incrementBits : Bool → List Bool → List Bool
  | _, [] => []
  | carry, bit :: bits =>
      Bool.xor bit carry :: incrementBits (bit && carry) bits

theorem incrementBits_eq_addBits (carry : Bool) (bits : List Bool) :
    incrementBits carry bits =
      addBits bits (List.replicate bits.length false) carry := by
  induction bits generalizing carry with
  | nil => rfl
  | cons bit bits ih =>
      cases bit <;> cases carry <;>
        simp [incrementBits, addBits, fullAdder, ih, List.replicate_succ]

theorem incrementBits_fixedBits (w n : Nat) :
    incrementBits true (fixedBits w n) = fixedBits w (n + 1) := by
  rw [incrementBits_eq_addBits]
  have hz : List.replicate (fixedBits w n).length false = fixedBits w 0 := by
    simp [fixedBits_zero]
  rw [hz, ← fixedBits_add_carry]
  simp

structure IncrementControl where
  carry : Bool := true
  held : Option SparseSymbol := none
  deriving DecidableEq, Fintype

instance : Inhabited IncrementControl := ⟨⟨true, none⟩⟩

inductive IncrementStack | word | temp
  deriving DecidableEq, Fintype, Inhabited

inductive IncrementLabel | scan | restore | done
  deriving DecidableEq, Fintype, Inhabited

def incrementProgram : IncrementLabel →
    TM2.Stmt (fun _ : IncrementStack => SparseSymbol)
      IncrementLabel IncrementControl
  | .scan =>
      .pop .word (fun s a => {s with held := a}) <|
      .branch (fun s => s.held.isNone)
        (.goto fun _ => .restore) <|
      .push .temp (fun s => .bit
        (Bool.xor (s.held.getD (.bit false)).bitValue s.carry)) <|
      .load (fun s => {s with
        carry := (s.held.getD (.bit false)).bitValue && s.carry,
        held := none}) <|
      .goto fun _ => .scan
  | .restore =>
      .pop .temp (fun s a => {s with held := a}) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .done) <|
      .push .word (fun s => s.held.getD default) <|
      .load (fun s => {s with held := none}) <|
      .goto fun _ => .restore
  | .done => .halt

def incrementStacks (word temp : List SparseSymbol) :
    IncrementStack → List SparseSymbol
  | .word => word
  | .temp => temp

def incrementCfg (label : IncrementLabel) (carry : Bool)
    (word temp : List SparseSymbol) :
    TM2.Cfg (fun _ : IncrementStack => SparseSymbol)
      IncrementLabel IncrementControl :=
  ⟨some label, ⟨carry, none⟩, incrementStacks word temp⟩

theorem increment_scan_step (carry bit : Bool) (bits : List Bool)
    (temp : List SparseSymbol) :
    TM2.step incrementProgram
      (incrementCfg .scan carry (.bit bit :: bits.map SparseSymbol.bit) temp) =
    some (incrementCfg .scan (bit && carry) (bits.map SparseSymbol.bit)
      (.bit (Bool.xor bit carry) :: temp)) := by
  simp [incrementProgram, incrementCfg, incrementStacks, TM2.step,
    Function.update]
  funext k
  cases k <;> rfl

theorem increment_scan_from (carry : Bool) (bits : List Bool)
    (temp : List SparseSymbol) :
    ((fun o => o.bind (TM2.step incrementProgram))^[bits.length + 1])
      (some (incrementCfg .scan carry (bits.map SparseSymbol.bit) temp)) =
    some (incrementCfg .restore
      (addCarryOut bits (List.replicate bits.length false) carry) []
      ((incrementBits carry bits).reverse.map SparseSymbol.bit ++ temp)) := by
  induction bits generalizing carry temp with
  | nil => simp [incrementProgram, incrementCfg, incrementStacks, TM2.step,
      incrementBits, addCarryOut]
  | cons bit bits ih =>
      have hs := increment_scan_step carry bit bits temp
      have hs' : ((fun o => o.bind (TM2.step incrementProgram))^[1])
          (some (incrementCfg .scan carry
            (.bit bit :: bits.map SparseSymbol.bit) temp)) =
          some (incrementCfg .scan (bit && carry)
            (bits.map SparseSymbol.bit)
            (.bit (Bool.xor bit carry) :: temp)) := by simpa using hs
      have hr := ih (bit && carry)
        (.bit (Bool.xor bit carry) :: temp)
      have h := chain_iterations _ hs' hr
      rw [List.length_cons,
        show bits.length + 1 + 1 = 1 + (bits.length + 1) by omega]
      cases bit <;> cases carry <;>
        simpa [incrementBits, addCarryOut, fullAdder,
          List.reverse_cons, List.append_assoc, List.replicate_succ] using h

theorem increment_scan (carry : Bool) (bits : List Bool) :
    ((fun o => o.bind (TM2.step incrementProgram))^[bits.length + 1])
      (some (incrementCfg .scan carry (bits.map SparseSymbol.bit) [])) =
    some (incrementCfg .restore
      (addCarryOut bits (List.replicate bits.length false) carry) []
      ((incrementBits carry bits).reverse.map SparseSymbol.bit)) := by
  simpa using increment_scan_from carry bits []

theorem increment_restore_from (carry : Bool) (source target : List SparseSymbol) :
    ((fun o => o.bind (TM2.step incrementProgram))^[source.length + 1])
      (some (incrementCfg .restore carry target source)) =
    some (incrementCfg .done true (source.reverse ++ target) []) := by
  induction source generalizing carry target with
  | nil =>
      cases carry <;>
        simp [incrementProgram, incrementCfg, incrementStacks, TM2.step]
      all_goals change (default : IncrementControl) = ⟨true, none⟩
      all_goals rfl
  | cons a source ih =>
      have hs : TM2.step incrementProgram
          (incrementCfg .restore carry target (a :: source)) =
          some (incrementCfg .restore carry (a :: target) source) := by
        simp [incrementProgram, incrementCfg, incrementStacks, TM2.step,
          Function.update]
        funext k
        cases k <;> rfl
      have hs' : ((fun o => o.bind (TM2.step incrementProgram))^[1])
          (some (incrementCfg .restore carry target (a :: source))) =
          some (incrementCfg .restore carry (a :: target) source) := by
        simpa using hs
      have h := chain_iterations _ hs' (ih carry (a :: target))
      rw [List.length_cons,
        show source.length + 1 + 1 = 1 + (source.length + 1) by omega]
      simpa [List.reverse_cons, List.append_assoc] using h

theorem increment_restore (carry : Bool) (bits : List Bool) :
    ((fun o => o.bind (TM2.step incrementProgram))^[bits.length + 1])
      (some (incrementCfg .restore carry []
        (bits.reverse.map SparseSymbol.bit))) =
    some (incrementCfg .done true (bits.map SparseSymbol.bit) []) := by
  have h := increment_restore_from carry
    (bits.reverse.map SparseSymbol.bit) []
  simpa [List.map_reverse] using h

theorem increment_correct (carry : Bool) (bits : List Bool) :
    ((fun o => o.bind (TM2.step incrementProgram))^[2 * bits.length + 2])
      (some (incrementCfg .scan carry (bits.map SparseSymbol.bit) [])) =
    some (incrementCfg .done true
      ((incrementBits carry bits).map SparseSymbol.bit) []) := by
  have hs := increment_scan carry bits
  have hr := increment_restore
    (addCarryOut bits (List.replicate bits.length false) carry)
    (incrementBits carry bits)
  have h := chain_iterations _ hs hr
  have hlen : (incrementBits carry bits).length = bits.length := by
    simp [incrementBits_eq_addBits, addBits_length_of_eq]
  rw [hlen] at h
  rw [show (bits.length + 1) + (bits.length + 1) =
    2 * bits.length + 2 by omega] at h
  exact h

theorem increment_fixed_correct (w n : Nat) :
    ((fun o => o.bind (TM2.step incrementProgram))^[2 * w + 2])
      (some (incrementCfg .scan true
        ((fixedBits w n).map SparseSymbol.bit) [])) =
    some (incrementCfg .done true
      ((fixedBits w (n + 1)).map SparseSymbol.bit) []) := by
  simpa [incrementBits_fixedBits] using
    increment_correct true (fixedBits w n)

end Lax20Proofs.RamToTM
