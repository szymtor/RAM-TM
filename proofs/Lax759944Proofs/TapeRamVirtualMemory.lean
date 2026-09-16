import Lax808846.Ram
import Mathlib.Data.Nat.Basic

namespace Lax759944Proofs.TapeRamVirtualMemory

open Lax808846.Ram

/-- A virtual RAM owns even physical addresses; an input adapter owns odd
addresses. At physical width `v+1`, all `v`-bit virtual addresses fit. -/
def merge (memory scratch : Nat → Nat) (address : Nat) : Nat :=
  if address % 2 = 0 then memory (address / 2) else scratch (address / 2)

theorem merge_even (memory scratch : Nat → Nat) (a : Nat) :
    merge memory scratch (2 * a) = memory a := by
  simp [merge, Nat.mul_div_right]

theorem merge_odd (memory scratch : Nat → Nat) (a : Nat) :
    merge memory scratch (2 * a + 1) = scratch a := by
  simp [merge, Nat.add_div, Nat.mul_div_right]

theorem even_address_lt (v a : Nat) : 2 * (a % 2 ^ v) < 2 ^ (v + 1) := by
  have := Nat.mod_lt a (Nat.two_pow_pos v)
  rw [Nat.pow_succ]
  omega

theorem odd_address_lt (v a : Nat) : 2 * (a % 2 ^ v) + 1 < 2 ^ (v + 1) := by
  have := Nat.mod_lt a (Nat.two_pow_pos v)
  rw [Nat.pow_succ]
  omega

/-- Reducing to the physical word and then to the virtual word agrees
with reducing to the virtual word directly. This is needed after arithmetic. -/
theorem mod_physical_virtual (v value : Nat) :
    value % 2 ^ (v + 1) % 2 ^ v = value % 2 ^ v := by
  apply Nat.mod_mod_of_dvd
  exact ⟨2, Nat.pow_succ 2 v⟩

/-- A write to an even address, with virtual-word truncation, updates
exactly the simulated cell. There is no unused-cell assumption on memory. -/
theorem set_virtual (v : Nat) (memory scratch : Nat → Nat) (a value : Nat) :
    setCell (v + 1) (merge memory scratch) (2 * (a % 2 ^ v)) (value % 2 ^ v) =
      merge (setCell v memory a value) scratch := by
  funext address
  have hvalue : value % 2 ^ v < 2 ^ (v + 1) :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos v))
      (Nat.pow_le_pow_right (by decide) (by omega))
  simp only [setCell, Nat.mod_eq_of_lt (even_address_lt v a),
    Nat.mod_eq_of_lt hvalue, merge]
  by_cases heven : address % 2 = 0
  · simp only [heven, ↓reduceIte]
    have heq : address = 2 * (a % 2 ^ v) ↔ address / 2 = a % 2 ^ v := by omega
    simp only [heq]
  · have hne : address ≠ 2 * (a % 2 ^ v) := by omega
    simp [heven, hne]

/-- Adapter writes never change the simulated memory. Odd cells may hold
full physical words, even though simulated data uses one fewer bit. -/
theorem set_scratch (v : Nat) (memory scratch : Nat → Nat) (a value : Nat) :
    setCell (v + 1) (merge memory scratch) (2 * (a % 2 ^ v) + 1) value =
      merge memory
        (fun b => if b = a % 2 ^ v then value % 2 ^ (v + 1) else scratch b) := by
  funext address
  simp only [setCell, Nat.mod_eq_of_lt (odd_address_lt v a), merge]
  by_cases heven : address % 2 = 0
  · have hne : address ≠ 2 * (a % 2 ^ v) + 1 := by omega
    simp [heven, hne]
  · simp only [heven, ↓reduceIte]
    have heq : address = 2 * (a % 2 ^ v) + 1 ↔ address / 2 = a % 2 ^ v := by omega
    simp only [heq]

end Lax759944Proofs.TapeRamVirtualMemory
