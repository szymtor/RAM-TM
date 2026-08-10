import Lax51Proofs.RamToTM.SparseMemory
import Mathlib.Computability.Partrec

namespace Lax51Proofs.Computability

/-! Computability of the three natural-number bitwise operations used by
the RAM semantics.  The implementation below processes one low bit per
iteration; `a + b` iterations suffice to exhaust both operands. -/

abbrev BitState := (ℕ × ℕ) × (ℕ × ℕ)

def bitStep (op : Bool → Bool → Bool) (s : BitState) : BitState :=
  let a := s.1.1
  let b := s.1.2
  let place := s.2.1
  let result := s.2.2
  ((a.div2, b.div2),
    (2 * place, result + if op a.bodd b.bodd then place else 0))

def bitLoop (op : Bool → Bool → Bool) (fuel : ℕ) (s : BitState) : BitState :=
  (bitStep op)^[fuel] s

def computableBitwise (op : Bool → Bool → Bool) (a b : ℕ) : ℕ :=
  (bitLoop op (a + b) ((a, b), (1, 0))).2.2

theorem bitStep_primrec (op : Bool → Bool → Bool) : Primrec (bitStep op) := by
  have ha : Primrec fun s : BitState => s.1.1 := Primrec.fst.comp Primrec.fst
  have hb : Primrec fun s : BitState => s.1.2 := Primrec.snd.comp Primrec.fst
  have hp : Primrec fun s : BitState => s.2.1 := Primrec.fst.comp Primrec.snd
  have hr : Primrec fun s : BitState => s.2.2 := Primrec.snd.comp Primrec.snd
  have hbit : Primrec fun s : BitState => op s.1.1.bodd s.1.2.bodd :=
    (Primrec.dom_bool₂ op).comp (Primrec.nat_bodd.comp ha) (Primrec.nat_bodd.comp hb)
  have hchoose : Primrec fun s : BitState =>
      if op s.1.1.bodd s.1.2.bodd then s.2.1 else 0 :=
    (Primrec.cond hbit hp (Primrec.const 0)).of_eq fun s => by
      cases op s.1.1.bodd s.1.2.bodd <;> rfl
  have hadd : Primrec fun s : BitState =>
      s.2.2 + if op s.1.1.bodd s.1.2.bodd then s.2.1 else 0 :=
    Primrec.nat_add.comp hr hchoose
  exact Primrec.pair
    (Primrec.pair (Primrec.nat_div2.comp ha) (Primrec.nat_div2.comp hb))
    (Primrec.pair (Primrec.nat_mul.comp (Primrec.const 2) hp) hadd)

theorem computableBitwise_primrec (op : Bool → Bool → Bool) :
    Primrec₂ (computableBitwise op) := by
  have hfuel : Primrec fun p : ℕ × ℕ => p.1 + p.2 :=
    Primrec.nat_add.comp Primrec.fst Primrec.snd
  have hstart : Primrec fun p : ℕ × ℕ => ((p.1, p.2), (1, 0)) :=
    Primrec.pair (Primrec.pair Primrec.fst Primrec.snd)
      (Primrec.pair (Primrec.const 1) (Primrec.const 0))
  have hiterate : Primrec fun p : ℕ × ℕ =>
      (bitStep op)^[p.1 + p.2] ((p.1, p.2), (1, 0)) :=
    Primrec.nat_iterate hfuel hstart
      ((bitStep_primrec op).comp Primrec.snd).to₂
  exact (Primrec.snd.comp (Primrec.snd.comp hiterate)).to₂

theorem div2_add_div2_lt {a b : ℕ} (h : 0 < a + b) :
    a.div2 + b.div2 < a + b := by
  rw [Nat.div2_val, Nat.div2_val]
  omega

theorem bitStep_zero (op : Bool → Bool → Bool)
    (hff : op false false = false) (place result : ℕ) :
    bitStep op ((0, 0), (place, result)) = ((0, 0), (2 * place, result)) := by
  simp [bitStep, hff]

theorem bitLoop_zero_result (op : Bool → Bool → Bool)
    (hff : op false false = false) (fuel place result : ℕ) :
    (bitLoop op fuel ((0, 0), (place, result))).2.2 = result := by
  induction fuel generalizing place with
  | zero => rfl
  | succ fuel ih =>
      rw [bitLoop, Function.iterate_succ_apply]
      simp only [bitStep_zero op hff]
      exact ih (2 * place)

theorem bitLoop_result (op : Bool → Bool → Bool)
    (hff : op false false = false) :
    ∀ fuel a b place result, a + b ≤ fuel →
      (bitLoop op fuel ((a, b), (place, result))).2.2 =
        result + place * Nat.bitwise op a b := by
  intro fuel
  induction fuel with
  | zero =>
      intro a b place result h
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst a
      subst b
      simp [bitLoop]
  | succ fuel ih =>
      intro a b place result h
      by_cases hz : a + b = 0
      · have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst a
        subst b
        rw [bitLoop_zero_result op hff]
        simp
      · have hpos : 0 < a + b := Nat.pos_of_ne_zero hz
        have hhalf : a.div2 + b.div2 ≤ fuel := by
          have hlt := div2_add_div2_lt hpos
          omega
        rw [bitLoop, Function.iterate_succ_apply]
        change (bitLoop op fuel (bitStep op ((a, b), (place, result)))).2.2 = _
        rw [show bitStep op ((a, b), (place, result)) =
            ((a.div2, b.div2),
              (2 * place, result + if op a.bodd b.bodd then place else 0)) by
          rfl]
        rw [ih a.div2 b.div2 (2 * place)
          (result + if op a.bodd b.bodd then place else 0) hhalf]
        conv_rhs =>
          rw [← Nat.bit_bodd_div2 a, ← Nat.bit_bodd_div2 b,
            Nat.bitwise_bit hff]
        simp only [Nat.bit]
        split <;> simp_all <;> ring

theorem computableBitwise_eq (op : Bool → Bool → Bool)
    (hff : op false false = false) (a b : ℕ) :
    computableBitwise op a b = Nat.bitwise op a b := by
  simpa [computableBitwise] using bitLoop_result op hff (a + b) a b 1 0 le_rfl

theorem nat_land_primrec₂ : Primrec₂ Nat.land := by
  change Primrec fun p : ℕ × ℕ => Nat.land p.1 p.2
  exact Primrec.of_eq (computableBitwise_primrec Bool.and) fun p =>
    computableBitwise_eq Bool.and rfl p.1 p.2

theorem nat_lor_primrec₂ : Primrec₂ Nat.lor := by
  change Primrec fun p : ℕ × ℕ => Nat.lor p.1 p.2
  exact Primrec.of_eq (computableBitwise_primrec Bool.or) fun p =>
    computableBitwise_eq Bool.or rfl p.1 p.2

theorem nat_xor_primrec₂ : Primrec₂ Nat.xor := by
  change Primrec fun p : ℕ × ℕ => Nat.xor p.1 p.2
  exact Primrec.of_eq (computableBitwise_primrec Bool.xor) fun p =>
    computableBitwise_eq Bool.xor rfl p.1 p.2

theorem nat_land_computable₂ : Computable₂ Nat.land := nat_land_primrec₂.to_comp

theorem nat_lor_computable₂ : Computable₂ Nat.lor := nat_lor_primrec₂.to_comp

theorem nat_xor_computable₂ : Computable₂ Nat.xor := nat_xor_primrec₂.to_comp

end Lax51Proofs.Computability
