import Lax20Proofs.TMToRam.BoundedSemantics

namespace Lax13Proofs.Imp

theorem exists_bind_pure_iff {α β : Type} (o : Option α) (f : α → β) :
    (∃ b, (o.bind fun a => some (f a)) = some b) ↔ ∃ a, o = some a := by
  cases o <;> simp

theorem exists_bind₂_pure_iff {α β γ : Type} (o : Option α) (p : Option β)
    (f : α → β → γ) :
    (∃ c, (o.bind fun a => p.bind fun b => some (f a b)) = some c) ↔
      (∃ a, o = some a) ∧ ∃ b, p = some b := by
  cases o <;> cases p <;> simp

theorem exists_bind₃_pure_iff {α β γ δ : Type} (o : Option α) (p : Option β)
    (q : Option γ) (f : α → β → γ → δ) :
    (∃ d, (o.bind fun a => p.bind fun b => q.bind fun c => some (f a b c)) = some d) ↔
      (∃ a, o = some a) ∧ (∃ b, p = some b) ∧ ∃ c, q = some c := by
  cases o <;> cases p <;> cases q <;> simp

/-- Bit-growth allowance for the restricted arithmetic fragment used by the
TM interpreter. `none` rejects variable-by-variable multiplication and
shifts, which could cause exponential word growth under iteration. -/
def Expr.bitGrowth : Expr → Option ℕ
  | .lit n => some (n + 1)
  | .var _ => some 0
  | .get _ i => i.bitGrowth
  | .bin .add e f => return max (← e.bitGrowth) (← f.bitGrowth) + 1
  | .bin .sub e f | .bin .div e f => return max (← e.bitGrowth) (← f.bitGrowth)
  | .bin .mul e (.lit n) => return (← e.bitGrowth) + n + 1
  | .bin .mul (.lit n) f => return (← f.bitGrowth) + n + 1
  | .bin .mul _ _ => none
  | .bin .and _ _ | .bin .or _ _ | .bin .xor _ _ => none
  | .bin .shiftl _ _ | .bin .shiftr _ _ => none

def Expr.Tame (e : Expr) : Prop := ∃ A, e.bitGrowth = some A

theorem Expr.tame_iff_exists_bitGrowth (e : Expr) :
    e.Tame ↔ ∃ A, e.bitGrowth = some A := Iff.rfl

/-- All values currently stored in or carried by an IMP environment fit in
`b` bits. Array lengths are deliberately excluded: they are addresses, not
stored word values. -/
structure Env.BitBounded (σ : Env) (b : ℕ) : Prop where
  vars : ∀ x, σ.vars x < 2 ^ b
  arrs : ∀ a v, v ∈ σ.arrs a → v < 2 ^ b
  inp : ∀ v, v ∈ σ.inp → v < 2 ^ b
  out : ∀ v, v ∈ σ.out → v < 2 ^ b

theorem pow_mono_exponent {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by omega) h

theorem option_add_eq_some {o : Option ℕ} {q A : ℕ}
    (h : (do let z ← o; pure (z + q + 1)) = some A) :
    ∃ F, o = some F ∧ A = F + q + 1 := by
  cases o <;> simp_all

theorem le_mul_of_le_of_one_le {E A K : ℕ} (hEA : E ≤ A) (hK : 1 ≤ K) :
    E ≤ K * A := by
  exact hEA.trans (by simpa using Nat.mul_le_mul_right A hK)

theorem Expr.evalB_of_bitGrowth {e : Expr} {σ : Env} {v A b : ℕ}
    (hσ : σ.BitBounded b) (hA : e.bitGrowth = some A)
    (he : e.eval σ = some v) : e.evalB (2 ^ (b + A)) σ = some v := by
  induction e generalizing v A with
  | lit n =>
      simp only [Expr.bitGrowth, Option.some.injEq] at hA
      subst A
      injection he with hv
      subst v
      apply fit_self
      exact (Nat.lt_two_pow_self (n := n)).trans_le
        (pow_mono_exponent (by omega))
  | var x =>
      simp only [Expr.bitGrowth, Option.some.injEq] at hA
      subst A
      injection he with hv
      subst v
      simpa [Expr.evalB, Nat.add_zero] using fit_self (hσ.vars x)
  | get a i ih =>
      simp only [Expr.bitGrowth] at hA
      rw [Expr.eval, Option.bind_eq_some_iff] at he
      obtain ⟨k, hk, hv⟩ := he
      have hkB := ih hA hk
      have hmem : v ∈ σ.arrs a := List.mem_of_getElem? hv
      have hvlt : v < 2 ^ (b + A) :=
        (hσ.arrs a v hmem).trans_le (pow_mono_exponent (Nat.le_add_right b A))
      simp [Expr.evalB, hkB, hv, fit_self hvlt]
  | bin op e f ihe ihf =>
      rw [Expr.eval, Option.bind_eq_some_iff] at he
      obtain ⟨m, hm, he⟩ := he
      rw [Option.map_eq_some_iff] at he
      obtain ⟨n, hn, hv⟩ := he
      subst v
      cases op with
      | add =>
          cases hE : e.bitGrowth with
          | none => simp [Expr.bitGrowth, hE] at hA
          | some E =>
            cases hF : f.bitGrowth with
            | none => simp [Expr.bitGrowth, hE, hF] at hA
            | some F =>
              simp [Expr.bitGrowth, hE, hF] at hA
              subst A
              let G := max E F
              have hm₀ := ihe hE hm
              have hn₀ := ihf hF hn
              have hmB : e.evalB (2 ^ (b + (G + 1))) σ = some m :=
                Expr.evalB_mono
                  (pow_mono_exponent (by dsimp [G]; omega)) hm₀
              have hnB : f.evalB (2 ^ (b + (G + 1))) σ = some n :=
                Expr.evalB_mono
                  (pow_mono_exponent (by dsimp [G]; omega)) hn₀
              have hmLt : m < 2 ^ (b + G) :=
                (Expr.lt_of_evalB hm₀).trans_le
                  (pow_mono_exponent (by dsimp [G]; omega))
              have hnLt : n < 2 ^ (b + G) :=
                (Expr.lt_of_evalB hn₀).trans_le
                  (pow_mono_exponent (by dsimp [G]; omega))
              have hadd : m + n < 2 ^ (b + (G + 1)) := by
                rw [show b + (G + 1) = b + G + 1 by omega]
                rw [pow_succ]
                omega
              simp [Expr.evalB, Bop.apply_add, hmB, hnB, fit_self hadd, G,
                Nat.add_assoc]
      | sub =>
          cases hE : e.bitGrowth with
          | none => simp [Expr.bitGrowth, hE] at hA
          | some E =>
            cases hF : f.bitGrowth with
            | none => simp [Expr.bitGrowth, hE, hF] at hA
            | some F =>
              simp [Expr.bitGrowth, hE, hF] at hA
              subst A
              let G := max E F
              have hm₀ := ihe hE hm
              have hn₀ := ihf hF hn
              have hmB : e.evalB (2 ^ (b + G)) σ = some m :=
                Expr.evalB_mono
                  (pow_mono_exponent (by dsimp [G]; omega)) hm₀
              have hnB : f.evalB (2 ^ (b + G)) σ = some n :=
                Expr.evalB_mono
                  (pow_mono_exponent (by dsimp [G]; omega)) hn₀
              have hsub : m - n < 2 ^ (b + G) :=
                (Nat.sub_le m n).trans_lt (Expr.lt_of_evalB hmB)
              simp [Expr.evalB, Bop.apply_sub, hmB, hnB, fit_self hsub, G]
      | mul =>
          have rightLiteral (q E : ℕ) (hE : e.bitGrowth = some E)
              (hA' : A = E + q + 1) (hf : f = .lit q) (hnq : n = q) :
              (Expr.bin .mul e f).evalB (2 ^ (b + A)) σ = some (m * n) := by
            subst A
            subst f
            subst n
            have hm₀ := ihe hE hm
            have hmLt := Expr.lt_of_evalB hm₀
            have hq : q < 2 ^ (q + 1) :=
              (Nat.lt_two_pow_self (n := q)).trans_le
                (pow_mono_exponent (by omega))
            have hmul : m * q < 2 ^ (b + (E + q + 1)) := by
              rw [show b + (E + q + 1) = (b + E) + (q + 1) by omega,
                pow_add]
              exact Nat.mul_lt_mul_of_lt_of_le hmLt (Nat.le_of_lt hq) (by positivity)
            have hmB := Expr.evalB_mono
              (pow_mono_exponent (by omega : b + E ≤ b + (E + q + 1))) hm₀
            have hnB : (Expr.lit q).evalB (2 ^ (b + (E + q + 1))) σ = some q := by
              apply fit_self
              exact hq.trans_le (pow_mono_exponent (by omega))
            rw [Expr.evalB, hmB]
            change (fit (2 ^ (b + (E + q + 1))) q).bind
              (fun z => fit (2 ^ (b + (E + q + 1))) (m * z)) = some (m * q)
            rw [show fit (2 ^ (b + (E + q + 1))) q = some q from hnB]
            exact fit_self hmul
          have leftLiteral (q F : ℕ) (hF : f.bitGrowth = some F)
              (hA' : A = F + q + 1) (heq : e = .lit q) (hmq : m = q) :
              (Expr.bin .mul e f).evalB (2 ^ (b + A)) σ = some (m * n) := by
            subst A
            subst e
            subst m
            have hn₀ := ihf hF hn
            have hnLt := Expr.lt_of_evalB hn₀
            have hq : q < 2 ^ (q + 1) :=
              (Nat.lt_two_pow_self (n := q)).trans_le
                (pow_mono_exponent (by omega))
            have hmul : q * n < 2 ^ (b + (F + q + 1)) := by
              rw [show b + (F + q + 1) = (q + 1) + (b + F) by omega,
                pow_add]
              exact Nat.mul_lt_mul_of_lt_of_le hq (Nat.le_of_lt hnLt) (by positivity)
            have hnB := Expr.evalB_mono
              (pow_mono_exponent (by omega : b + F ≤ b + (F + q + 1))) hn₀
            have hmB : (Expr.lit q).evalB (2 ^ (b + (F + q + 1))) σ = some q := by
              apply fit_self
              exact hq.trans_le (pow_mono_exponent (by omega))
            rw [Expr.evalB]
            change (fit (2 ^ (b + (F + q + 1))) q).bind
              (fun z => (f.evalB (2 ^ (b + (F + q + 1))) σ).bind
                (fun z' => fit (2 ^ (b + (F + q + 1))) (z * z'))) = some (q * n)
            rw [show fit (2 ^ (b + (F + q + 1))) q = some q from hmB, hnB]
            exact fit_self hmul
          cases f with
          | lit q =>
              cases hE : e.bitGrowth with
              | none => simp [Expr.bitGrowth, hE] at hA
              | some E =>
                have hnq : n = q := by simpa using hn.symm
                simpa only [Bop.apply_mul] using rightLiteral q E hE
                  (by simpa [Expr.bitGrowth, hE] using hA.symm)
                  rfl
                  hnq
          | var x | get x i | bin op' x i =>
              cases e with
              | lit q =>
                  have hmq : m = q := by simpa using hm.symm
                  obtain ⟨F, hF, hFA⟩ := option_add_eq_some hA
                  simpa only [Bop.apply_mul] using
                    leftLiteral q F hF hFA rfl hmq
              | var y | get y i' | bin op'' y i' =>
                  simp [Expr.bitGrowth] at hA
      | div =>
          cases hE : e.bitGrowth with
          | none => simp [Expr.bitGrowth, hE] at hA
          | some E =>
            cases hF : f.bitGrowth with
            | none => simp [Expr.bitGrowth, hE, hF] at hA
            | some F =>
              simp [Expr.bitGrowth, hE, hF] at hA
              subst A
              let G := max E F
              have hm₀ := ihe hE hm
              have hn₀ := ihf hF hn
              have hmB : e.evalB (2 ^ (b + G)) σ = some m :=
                Expr.evalB_mono
                  (pow_mono_exponent (by dsimp [G]; omega)) hm₀
              have hnB : f.evalB (2 ^ (b + G)) σ = some n :=
                Expr.evalB_mono
                  (pow_mono_exponent (by dsimp [G]; omega)) hn₀
              have hdiv : m / n < 2 ^ (b + G) :=
                (Nat.div_le_self m n).trans_lt (Expr.lt_of_evalB hmB)
              simp [Expr.evalB, Bop.apply_div, hmB, hnB, fit_self hdiv, G]
      | and | or | xor | shiftl | shiftr => simp [Expr.bitGrowth] at hA

def Cond.bitGrowth : Cond → Option ℕ
  | .eq e f | .lt e f => return max (← e.bitGrowth) (← f.bitGrowth)

def Cond.Tame (c : Cond) : Prop := ∃ A, c.bitGrowth = some A

theorem Cond.tame_iff_exists_bitGrowth (c : Cond) :
    c.Tame ↔ ∃ A, c.bitGrowth = some A := Iff.rfl

theorem Cond.evalB_of_bitGrowth {c : Cond} {σ : Env} {r : Bool} {A b : ℕ}
    (hσ : σ.BitBounded b) (hA : c.bitGrowth = some A)
    (hc : c.eval σ = some r) : c.evalB (2 ^ (b + A)) σ = some r := by
  cases c with
  | eq e f =>
      rw [Cond.eval, Option.bind_eq_some_iff] at hc
      obtain ⟨m, hm, hc⟩ := hc
      rw [Option.map_eq_some_iff] at hc
      obtain ⟨n, hn, rfl⟩ := hc
      cases hE : e.bitGrowth with
      | none => simp [Cond.bitGrowth, hE] at hA
      | some E =>
        cases hF : f.bitGrowth with
        | none => simp [Cond.bitGrowth, hE, hF] at hA
        | some F =>
          simp [Cond.bitGrowth, hE, hF] at hA
          subst A
          have hm₀ := Expr.evalB_of_bitGrowth hσ hE hm
          have hn₀ := Expr.evalB_of_bitGrowth hσ hF hn
          have hmB := Expr.evalB_mono
            (pow_mono_exponent (by omega : b + E ≤ b + max E F)) hm₀
          have hnB := Expr.evalB_mono
            (pow_mono_exponent (by omega : b + F ≤ b + max E F)) hn₀
          simp [Cond.evalB, hmB, hnB]
  | lt e f =>
      rw [Cond.eval, Option.bind_eq_some_iff] at hc
      obtain ⟨m, hm, hc⟩ := hc
      rw [Option.map_eq_some_iff] at hc
      obtain ⟨n, hn, rfl⟩ := hc
      cases hE : e.bitGrowth with
      | none => simp [Cond.bitGrowth, hE] at hA
      | some E =>
        cases hF : f.bitGrowth with
        | none => simp [Cond.bitGrowth, hE, hF] at hA
        | some F =>
          simp [Cond.bitGrowth, hE, hF] at hA
          subst A
          have hm₀ := Expr.evalB_of_bitGrowth hσ hE hm
          have hn₀ := Expr.evalB_of_bitGrowth hσ hF hn
          have hmB := Expr.evalB_mono
            (pow_mono_exponent (by omega : b + E ≤ b + max E F)) hm₀
          have hnB := Expr.evalB_mono
            (pow_mono_exponent (by omega : b + F ≤ b + max E F)) hn₀
          simp [Cond.evalB, hmB, hnB]

theorem Env.BitBounded.mono {σ : Env} {a b : ℕ} (h : σ.BitBounded a)
    (hab : a ≤ b) : σ.BitBounded b := by
  have hp := pow_mono_exponent hab
  exact ⟨fun x => (h.vars x).trans_le hp,
    fun x v hv => (h.arrs x v hv).trans_le hp,
    fun v hv => (h.inp v hv).trans_le hp,
    fun v hv => (h.out v hv).trans_le hp⟩

theorem Env.BitBounded.setVar {σ : Env} {b v : ℕ} (h : σ.BitBounded b)
    (x : String) (hv : v < 2 ^ b) : (σ.setVar x v).BitBounded b := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y
    by_cases hy : y = x
    · simp [Env.setVar, hy, hv]
    · simp [Env.setVar, hy, h.vars y]
  · exact h.arrs
  · exact h.inp
  · exact h.out

theorem Env.BitBounded.setArr {σ : Env} {b k v : ℕ} (h : σ.BitBounded b)
    (a : String) (hv : v < 2 ^ b) : (σ.setArr a k v).BitBounded b := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h.vars
  · intro name u hu
    simp only [Env.setArr] at hu
    split at hu
    · rename_i heq
      subst name
      rcases List.mem_or_eq_of_mem_set hu with hu | rfl
      · exact h.arrs a u hu
      · exact hv
    · exact h.arrs name u hu
  · exact h.inp
  · exact h.out

theorem Env.BitBounded.write {σ : Env} {b v : ℕ} (h : σ.BitBounded b)
    (hv : v < 2 ^ b) : ({σ with out := σ.out ++ [v]} : Env).BitBounded b := by
  refine ⟨h.vars, h.arrs, h.inp, ?_⟩
  intro u hu
  rw [List.mem_append] at hu
  rcases hu with hu | hu
  · exact h.out u hu
  · simp at hu
    subst u
    exact hv

theorem initEnv_bitBounded (ext : String → ℕ) (x : List ℕ) :
    (initEnv ext (x.length :: x)).BitBounded
      (Lax20.BinaryWordEncoding.bitSize x + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro name
    simp [initEnv]
  · intro name v hv
    simp [initEnv] at hv
    rcases hv with ⟨_, rfl⟩
    positivity
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Lax20Proofs.Encoding.length_lt_two_pow_bitSize_add_one x
    · exact Lax20Proofs.Encoding.mem_lt_two_pow_bitSize_add_one hv
  · simp [initEnv]

end Lax13Proofs.Imp

namespace Lax13Proofs.Compile

def Layout.bitOverhead (L : Layout) : ℕ :=
  L.scalars.length + L.temps + L.arrays.length

/-- If values require `E` bits, adding the fixed layout overhead to the word
length suffices for every scalar, temporary and flattened-array address. -/
theorem Layout.fitsWords_two_pow (L : Layout) {E w : ℕ} (hE : 0 < E)
    (hw : E + L.bitOverhead ≤ w) : L.FitsWords (2 ^ E) w := by
  have hpowE : 1 < 2 ^ E := by
    cases E with
    | zero => contradiction
    | succ E =>
      have hp : 0 < 2 ^ E := pow_pos (by omega) E
      rw [pow_succ]
      omega
  have hbound : 2 ^ E ≤ 2 ^ w :=
    Nat.pow_le_pow_right (by omega) ((Nat.le_add_right E _).trans hw)
  refine ⟨hpowE, hbound, ?_⟩
  let C := L.bitOverhead
  have hCB : L.span (2 ^ E) ≤ C * 2 ^ E := by
    have hone : 1 ≤ 2 ^ E := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    have hsmall : L.scalars.length + L.temps ≤
        (L.scalars.length + L.temps) * 2 ^ E := by
      simpa using Nat.mul_le_mul_left (L.scalars.length + L.temps) hone
    simp only [Layout.span, C, Layout.bitOverhead]
    rw [Nat.add_mul]
    omega
  have hC : C ≤ 2 ^ C := Nat.le_of_lt (Nat.lt_two_pow_self (n := C))
  calc
    L.span (2 ^ E) ≤ C * 2 ^ E := hCB
    _ ≤ 2 ^ C * 2 ^ E := Nat.mul_le_mul_right _ hC
    _ = 2 ^ (E + C) := by rw [← pow_add, Nat.add_comm]
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw

end Lax13Proofs.Compile

namespace Lax13Proofs.Imp

def Com.bitGrowth : Com → Option ℕ
  | .skip | .read _ => some 1
  | .assign _ e | .write e => return max 1 (← e.bitGrowth)
  | .store _ i e => return max 1 (max (← i.bitGrowth) (← e.bitGrowth))
  | .seq c d => return max (← c.bitGrowth) (← d.bitGrowth)
  | .ite b c d => return max (← b.bitGrowth) (max (← c.bitGrowth) (← d.bitGrowth))
  | .while b c => return max (← b.bitGrowth) (← c.bitGrowth)

def Com.Tame (c : Com) : Prop := ∃ A, c.bitGrowth = some A

theorem Com.tame_iff_exists_bitGrowth (c : Com) :
    c.Tame ↔ ∃ A, c.bitGrowth = some A := Iff.rfl

namespace Expr.Tame

theorem lit (n : ℕ) : (Expr.lit n).Tame := ⟨n + 1, rfl⟩
theorem var (x : String) : (Expr.var x).Tame := ⟨0, rfl⟩
theorem get {i : Expr} (h : i.Tame) (a : String) : (Expr.get a i).Tame := h

theorem add {e f : Expr} (he : e.Tame) (hf : f.Tame) : (Expr.add e f).Tame := by
  obtain ⟨E, hE⟩ := he
  obtain ⟨F, hF⟩ := hf
  exact ⟨max E F + 1, by simp [Expr.bitGrowth, hE, hF]⟩

theorem sub {e f : Expr} (he : e.Tame) (hf : f.Tame) : (Expr.sub e f).Tame := by
  obtain ⟨E, hE⟩ := he
  obtain ⟨F, hF⟩ := hf
  exact ⟨max E F, by simp [Expr.bitGrowth, hE, hF]⟩

theorem div {e f : Expr} (he : e.Tame) (hf : f.Tame) : (Expr.div e f).Tame := by
  obtain ⟨E, hE⟩ := he
  obtain ⟨F, hF⟩ := hf
  exact ⟨max E F, by simp [Expr.bitGrowth, hE, hF]⟩

theorem mul_lit_right {e : Expr} (he : e.Tame) (n : ℕ) :
    (Expr.mul e (.lit n)).Tame := by
  obtain ⟨E, hE⟩ := he
  exact ⟨E + n + 1, by simp [Expr.bitGrowth, hE]⟩

theorem mul_lit_left (n : ℕ) {e : Expr} (he : e.Tame) :
    (Expr.mul (.lit n) e).Tame := by
  cases e with
  | lit q => exact mul_lit_right (lit n) q
  | var x => exact ⟨n + 1, by simp [Expr.bitGrowth]⟩
  | get x q | bin x q =>
      obtain ⟨E, hE⟩ := he
      refine ⟨E + n + 1, ?_⟩
      change ((Expr.bitGrowth _).bind fun z => some (z + n + 1)) = _
      simp [hE]

end Expr.Tame

namespace Cond.Tame

theorem eq {e f : Expr} (he : e.Tame) (hf : f.Tame) : (Cond.eq e f).Tame := by
  obtain ⟨E, hE⟩ := he
  obtain ⟨F, hF⟩ := hf
  exact ⟨max E F, by simp [Cond.bitGrowth, hE, hF]⟩

theorem lt {e f : Expr} (he : e.Tame) (hf : f.Tame) : (Cond.lt e f).Tame := by
  obtain ⟨E, hE⟩ := he
  obtain ⟨F, hF⟩ := hf
  exact ⟨max E F, by simp [Cond.bitGrowth, hE, hF]⟩

end Cond.Tame

namespace Com.Tame

theorem skip : Com.skip.Tame := ⟨1, rfl⟩
theorem read (x : String) : (Com.read x).Tame := ⟨1, rfl⟩

theorem assign (x : String) {e : Expr} (he : e.Tame) : (Com.assign x e).Tame := by
  obtain ⟨E, hE⟩ := he
  exact ⟨max 1 E, by simp [Com.bitGrowth, hE]⟩

theorem write {e : Expr} (he : e.Tame) : (Com.write e).Tame := by
  obtain ⟨E, hE⟩ := he
  exact ⟨max 1 E, by simp [Com.bitGrowth, hE]⟩

theorem store (a : String) {i e : Expr} (hi : i.Tame) (he : e.Tame) :
    (Com.store a i e).Tame := by
  obtain ⟨I, hI⟩ := hi
  obtain ⟨E, hE⟩ := he
  exact ⟨max 1 (max I E), by simp [Com.bitGrowth, hI, hE]⟩

theorem seq {c d : Com} (hc : c.Tame) (hd : d.Tame) : (Com.seq c d).Tame := by
  obtain ⟨C, hC⟩ := hc
  obtain ⟨D, hD⟩ := hd
  exact ⟨max C D, by simp [Com.bitGrowth, hC, hD]⟩

theorem ite {b : Cond} {c d : Com} (hb : b.Tame) (hc : c.Tame) (hd : d.Tame) :
    (Com.ite b c d).Tame := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨C, hC⟩ := hc
  obtain ⟨D, hD⟩ := hd
  exact ⟨max B (max C D), by simp [Com.bitGrowth, hB, hC, hD]⟩

theorem «while» {b : Cond} {c : Com} (hb : b.Tame) (hc : c.Tame) :
    (Com.while b c).Tame := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨C, hC⟩ := hc
  exact ⟨max B C, by simp [Com.bitGrowth, hB, hC]⟩

end Com.Tame

theorem Com.one_le_bitGrowth {c : Com} {A : ℕ} (h : c.bitGrowth = some A) :
    1 ≤ A := by
  induction c generalizing A with
  | skip | read => simp [Com.bitGrowth] at h; omega
  | assign x e | write e =>
      cases he : e.bitGrowth <;> simp [Com.bitGrowth, he] at h
      omega
  | store a i e =>
      cases hi : i.bitGrowth <;> cases he : e.bitGrowth <;>
        simp [Com.bitGrowth, hi, he] at h
      omega
  | seq c d ihc ihd =>
      cases hc : c.bitGrowth <;> cases hd : d.bitGrowth <;>
        simp [Com.bitGrowth, hc, hd] at h
      subst A
      exact (ihc hc).trans (le_max_left _ _)
  | ite b c d ihc ihd =>
      cases hb : b.bitGrowth <;> cases hc : c.bitGrowth <;>
        cases hd : d.bitGrowth <;> simp [Com.bitGrowth, hb, hc, hd] at h
      subst A
      exact (ihc hc).trans (le_max_left _ _ |>.trans (le_max_right _ _))
  | «while» b c ih =>
      cases hb : b.bitGrowth <;> cases hc : c.bitGrowth <;>
        simp [Com.bitGrowth, hb, hc] at h
      subst A
      exact (ih hc).trans (le_max_right _ _)

/-- A run of a fixed tame command increases bit length by at most its
syntactic allowance per unit of IMP cost. -/
theorem BigStep.bigStepB_of_bitGrowth {c : Com} {σ σ' : Env} {k b G A : ℕ}
    (h : BigStep c σ σ' k) (hσ : σ.BitBounded b)
    (hG : c.bitGrowth = some G) (hGA : G ≤ A) :
    BigStepB (2 ^ (b + k * A)) c σ σ' k ∧ σ'.BitBounded (b + k * A) := by
  induction h generalizing b G A with
  | @skip σ0 =>
      constructor
      · exact .skip
      · simpa [Com.bitGrowth] using hσ.mono (Nat.le_add_right b _)
  | @assign σ0 x e v he =>
      cases hE : e.bitGrowth with
      | none => simp [Com.bitGrowth, hE] at hG
      | some E =>
        simp [Com.bitGrowth, hE] at hG
        subst G
        have hEA : E ≤ A := (le_max_right 1 E).trans hGA
        have he₀ := Expr.evalB_of_bitGrowth hσ hE he
        have heB := Expr.evalB_mono
          (pow_mono_exponent (Nat.add_le_add_left
            (le_mul_of_le_of_one_le (K := 1 + e.size) hEA (by omega)) b)) he₀
        have hv := Expr.lt_of_evalB heB
        exact ⟨.assign heB,
          (hσ.mono (Nat.le_add_right b _)).setVar x hv⟩
  | @store σ0 a i e pos v hi he hk =>
      cases hI : i.bitGrowth with
      | none => simp [Com.bitGrowth, hI] at hG
      | some I =>
        cases hE : e.bitGrowth with
        | none => simp [Com.bitGrowth, hI, hE] at hG
        | some E =>
          simp [Com.bitGrowth, hI, hE] at hG
          subst G
          have hIA : I ≤ A :=
            (le_max_left I E).trans (le_max_right 1 (max I E) |>.trans hGA)
          have hEA : E ≤ A :=
            (le_max_right I E).trans (le_max_right 1 (max I E) |>.trans hGA)
          let K := 1 + i.size + e.size
          have hi₀ := Expr.evalB_of_bitGrowth hσ hI hi
          have he₀ := Expr.evalB_of_bitGrowth hσ hE he
          have hiB := Expr.evalB_mono
            (pow_mono_exponent (Nat.add_le_add_left
              (le_mul_of_le_of_one_le (K := K) hIA (by
                dsimp [K]
                omega)) b)) hi₀
          have heB := Expr.evalB_mono
            (pow_mono_exponent (Nat.add_le_add_left
              (le_mul_of_le_of_one_le (K := K) hEA (by
                dsimp [K]
                omega)) b)) he₀
          exact ⟨.store hiB heB hk,
            (hσ.mono (Nat.le_add_right b _)).setArr a
              (Expr.lt_of_evalB heB)⟩
  | @seq c d σ0 σ1 σ2 k1 k2 h₁ h₂ ih₁ ih₂ =>
      cases hC : c.bitGrowth with
      | none => simp [Com.bitGrowth, hC] at hG
      | some C =>
        cases hD : d.bitGrowth with
        | none => simp [Com.bitGrowth, hC, hD] at hG
        | some D =>
          simp [Com.bitGrowth, hC, hD] at hG
          subst G
          have hCA : C ≤ A := (le_max_left C D).trans hGA
          have hDA : D ≤ A := (le_max_right C D).trans hGA
          obtain ⟨hb₁, hs₁⟩ := ih₁ hσ hC hCA
          obtain ⟨hb₂, hs₂⟩ := ih₂ hs₁ hD hDA
          have hb₁' : BigStepB (2 ^ (b + (k1 + k2) * A)) c σ0 σ1 k1 :=
            hb₁.mono (pow_mono_exponent (by
              rw [Nat.add_mul]
              omega))
          have hb₂' : BigStepB (2 ^ (b + (k1 + k2) * A)) d σ1 σ2 k2 := by
            simpa [Nat.add_mul, Nat.add_assoc] using hb₂
          exact ⟨.seq
            hb₁' hb₂',
            by simpa [Nat.add_mul, Nat.add_assoc] using hs₂⟩
  | @ite_true cond c d σ0 σ1 k1 hb hc ih =>
      cases hB : cond.bitGrowth with
      | none => simp [Com.bitGrowth, hB] at hG
      | some B =>
        cases hC : c.bitGrowth with
        | none => simp [Com.bitGrowth, hB, hC] at hG
        | some C =>
          cases hD : d.bitGrowth with
          | none => simp [Com.bitGrowth, hB, hC, hD] at hG
          | some D =>
            simp [Com.bitGrowth, hB, hC, hD] at hG
            subst G
            have hBA : B ≤ A := (le_max_left B (max C D)).trans hGA
            have hCA : C ≤ A :=
              (le_max_left C D).trans (le_max_right B (max C D) |>.trans hGA)
            obtain ⟨hcB, hs'⟩ := ih hσ hC hCA
            have hone : 1 ≤ A := (Com.one_le_bitGrowth hC).trans hCA
            let T := b + (1 + cond.size + k1) * A
            have hb₀ := Cond.evalB_of_bitGrowth hσ hB hb
            have hbB : cond.evalB (2 ^ T) σ0 = some true :=
              Cond.evalB_mono (pow_mono_exponent (Nat.add_le_add_left
                (le_mul_of_le_of_one_le (K := 1 + cond.size + k1) hBA
                  (by omega)) b)) hb₀
            have hcB' : BigStepB (2 ^ T) c σ0 σ1 k1 :=
              hcB.mono (pow_mono_exponent (by
                dsimp [T]
                rw [Nat.add_mul]
                omega))
            exact ⟨.ite_true hbB hcB', by
              apply hs'.mono
              dsimp [T]
              rw [Nat.add_mul]
              omega⟩
  | @ite_false cond c d σ0 σ1 k1 hb hd ih =>
      cases hB : cond.bitGrowth with
      | none => simp [Com.bitGrowth, hB] at hG
      | some B =>
        cases hC : c.bitGrowth with
        | none => simp [Com.bitGrowth, hB, hC] at hG
        | some C =>
          cases hD : d.bitGrowth with
          | none => simp [Com.bitGrowth, hB, hC, hD] at hG
          | some D =>
            simp [Com.bitGrowth, hB, hC, hD] at hG
            subst G
            have hBA : B ≤ A := (le_max_left B (max C D)).trans hGA
            have hDA : D ≤ A :=
              (le_max_right C D).trans (le_max_right B (max C D) |>.trans hGA)
            obtain ⟨hdB, hs'⟩ := ih hσ hD hDA
            have hone : 1 ≤ A := (Com.one_le_bitGrowth hD).trans hDA
            let T := b + (1 + cond.size + k1) * A
            have hb₀ := Cond.evalB_of_bitGrowth hσ hB hb
            have hbB : cond.evalB (2 ^ T) σ0 = some false :=
              Cond.evalB_mono (pow_mono_exponent (Nat.add_le_add_left
                (le_mul_of_le_of_one_le (K := 1 + cond.size + k1) hBA
                  (by omega)) b)) hb₀
            have hdB' : BigStepB (2 ^ T) d σ0 σ1 k1 :=
              hdB.mono (pow_mono_exponent (by
                dsimp [T]
                rw [Nat.add_mul]
                omega))
            exact ⟨.ite_false hbB hdB', by
              apply hs'.mono
              dsimp [T]
              rw [Nat.add_mul]
              omega⟩
  | @while_true cond c σ0 σ1 σ2 k1 k2 hb hc hw ihc ihw =>
      cases hB : cond.bitGrowth with
      | none => simp [Com.bitGrowth, hB] at hG
      | some B =>
        cases hC : c.bitGrowth with
        | none => simp [Com.bitGrowth, hB, hC] at hG
        | some C =>
          simp [Com.bitGrowth, hB, hC] at hG
          subst G
          have hBA : B ≤ A := (le_max_left B C).trans hGA
          have hCA : C ≤ A := (le_max_right B C).trans hGA
          obtain ⟨hcB, hs₁⟩ := ihc hσ hC hCA
          obtain ⟨hwB, hs₂⟩ := ihw hs₁ (by simpa [Com.bitGrowth, hB, hC]) hGA
          have hone : 1 ≤ A := (Com.one_le_bitGrowth hC).trans hCA
          let T := b + (1 + cond.size + k1 + k2) * A
          have hb₀ := Cond.evalB_of_bitGrowth hσ hB hb
          have hbB : cond.evalB (2 ^ T) σ0 = some true :=
            Cond.evalB_mono (pow_mono_exponent (Nat.add_le_add_left
              (le_mul_of_le_of_one_le (K := 1 + cond.size + k1 + k2) hBA
                (by omega)) b)) hb₀
          have hcB' : BigStepB (2 ^ T) c σ0 σ1 k1 :=
            hcB.mono (pow_mono_exponent (by
              dsimp [T]
              simp only [Nat.add_mul, Nat.one_mul]
              omega))
          have hwB' : BigStepB (2 ^ T) (.while cond c) σ1 σ2 k2 :=
            hwB.mono (pow_mono_exponent (by
              dsimp [T]
              simp only [Nat.add_mul, Nat.one_mul]
              omega))
          exact ⟨.while_true hbB hcB' hwB',
            by
              apply hs₂.mono
              dsimp [T]
              simp only [Nat.add_mul, Nat.one_mul]
              omega⟩
  | @while_false cond c σ0 hb =>
      cases hB : cond.bitGrowth with
      | none => simp [Com.bitGrowth, hB] at hG
      | some B =>
        cases hC : c.bitGrowth with
        | none => simp [Com.bitGrowth, hB, hC] at hG
        | some C =>
          simp [Com.bitGrowth, hB, hC] at hG
          subst G
          have hBA : B ≤ A := (le_max_left B C).trans hGA
          have hCA : C ≤ A := (le_max_right B C).trans hGA
          have hone : 1 ≤ A := (Com.one_le_bitGrowth hC).trans hCA
          have hb₀ := Cond.evalB_of_bitGrowth hσ hB hb
          have hbB := Cond.evalB_mono (pow_mono_exponent
            (Nat.add_le_add_left
              (le_mul_of_le_of_one_le (K := 1 + cond.size) hBA (by omega)) b)) hb₀
          exact ⟨.while_false hbB,
            hσ.mono (Nat.le_add_right b _)⟩
  | @read σ0 x v rest hin =>
      simp [Com.bitGrowth] at hG
      subst G
      have hv : v < 2 ^ b := hσ.inp v (by rw [hin]; simp)
      have hrest : ∀ u ∈ rest, u < 2 ^ b := by
        intro u hu
        exact hσ.inp u (by rw [hin]; exact List.mem_cons_of_mem _ hu)
      constructor
      · exact .read hin
      · have hset := hσ.setVar x hv
        have hnew : ({σ0.setVar x v with inp := rest} : Env).BitBounded b :=
          ⟨hset.vars, hset.arrs, hrest, hset.out⟩
        exact hnew.mono (Nat.le_add_right b _)
  | @write σ0 e v he =>
      cases hE : e.bitGrowth with
      | none => simp [Com.bitGrowth, hE] at hG
      | some E =>
        simp [Com.bitGrowth, hE] at hG
        subst G
        have hEA : E ≤ A := (le_max_right 1 E).trans hGA
        have he₀ := Expr.evalB_of_bitGrowth hσ hE he
        have heB := Expr.evalB_mono
          (pow_mono_exponent (Nat.add_le_add_left
            (le_mul_of_le_of_one_le (K := 1 + e.size) hEA (by omega)) b)) he₀
        exact ⟨.write heB,
          (hσ.mono (Nat.le_add_right b _)).write
            (Expr.lt_of_evalB heB)⟩

end Lax13Proofs.Imp
