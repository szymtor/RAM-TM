-- Adapted 2026-09-15 from word-ram-v4-33 at 0aa87e1f6e6add4abe4f4e0aff8fe4a28950b2ea.
-- Namespace relocated for use as a proof-only intermediate; semantics unchanged.
import Lax759944Proofs.Legacy.Lib.Ind

/-!
An undo trail: a log of the cells of a companion array that were set,
and a height, so that everything logged above a saved height can be put
back at once.

Both of Lax15's rungs are built on one. A frame of the search marks a
set of vertices, records each of them on the trail, and saves the trail
height it found; popping the frame runs the height back down to what it
saved, unmarking as it goes. The loop that does it — `unwindLoop` at
`Lax15Proofs/Phases.lean:254`, proved once there and used by both rungs
— is this module's `unwind`, and it is the reason the module exists.

### What is logged, and what undoing means

The trail is a log of *indices into one companion array*, and undoing an
entry writes `0` into that cell. That is exactly the consumers' shape
and nothing more: their entries are vertices, their companion is the
mark array, and the value put back is always `0`, because `0` is what an
indicator array holds for "not in the set" and a fresh machine array is
zeroed. A general trail would log (index, old value) pairs and need a
second array to hold the values; neither consumer has one, and the
campaign's watch item says to keep the relations cheap. So: one trail
array, one companion, and the undo value is `0`.

The companion is named in the *operations and their specifications*, not
in the relation. A `record` does not touch the companion — in both
consumers the marking store and the trail store are separate commands,
`mark[v] := 1; trail[tt] := v; tt := tt + 1` — so making the relation
carry the companion would put a conjunct into every statement that most
of them do not use. `unwind` is where the two meet, and its
specification names both: it takes `Trail` and `Ind` and gives back
`Trail` at the saved height and `Ind` with the entries cleared.

### The relation

`Trail a t cap n h g σ` is `Stack`'s relation with the entry bound
instantiated at the companion's extent: the array named `a` is
`arrOf cap g`, the scalar `t` holds `h`, the trail fits, and every entry
below the height is a position of an `n`-cell array. The two relations
agreeing conjunct for conjunct is not an accident — a trail *is* a stack
of indices — but they are declared separately, because a trail is never
peeked or popped and a stack is never unwound, and a `Lib` module should
be readable and instantiable one at a time. A consumer wanting both
views of one array pairs the two relations.

The entry bound is what makes `unwind`'s inner store legal: the cell it
writes into is `g i`, and the store's range obligation is exactly
`g i < n`. This is `Ind`'s bit condition in the same role — the
invariant that lives *in* the relation so that no operation's
precondition has to carry it.

### The cost of `unwind`

Linear in the entries removed, and stated that way: `12 * (h - base) +
4`. The loop is proved with `Spec.while_count` — an invariant, a
variant, one cost per turn — rather than `while_potential`, because
nothing here is amortized: every turn removes one entry and costs the
same eight. The potential form is for `Csr`'s owner-advancing scan,
where a turn's cost varies.
-/

namespace Lax759944Proofs.Legacy.Reasoning.Lib

open Lax759944Proofs.Legacy.Imp

variable {B cap n h h' i v : ℕ} {a t tb b x y : String} {g : ℕ → ℕ} {σ : Env}

/-! ### The relation -/

/-- `Trail a t cap n h g σ`: in `σ`, the array named `a` is the
length-`cap` array whose cell `i` is `g i`, the scalar named `t` holds
the height `h`, the trail fits in the array, and every entry below the
height is a position of an `n`-cell array. -/
def Trail (a t : String) (cap n h : ℕ) (g : ℕ → ℕ) (σ : Env) : Prop :=
  σ.arrs a = arrOf cap g ∧ σ.vars t = h ∧ h ≤ cap ∧ ∀ i, i < h → g i < n

/-- The trail array. -/
theorem Trail.arr (ht : Trail a t cap n h g σ) : σ.arrs a = arrOf cap g := ht.1

/-- The height. -/
theorem Trail.height (ht : Trail a t cap n h g σ) : σ.vars t = h := ht.2.1

/-- The trail fits. -/
theorem Trail.le_cap (ht : Trail a t cap n h g σ) : h ≤ cap := ht.2.2.1

/-- Every entry is a position of the companion. -/
theorem Trail.entry (ht : Trail a t cap n h g σ) (hi : i < h) : g i < n := ht.2.2.2 i hi

/-- The length, which is what a store's range condition asks for. -/
theorem Trail.length (ht : Trail a t cap n h g σ) : (σ.arrs a).length = cap := by
  rw [ht.arr, length_arrOf]

/-- Reading an entry. -/
theorem Trail.getD (ht : Trail a t cap n h g σ) (hi : i < cap) :
    (σ.arrs a).getD i 0 = g i := by
  rw [ht.arr, getD_arrOf g hi]

/-- **Every entry is a word as soon as the companion's extent is**: the
reason the bound belongs in the relation, exactly as `Ind.lt`. -/
theorem Trail.lt (ht : Trail a t cap n h g σ) (hnB : n ≤ B) (hi : i < h) : g i < B :=
  lt_of_lt_of_le (ht.entry hi) hnB

/-- The relation, restated at the height the environment holds — the
form the loop invariant is in. -/
theorem Trail.at_height (ht : Trail a t cap n h g σ) :
    Trail a t cap n (σ.vars t) g σ := ht.height ▸ ht

/-- An assignment to any scalar but the height leaves the trail
alone. -/
@[simp] theorem Trail.setVar_iff (a t : String) (cap n h : ℕ) (g : ℕ → ℕ) (σ : Env)
    (y : String) (v : ℕ) (hy : y ≠ t) :
    Trail a t cap n h g (σ.setVar y v) ↔ Trail a t cap n h g σ := by
  simp [Trail, Ne.symm hy]

theorem Trail.setVar (ht : Trail a t cap n h g σ) (hy : y ≠ t) (v : ℕ) :
    Trail a t cap n h g (σ.setVar y v) :=
  (Trail.setVar_iff a t cap n h g σ y v hy).2 ht

/-- **The transport lemma.** The relation is a statement about one array
and one scalar, so any environment agreeing on those two satisfies it.
This is what carries a trail across a phase that touches neither — in
the consumers, across every marking store and every scan. -/
theorem Trail.of_eq (ht : Trail a t cap n h g σ) {σ' : Env}
    (harr : σ'.arrs a = σ.arrs a) (hvar : σ'.vars t = σ.vars t) :
    Trail a t cap n h g σ' :=
  ⟨by rw [harr, ht.arr], by rw [hvar, ht.height], ht.2.2.1, ht.2.2.2⟩

/-- A store into another array — the companion, in particular — leaves
the trail alone. -/
theorem Trail.setArr_of_ne (ht : Trail a t cap n h g σ) (hb : b ≠ a) (k v : ℕ) :
    Trail a t cap n h g (σ.setArr b k v) :=
  ⟨by rw [arrs_setArr, if_neg (Ne.symm hb), ht.arr], ht.2.1, ht.2.2.1, ht.2.2.2⟩

/-- **Writing the cell above the top**, the first half of a `record`. -/
theorem Trail.setTop (ht : Trail a t cap n h g σ) (v : ℕ) :
    Trail a t cap n h (upd g h v) (σ.setArr a h v) :=
  ⟨by rw [arrs_setArr, if_pos rfl, ht.arr, set_arrOf_eq_upd], ht.2.1, ht.2.2.1,
   fun i hi => by rw [upd_of_ne _ (by omega)]; exact ht.entry hi⟩

/-- **Taking it into the trail**, the second half: the height moves up,
and the new entry has to be a position of the companion. -/
theorem Trail.raise (ht : Trail a t cap n h g σ) (hcap : h < cap) (hv : g h < n) :
    Trail a t cap n (h + 1) g (σ.setVar t (h + 1)) :=
  ⟨by rw [arrs_setVar, ht.arr], by simp, hcap, fun i hi => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ht.entry hi
    · exact hv⟩

/-- **Lowering the height.** The entries above it stay in the array —
nothing ever reads them — so this is the whole of an undone turn as far
as the trail is concerned. -/
theorem Trail.shrink (ht : Trail a t cap n h g σ) (hle : h' ≤ h) :
    Trail a t cap n h' g (σ.setVar t h') :=
  ⟨by rw [arrs_setVar, ht.arr], by simp, le_trans hle ht.le_cap,
   fun i hi => ht.entry (lt_of_lt_of_le hi hle)⟩

/-! Everything from here on is this module's own, so it lives in the
module's namespace. -/

namespace Trail

/-! ### Undoing a stretch of the trail

What `unwind` does to the companion's cell function, as a function: the
entries logged at `t, t + 1, …, t + d - 1` are put back to zero. The
recursion is on the number of entries and moves the pointer up, which is
the direction the loop's invariant needs — at height `t`, everything
from `t` to the height the unwind started at has been undone. Since
every undo writes the same value, the order does not matter, and the
convenient recursion is the one that reads. -/

/-- `f` with the cells the trail logged at `t, …, t + d - 1` set to
zero. -/
def undoRange (g f : ℕ → ℕ) : ℕ → ℕ → (ℕ → ℕ)
  | _, 0 => f
  | t, d + 1 => upd (undoRange g f (t + 1) d) (g t) 0

/-! The equation lemmas, materialized here per the standing kit rule of
`Frame.lean`: a downstream `simp [undoRange]` then finds them among its
imports and creates nothing named under `Lax759944Proofs.Legacy` in a consumer
package. -/

@[simp] theorem undoRange_zero (g f : ℕ → ℕ) (t : ℕ) : undoRange g f t 0 = f := by
  simp [undoRange]

theorem undoRange_succ (g f : ℕ → ℕ) (t d : ℕ) :
    undoRange g f t (d + 1) = upd (undoRange g f (t + 1) d) (g t) 0 := by
  simp [undoRange]

/-- **The step the loop takes.** One more entry undone, at the bottom
end: this is the whole functional content of a turn. -/
theorem undoRange_step (g f : ℕ → ℕ) {t d : ℕ} (h0 : 0 < t) (hle : t ≤ d) :
    undoRange g f (t - 1) (d - (t - 1)) = upd (undoRange g f t (d - t)) (g (t - 1)) 0 := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel, show d - t' = (d - (t' + 1)) + 1 by omega, undoRange_succ]

/-- An undone stretch keeps the companion's cells bounded: the only
value it writes is zero. -/
theorem undoRange_le (g f : ℕ → ℕ) (t d c i : ℕ) (hf : ∀ j, f j ≤ c) :
    undoRange g f t d i ≤ c := by
  induction d generalizing t i with
  | zero => simpa using hf i
  | succ d ih => rw [undoRange_succ, upd_apply]; split; · omega
                 exact ih _ _

/-- A cell the stretch logged comes back zero — what a consumer reads
off an unwind. -/
theorem undoRange_of_mem (g f : ℕ → ℕ) {t d j : ℕ} (hj : t ≤ j) (hj' : j < t + d) :
    undoRange g f t d (g j) = 0 := by
  induction d generalizing t with
  | zero => omega
  | succ d ih =>
      rw [undoRange_succ]
      rcases Nat.eq_or_lt_of_le hj with rfl | hj''
      · simp
      · rw [upd_apply]
        split
        · rfl
        · exact ih (by omega) (by omega)

/-- A cell the stretch did not log is where it was. -/
theorem undoRange_of_notMem (g f : ℕ → ℕ) {t d k : ℕ}
    (hk : ∀ j, t ≤ j → j < t + d → g j ≠ k) : undoRange g f t d k = f k := by
  induction d generalizing t with
  | zero => simp
  | succ d ih =>
      rw [undoRange_succ, upd_of_ne _ (fun hgt => hk t le_rfl (by omega) hgt.symm)]
      exact ih (fun j hj hj' => hk j (by omega) (by omega))

/-! ### The operations -/

/-- Log the value of `x` on the trail `a` counted by `t`. -/
def record (a t x : String) : Com :=
  .seq (.store a (.var t) (.var x)) (.assign t (.add (.var t) (.lit 1)))

/-- One turn of an unwind: take the top entry off and put its cell of
the companion `b` back to zero. -/
def unwindBody (a t b : String) : Com :=
  .seq (.assign t (.sub (.var t) (.lit 1))) (.store b (.get a (.var t)) (.lit 0))

/-- Unwind the trail `a` down to the height saved in `tb`, undoing every
entry above it in the companion `b`. -/
def unwind (a t tb b : String) : Com :=
  .while (.lt (.var tb) (.var t)) (unwindBody a t b)

/-! The frame conditions of the two exported operations, as `simp`
lemmas: a call site's array and count are bound variables, so
`Spec.frame`'s obligations are discharged there by `simp` and not by
`decide`. -/

@[simp] theorem wvars_record (a t x : String) : (record a t x).wvars = [t] := by
  simp [record, Com.wvars]

@[simp] theorem warrs_record (a t x : String) : (record a t x).warrs = [a] := by
  simp [record, Com.warrs]

@[simp] theorem not_reads_record (a t x : String) : ¬ (record a t x).reads := by
  simp [record, Com.reads]

@[simp] theorem noWrite_record (a t x : String) : (record a t x).NoWrite := by
  simp [record, Com.NoWrite]

@[simp] theorem wvars_unwind (a t tb b : String) : (unwind a t tb b).wvars = [t] := by
  simp [unwind, unwindBody, Com.wvars]

@[simp] theorem warrs_unwind (a t tb b : String) : (unwind a t tb b).warrs = [b] := by
  simp [unwind, unwindBody, Com.warrs]

@[simp] theorem not_reads_unwind (a t tb b : String) : ¬ (unwind a t tb b).reads := by
  simp [unwind, unwindBody, Com.reads]

@[simp] theorem noWrite_unwind (a t tb b : String) : (unwind a t tb b).NoWrite := by
  simp [unwind, unwindBody, Com.NoWrite]

/-! ### The specifications -/

/-- What both operations need: the relation, the companion's extent
inside the word bound, and a height that stays a word when it moves. -/
abbrev Pre (a t : String) (cap n h B : ℕ) (g : ℕ → ℕ) (σ : Env) : Prop :=
  Trail a t cap n h g σ ∧ n ≤ B ∧ h + 1 < B

/-- What a `record` needs on top of that: room in the array, and an
entry that is a position of the companion. -/
abbrev RecordPre (a t x : String) (cap n h B : ℕ) (g : ℕ → ℕ) (σ : Env) : Prop :=
  Pre a t cap n h B g σ ∧ h < cap ∧ σ.vars x < n

/-- What `record` leaves: one entry more, at the old height. -/
abbrev RecordPost (a t x : String) (cap n h : ℕ) (g : ℕ → ℕ) (σ σ' : Env) : Prop :=
  Trail a t cap n (h + 1) (upd g h (σ.vars x)) σ'

/-- What an `unwind` needs: the trail, the companion as an indicator,
and a saved height in `tb` that the trail has not gone below. -/
abbrev UnwindPre (a t tb b : String) (cap n h base B : ℕ) (g f : ℕ → ℕ) (σ : Env) : Prop :=
  Pre a t cap n h B g σ ∧ Ind b n f σ ∧ σ.vars tb = base ∧ base ≤ h

/-- What `unwind` leaves: the trail at the saved height, and the
companion with everything logged above it undone. -/
abbrev UnwindPost (a t _tb b : String) (cap n h base : ℕ) (g f : ℕ → ℕ) (_σ σ' : Env) :
    Prop :=
  Trail a t cap n base g σ' ∧ Ind b n (undoRange g f base (h - base)) σ' ∧
    σ'.vars t = base

/-- **Recording.** The store's range obligation is the relation's to
answer and the relation is opaque to the walk's discharger, so it is put
into the precondition first, in the array form the walk states it in —
shape note 5. -/
theorem record_spec (B cap n h : ℕ) (a t x : String) (g : ℕ → ℕ) :
    Spec B (RecordPre a t x cap n h B g) (record a t x)
      (RecordPost a t x cap n h g) 7 := by
  refine Spec.pre (P := fun σ => RecordPre a t x cap n h B g σ ∧
      σ.vars t < (σ.arrs a).length ∧ σ.vars t + 1 < B) ?_
    (fun σ hσ => ⟨hσ, by rw [hσ.1.1.height, hσ.1.1.length]; exact hσ.2.1,
      by rw [hσ.1.1.height]; exact hσ.1.2.2⟩)
  run_vcg
  have ht := ‹Trail a t cap n h g σ›
  simp only [vars_setArr, ht.height]
  exact (ht.setTop _).raise (by omega) (by simpa using ‹σ.vars x < n›)

/-! #### The unwind loop

The loop is content, not bookkeeping, so it is proved by hand: an
invariant, a variant that drops by one a turn, and a body specification
the walk produces. `Spec.while_count` assembles the three. -/

/-- The invariant: the saved height is where it was, the trail is at
some height between it and where the unwind started, and the companion
has had exactly the entries above the current height undone. It is an
`abbrev` so that the walk can split it and feed `omega` — shape note
4. -/
abbrev UnwindInv (a t tb b : String) (cap n h base : ℕ) (g f : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars tb = base ∧ base ≤ σ.vars t ∧ σ.vars t ≤ h ∧
    Trail a t cap n (σ.vars t) g σ ∧
    Ind b n (undoRange g f (σ.vars t) (h - σ.vars t)) σ

/-- **One turn.** The height drops by one and the entry it uncovers is
undone in the companion; `undoRange_step` is the whole of it. -/
theorem unwindBody_spec (B cap n h base : ℕ) (a t tb b : String) (g f : ℕ → ℕ)
    (hab : b ≠ a) (htb : tb ≠ t) (hnB : n ≤ B) (hhB : h < B) :
    Spec B (fun σ => UnwindInv a t tb b cap n h base g f σ ∧
        (Cond.lt (.var tb) (.var t)).evalB B σ = some true)
      (unwindBody a t b)
      (fun σ σ' => UnwindInv a t tb b cap n h base g f σ' ∧
        σ'.vars t - base < σ.vars t - base) 8 := by
  refine Spec.pre (P := fun σ => (UnwindInv a t tb b cap n h base g f σ ∧
      base < σ.vars t) ∧
      σ.vars t - 1 < (σ.arrs a).length ∧
      (σ.arrs a).getD (σ.vars t - 1) 0 < B ∧
      (σ.arrs a)[σ.vars t - 1]?.getD 0 < B ∧
      (σ.arrs a).getD (σ.vars t - 1) 0 < (σ.arrs b).length ∧
      (σ.arrs a)[σ.vars t - 1]?.getD 0 < (σ.arrs b).length ∧
      σ.vars t < B ∧ σ.vars tb < B) ?_ ?_
  · run_vcg
    have htbσ : σ.vars tb = base := ‹_›
    have hbase : base ≤ σ.vars t := ‹_›
    have hhσ : σ.vars t ≤ h := ‹_›
    have htr : Trail a t cap n (σ.vars t) g σ := ‹_›
    have hind : Ind b n (undoRange g f (σ.vars t) (h - σ.vars t)) σ := ‹_›
    have hpos : base < σ.vars t := ‹_›
    have hk : ((σ.setVar t (σ.vars t - 1)).arrs a).getD
        ((σ.setVar t (σ.vars t - 1)).vars t) 0 = g (σ.vars t - 1) := by
      have hvt : (σ.setVar t (σ.vars t - 1)).vars t = σ.vars t - 1 := by simp
      rw [arrs_setVar, hvt]
      exact htr.getD (by have := htr.le_cap; omega)
    rw [hk]
    refine ⟨⟨by simp [htb, htbσ], by simp; omega, by simp; omega, ?_, ?_⟩, by simp; omega⟩
    · simpa using (htr.shrink (h' := σ.vars t - 1) (by omega)).setArr_of_ne hab
        (g (σ.vars t - 1)) 0
    · have hstep := undoRange_step g f (t := σ.vars t) (d := h) (by omega) hhσ
      simpa [hstep] using (hind.setVar t (σ.vars t - 1)).setArr (g (σ.vars t - 1)) 0 (by omega)
  · rintro σ ⟨hI, hcond⟩
    have hpos : base < σ.vars t := by
      have := lt_of_condLt_true hcond
      have h1 : σ.vars tb = base := hI.1
      omega
    have htr := hI.2.2.2.1
    have hind := hI.2.2.2.2
    have hlen : σ.vars t - 1 < (σ.arrs a).length := by
      rw [htr.length]; have := htr.le_cap; omega
    have hval : (σ.arrs a).getD (σ.vars t - 1) 0 = g (σ.vars t - 1) :=
      htr.getD (by have := htr.le_cap; omega)
    have hentry : g (σ.vars t - 1) < n := htr.entry (by omega)
    have hind_len : (σ.arrs b).length = n := hind.length
    have hhσ : σ.vars t ≤ h := hI.2.2.1
    have htbσ : σ.vars tb = base := hI.1
    exact ⟨⟨hI, hpos⟩, hlen, by rw [hval]; omega,
      by rw [← List.getD_eq_getElem?_getD, hval]; omega,
      by rw [hval, hind_len]; omega,
      by rw [← List.getD_eq_getElem?_getD, hval, hind_len]; omega,
      by omega, by omega⟩

/-- **Unwinding.** One specification with the loop inside it: from a
trail at height `h` and a companion holding `f`, the loop runs the
height back to the saved `base` and undoes every entry logged above it,
at a cost linear in the entries removed. -/
theorem unwind_spec (B cap n h base : ℕ) (a t tb b : String) (g f : ℕ → ℕ)
    (hab : b ≠ a) (htb : tb ≠ t) (hnB : n ≤ B) (hhB : h < B) :
    Spec B (UnwindPre a t tb b cap n h base B g f) (unwind a t tb b)
      (UnwindPost a t tb b cap n h base g f) (12 * (h - base) + 4) := by
  have hbody := unwindBody_spec B cap n h base a t tb b g f hab htb hnB hhB
  refine (Spec.while_count (b := .lt (.var tb) (.var t))
      (UnwindInv a t tb b cap n h base g f) (fun σ => σ.vars t - base) 8
      (fun σ hI => evalB_condLt_vars (by omega) (by omega)) hbody ?_ ?_).post ?_
  · rintro σ ⟨⟨htr, -, -⟩, hind, htbσ, hbase⟩
    have hheight : σ.vars t = h := htr.height
    exact ⟨htbσ, by omega, by omega, by rw [hheight]; exact htr,
      by rw [hheight]; simpa using hind⟩
  · rintro σ ⟨⟨htr, -, -⟩, -, -, -⟩
    simp only [size_condLt, size_var, htr.height]
    omega
  · rintro σ σ' - ⟨⟨htbσ', hbase', hhσ', htr', hind'⟩, hfalse⟩
    have hle : σ'.vars t ≤ σ'.vars tb := le_of_condLt_false hfalse
    have heq : σ'.vars t = base := by omega
    rw [heq] at htr' hind'
    exact ⟨htr', hind', heq⟩

/-! ### The worked example

Mark two cells, record both on the trail, unwind, and see them come
back. The two `record`s take their value from different scalars because
`run_vcg [·]` matches a handed specification against the command it is
about — see `Stack`'s worked example. -/

namespace Demo

/-- Mark cell one and cell three, log both, then unwind to the saved
height `tb`. This is the two `Lib` modules composing: the marking is
`Ind.mark`, the logging is `Trail.record`, and `unwind` puts the marks
back. -/
def demo (a t tb b x y : String) : Com :=
  .seq (.assign x (.lit 1))
    (.seq (Ind.mark b x)
      (.seq (record a t x)
        (.seq (.assign y (.lit 3))
          (.seq (Ind.mark b y)
            (.seq (record a t y) (unwind a t tb b))))))

/-- The block, by the four specifications and nothing else. The
postcondition is the companion with both entries undone — which, at
the concrete cell functions of the machine run below, is the indicator
it started with. -/
theorem demo_spec (B cap n : ℕ) (a t tb b x y : String) (f g : ℕ → ℕ)
    (hab : b ≠ a) (htb : tb ≠ t) (hxt : x ≠ t) (hyt : y ≠ t) (htbx : tb ≠ x) (htby : tb ≠ y)
    (h1n : 1 < n) (h3n : 3 < n) (h2cap : 2 ≤ cap) (hnB : n ≤ B) (h3B : 3 < B) :
    Spec B (fun σ => Trail a t cap n 0 g σ ∧ Ind b n f σ ∧ σ.vars tb = 0)
      (demo a t tb b x y)
      (fun _ σ' => Ind b n
          (undoRange (upd (upd g 0 1) 1 3) (upd (upd f 1 1) 3 1) 0 2) σ' ∧
        σ'.vars t = 0) 52 := by
  run_vcg [(Ind.mark_spec B n b x f (by omega)).frame,
      (record_spec B cap n 0 a t x g).frame,
      (Ind.mark_spec B n b y (upd f 1 1) (by omega)).frame,
      (record_spec B cap n 1 a t y (upd g 0 1)).frame,
      (unwind_spec B cap n 2 0 a t tb b (upd (upd g 0 1) 1 3) (upd (upd f 1 1) 3 1)
        hab htb (by omega) (by omega)).frame] <;>
    simp_all [Pre, RecordPost, Ind.MarkPost, UnwindPost, Trail, Ind,
      Ne.symm hab, Ne.symm hxt, Ne.symm hyt] <;>
      omega

/-- The same, with the two marks read out before and after the
unwind. -/
def demoWatched (a t tb b x y r : String) : Com :=
  .seq (.assign x (.lit 1))
    (.seq (Ind.mark b x)
      (.seq (record a t x)
        (.seq (.assign y (.lit 3))
          (.seq (Ind.mark b y)
            (.seq (record a t y)
              (.seq (Ind.test b x r)
                (.seq (.write (.var r))
                  (.seq (Ind.test b y r)
                    (.seq (.write (.var r))
                      (.seq (unwind a t tb b)
                        (.seq (Ind.test b x r)
                          (.seq (.write (.var r))
                            (.seq (Ind.test b y r) (.write (.var r)))))))))))))))

/-- Five scalars, the trail and the mark array, four temporaries (the
deepest expression is the unwind's `mark[trail[tt]] := 0`). -/
def layout : Lax759944Proofs.Legacy.Compile.Layout := ⟨["t", "tb", "x", "y", "r"], ["tr", "mk"], 4⟩

/-- The machine program. -/
def prog : Lax759944Proofs.Legacy.Ram.Program :=
  Lax759944Proofs.Legacy.Compile.compileProgram layout (demoWatched "tr" "t" "tb" "mk" "x" "y" "r")

/-- The layout covers the block, so the compilation is the one the
simulation theorem is about and not an accident. -/
theorem demoWatched_ok :
    Lax759944Proofs.Legacy.Compile.Com.Ok layout (demoWatched "tr" "t" "tb" "mk" "x" "y" "r") := by
  simp [demoWatched, record, unwind, unwindBody, Ind.mark, Ind.test, layout,
    Lax759944Proofs.Legacy.Compile.Com.Ok, Lax759944Proofs.Legacy.Compile.Cond.Ok, Lax759944Proofs.Legacy.Compile.condExpr,
    Lax759944Proofs.Legacy.Compile.Expr.Ok]

/-- Run it: the machine's memory starts zeroed, so the trail starts
empty and the saved height is `0`. Both cells must read `1` before the
unwind and `0` after it. -/
def demoRun : Option (List ℕ × ℕ) := runOut 16 4000 prog (Lax759944Proofs.Legacy.Ram.initState []) 0

#guard demoRun = some ([1, 1, 0, 0], 165)

/-! And the arithmetic on the other side of the abstraction: a trail
holding `[1, 3]`, an indicator with those two cells set, and the
indicator the unwind restores. -/

#guard arrOf 2 (upd (upd (fun _ => 0) 0 1) 1 3) = [1, 3]
#guard arrOf 4 (upd (upd (fun _ => 0) 1 1) 3 1) = [0, 1, 0, 1]
#guard arrOf 4 (undoRange (upd (upd (fun _ => 0) 0 1) 1 3)
  (upd (upd (fun _ => 0) 1 1) 3 1) 0 2) = [0, 0, 0, 0]

end Demo

end Trail

end Lax759944Proofs.Legacy.Reasoning.Lib
