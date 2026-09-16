-- Adapted 2026-09-15 from word-ram-v4-33 at 0aa87e1f6e6add4abe4f4e0aff8fe4a28950b2ea.
-- Namespace relocated for use as a proof-only intermediate; semantics unchanged.
import Lax759944Proofs.Legacy.Lib.Basic

/-!
An array filled cell by cell by a counter: the array, a scalar counting
how much of it is done, and the promise that everything below the
counter already holds what it should.

This is what a *pass* over an array leaves behind, and the repo is full
of them — Lax11's read loop copying the tape into `off` and into `tgt`,
its `initLab` marking every vertex unvisited, Lax15's two-array
initialisations. Each of them wrote out the same invariant by hand
("`i ≤ n`, and there is a `g` with `arrs a = arrOf n g` and `∀ j < i,
g j = F j`"), the same one-turn extension of it, and the same reading of
it at the exit. Here that is proved once.

The module is the counterpart of `Spec.forRangeZero`, not a competitor:
that rule owns the loop, this one owns what the loop's body does to the
array, and `loop_spec` at the end is the two of them put together — the
whole phase `x := 0; while x < m do (a[x] := e; x := x + 1)` as one
specification, at a cost of `(10 + e.size) · n + 6`.

### Two forms of the relation

`Fill a x n i g F σ` names the cell function `g` and the counter's value
`i`, as `Stack` names its height: what a *specification* changes has to
be a parameter, since it cannot be recovered from an intermediate state.
`Fill.Below a x n F σ` hides both — the counter is read off `σ` and the
cell function is existentially quantified — and that is the form a *loop
invariant* needs, since neither is fixed over a loop. The operations are
proved in the first form and exported in the second, which is the only
place the two meet.

What is deliberately absent is any statement about the cells at or above
the counter: a fill says nothing about where it has not been yet, so the
caller's precondition is only that the array has the right length.
-/

namespace Lax759944Proofs.Legacy.Reasoning.Lib

open Lax759944Proofs.Legacy.Imp

variable {B n i j k v : ℕ} {a b x y m : String} {g F : ℕ → ℕ} {σ : Env}

/-! ### The relation -/

/-- `Fill a x n i g F σ`: in `σ`, the array named `a` is the length-`n`
array whose cell `j` is `g j`, the counter named `x` holds `i`, the
counter has not passed the end, and every cell below it holds what `F`
says it should. -/
def Fill (a x : String) (n i : ℕ) (g F : ℕ → ℕ) (σ : Env) : Prop :=
  σ.arrs a = arrOf n g ∧ σ.vars x = i ∧ i ≤ n ∧ ∀ j, j < i → g j = F j

/-- The array. -/
theorem Fill.arr (h : Fill a x n i g F σ) : σ.arrs a = arrOf n g := h.1

/-- The counter. -/
theorem Fill.counter (h : Fill a x n i g F σ) : σ.vars x = i := h.2.1

/-- The counter has not passed the end. -/
theorem Fill.le (h : Fill a x n i g F σ) : i ≤ n := h.2.2.1

/-- Everything below the counter is done. -/
theorem Fill.cell (h : Fill a x n i g F σ) (hj : j < i) : g j = F j := h.2.2.2 j hj

/-- The length, which is what a store's range condition asks for. -/
theorem Fill.length (h : Fill a x n i g F σ) : (σ.arrs a).length = n := by
  rw [h.arr, length_arrOf]

/-- Reading a cell. -/
theorem Fill.getD (h : Fill a x n i g F σ) (hj : j < n) : (σ.arrs a).getD j 0 = g j := by
  rw [h.arr, getD_arrOf g hj]

/-- An assignment to any scalar but the counter leaves the fill alone. -/
@[simp] theorem Fill.setVar_iff (a x : String) (n i : ℕ) (g F : ℕ → ℕ) (σ : Env)
    (y : String) (v : ℕ) (hy : y ≠ x) :
    Fill a x n i g F (σ.setVar y v) ↔ Fill a x n i g F σ := by
  simp [Fill, Ne.symm hy]

theorem Fill.setVar (h : Fill a x n i g F σ) (hy : y ≠ x) (v : ℕ) :
    Fill a x n i g F (σ.setVar y v) :=
  (Fill.setVar_iff a x n i g F σ y v hy).2 h

/-- **The transport lemma.** The relation is a statement about one array
and one scalar, so any environment agreeing on those two satisfies it —
which is how a fill crosses a phase that touches neither, off the
equations `Spec.frame` hands the call site. It is also what crosses a
`read`, whose environment is a `setVar` under a new input tape. -/
theorem Fill.of_eq (h : Fill a x n i g F σ) {σ' : Env}
    (harr : σ'.arrs a = σ.arrs a) (hvar : σ'.vars x = σ.vars x) : Fill a x n i g F σ' :=
  ⟨by rw [harr, h.arr], by rw [hvar, h.counter], h.2.2.1, h.2.2.2⟩

/-- A store into another array leaves the fill alone. -/
theorem Fill.setArr_of_ne (h : Fill a x n i g F σ) (hb : b ≠ a) (k v : ℕ) :
    Fill a x n i g F (σ.setArr b k v) :=
  ⟨by rw [arrs_setArr, if_neg (Ne.symm hb), h.arr], h.2.1, h.2.2.1, h.2.2.2⟩

/-- **The one-turn extension**, on the cell functions alone: writing
what `F` says into the cell the counter names extends "everything below
the counter is done" by one. Every fill in the repo re-proved this
`by_cases` inline. -/
theorem upd_below_succ (hv : v = F i) (hg : ∀ j, j < i → g j = F j) (j : ℕ) (hj : j < i + 1) :
    upd g i v j = F j := by
  by_cases hje : j = i
  · simp [hje, hv]
  · rw [upd_of_ne _ hje]; exact hg j (by omega)

/-- **Writing the cell the counter names.** The relation says nothing
about cells at or above the counter, so this asks nothing; it is the
first half of a turn. -/
theorem Fill.setCell (h : Fill a x n i g F σ) (v : ℕ) :
    Fill a x n i (upd g i v) F (σ.setArr a i v) :=
  ⟨by rw [arrs_setArr, if_pos rfl, h.arr, set_arrOf_eq_upd], by rw [vars_setArr, h.counter],
   h.2.2.1, fun j hj => by rw [upd_of_ne _ (by omega)]; exact h.cell hj⟩

/-- **Moving the counter up over a finished cell.** The second half of a
turn: the cell the counter is leaving must hold what it should. -/
theorem Fill.bump (h : Fill a x n i g F σ) (hin : i < n) (hgi : g i = F i) :
    Fill a x n (i + 1) g F (σ.setVar x (i + 1)) :=
  ⟨by rw [arrs_setVar, h.arr], by simp, hin, fun j hj => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact h.cell hj
    · exact hgi⟩

/-! Everything from here on is this module's own — the loop-invariant
form of the relation, the operation, its specification and the phase
they add up to — so it lives in the module's namespace. -/

namespace Fill

/-! ### The loop-invariant form

A loop cannot hold the cell function or the counter fixed, so the form
an invariant is stated in has neither: the counter is whatever `σ` says
and the cell function is quantified away. Everything a caller needs of
it comes back out at the exit, when `Spec.forRangeZero` reports the
counter *at* the bound. -/

/-- `Below a x n F σ`: the array `a` has length `n` and everything below
the counter `x` holds what `F` says. -/
def Below (a x : String) (n : ℕ) (F : ℕ → ℕ) (σ : Env) : Prop :=
  ∃ g, Fill a x n (σ.vars x) g F σ

/-- The counter has not passed the end — one of `Spec.forRangeZero`'s
two obligations on an invariant, and free. -/
theorem Below.le (h : Below a x n F σ) : σ.vars x ≤ n := by
  obtain ⟨_, hf⟩ := h; exact hf.le

/-- The length of the array, which is what a store's range condition
asks for. A caller reads it off the invariant rather than opening the
existential. -/
theorem Below.length (h : Below a x n F σ) : (σ.arrs a).length = n := by
  obtain ⟨_, hf⟩ := h; exact hf.length

/-- An array of the right length with the counter at zero is a fill that
has not started: the entry condition of every pass. -/
theorem below_zero (h : σ.arrs a = arrOf n g) (hx : σ.vars x = 0) : Below a x n F σ :=
  ⟨g, h, rfl, by omega, fun j hj => absurd hj (by omega)⟩

/-- **The exit reading.** A pass whose counter has reached the end has
filled the whole array — the form every phase lemma states its
conclusion in. -/
theorem Below.done (h : Below a x n F σ) (hx : σ.vars x = n) :
    ∃ g, σ.arrs a = arrOf n g ∧ ∀ j, j < n → g j = F j := by
  obtain ⟨g, hf⟩ := h
  exact ⟨g, hf.arr, fun j hj => hf.cell (by omega)⟩

/-- Transport, in the invariant form. -/
theorem Below.of_eq (h : Below a x n F σ) {σ' : Env}
    (harr : σ'.arrs a = σ.arrs a) (hvar : σ'.vars x = σ.vars x) : Below a x n F σ' := by
  obtain ⟨g, hf⟩ := h
  refine ⟨g, ?_⟩
  rw [hvar]
  exact hf.of_eq harr hvar

/-- **One turn, on the state.** Write `v` — which has to be what `F`
says about the cell the counter names — and move the counter up. This is
`setCell` and `bump` in the form a hand-written body proof wants, with
no cell function to name. -/
theorem Below.step (h : Below a x n F σ) (hlt : σ.vars x < n) (hv : v = F (σ.vars x)) :
    Below a x n F ((σ.setArr a (σ.vars x) v).setVar x (σ.vars x + 1)) := by
  obtain ⟨g, hf⟩ := h
  refine ⟨upd g (σ.vars x) v, ?_⟩
  rw [show ((σ.setArr a (σ.vars x) v).setVar x (σ.vars x + 1)).vars x = σ.vars x + 1 by simp]
  exact (hf.setCell v).bump hlt (by simp [hv])

/-! ### The operation

One command, parameterized in the array, the counter and the expression
whose value is filled in. It is a store and a bump, which is what every
fill in the repo already writes; its cost is `6 + e.size`, the store's
`2 + e.size` and the bump's `4`. -/

/-- Put the value of `e` into the cell the counter `x` names, and move
the counter up. -/
def put (a x : String) (e : Expr) : Com :=
  .seq (.store a (.var x) e) (.assign x (.add (.var x) (.lit 1)))

/-! The frame conditions, as `simp` lemmas: a call site's array and
counter are bound variables, so `Spec.frame`'s obligations are
discharged there by `simp` and not by `decide`. -/

@[simp] theorem wvars_put (a x : String) (e : Expr) : (put a x e).wvars = [x] := by
  simp [put, Com.wvars]

@[simp] theorem warrs_put (a x : String) (e : Expr) : (put a x e).warrs = [a] := by
  simp [put, Com.warrs]

@[simp] theorem not_reads_put (a x : String) (e : Expr) : ¬ (put a x e).reads := by
  simp [put, Com.reads]

@[simp] theorem noWrite_put (a x : String) (e : Expr) : (put a x e).NoWrite := by
  simp [put, Com.NoWrite]

/-! ### The specification -/

/-- What a turn leaves: the fill one cell longer, and the counter one
higher. -/
abbrev PutPost (a x : String) (n : ℕ) (F : ℕ → ℕ) (σ σ' : Env) : Prop :=
  Below a x n F σ' ∧ σ'.vars x = σ.vars x + 1

/-- **One turn.** The caller's precondition is its own — a loop
invariant carries more than the fill — so it is a parameter, and what is
asked of it is exactly what a turn needs: that it contains the fill with
the counter still inside the array, and that it makes `e` evaluate to
what `F` says the cell should hold. The counter's own bound is not asked
for: it is below `n`, and `n` is below `B`.

The store's range obligation is the relation's to answer and the
relation is opaque to the walk's discharger, so it is discharged here
rather than left to a caller — this specification is what shape note 5
saves every site. -/
theorem put_spec (B n : ℕ) (a x : String) (e : Expr) (F : ℕ → ℕ) (P : Env → Prop)
    (hP : ∀ σ, P σ → Below a x n F σ ∧ σ.vars x < n) (hnB : n < B)
    (he : ∀ σ, P σ → e.evalB B σ = some (F (σ.vars x))) :
    Spec B P (put a x e) (PutPost a x n F) (6 + e.size) := by
  intro σ hσ
  obtain ⟨hb, hlt⟩ := hP σ hσ
  obtain ⟨g, hf⟩ := hb
  refine ⟨_, (Run.seq (Run.store (idx := σ.vars x) (v := F (σ.vars x))
        (evalB_var (by omega)) (he σ hσ) (by rw [hf.length]; omega))
      (Run.assign (v := σ.vars x + 1) ?_)).mono (by simp; omega), ?_, by simp⟩
  · rw [evalB_bin (evalB_var (by simp; omega)) (evalB_lit (by omega)) (by simp; omega)]
    simp [Bop.apply]
  · exact Below.step ⟨g, hf⟩ hlt rfl

/-! ### The phase

The loop and its body together: `Spec.forRangeZero` owns the counter and
the cost, `put_spec` owns the array, and what is left for the caller is
the one thing neither can know — what the cell it is filling in should
hold. -/

/-- **Filling an array by a counter loop**: `x := 0; while x < m do
(a[x] := e; x := x + 1)`, where `m` holds the length. All that is asked
at entry is that the array *has* that length; all that comes back is
that every cell of it holds what `F` says. A turn costs `6 + e.size`, so
the phase costs `(10 + e.size) · n + 6`. -/
theorem loop_spec (B n : ℕ) (a x m : String) (e : Expr) (F : ℕ → ℕ)
    (hxm : x ≠ m) (hnB : n < B)
    (he : ∀ σ, Below a x n F σ → σ.vars m = n → σ.vars x < n →
      e.evalB B σ = some (F (σ.vars x))) :
    Spec B (fun σ => (∃ g, σ.arrs a = arrOf n g) ∧ σ.vars m = n)
      (.seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) (put a x e)))
      (fun _ σ' => (∃ g, σ'.arrs a = arrOf n g ∧ ∀ j, j < n → g j = F j) ∧ σ'.vars x = n)
      ((10 + e.size) * n + 6) := by
  have hbody : Spec B (fun σ => (Below a x n F σ ∧ σ.vars m = n) ∧ σ.vars x < n) (put a x e)
      (fun σ σ' => (Below a x n F σ' ∧ σ'.vars m = n) ∧ σ'.vars x = σ.vars x + 1)
      (6 + e.size) :=
    ((put_spec B n a x e F _ (fun _ hσ => ⟨hσ.1.1, hσ.2⟩) hnB
      (fun _ hσ => he _ hσ.1.1 hσ.1.2 hσ.2)).frame).post
      (fun _ _ hσ hq => ⟨⟨hq.1.1, by rw [hq.2.1 m (by simp [Ne.symm hxm]), hσ.1.2]⟩, hq.1.2⟩)
  refine ((Spec.forRangeZero x m (fun σ => Below a x n F σ ∧ σ.vars m = n) n (6 + e.size) hnB
    (fun _ hσ => hσ.1.le) (fun _ hσ => hσ.2) hbody).pre ?_).post ?_ |>.mono (by ring_nf; omega)
  · rintro σ ⟨⟨g, harr⟩, hm⟩
    exact ⟨below_zero (by rw [arrs_setVar]; exact harr) (by simp), by simp [Ne.symm hxm, hm]⟩
  · exact fun _ σ' _ hq => ⟨hq.1.1.done hq.2, hq.2⟩

/-! ### The worked example

Fill a three-cell array with the counter's own value, then write the
three cells out. `demo` is the phase the specification is about;
`demoWatched` is the same phase with the reads appended, so that the
machine can be seen doing it. -/

namespace Demo

/-- Fill `a` with the identity, up to what `m` holds. -/
def demo (a x m : String) : Com :=
  .seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) (put a x (.var x)))

/-- The phase, by `loop_spec` and nothing else: what is left for the
example is that the value stored — the counter — is what the identity
says about the cell the counter names. -/
theorem demo_spec (B n : ℕ) (a x m : String) (hxm : x ≠ m) (hnB : n < B) :
    Spec B (fun σ => (∃ g, σ.arrs a = arrOf n g) ∧ σ.vars m = n) (demo a x m)
      (fun _ σ' => (∃ g, σ'.arrs a = arrOf n g ∧ ∀ j, j < n → g j = j) ∧ σ'.vars x = n)
      (11 * n + 6) :=
  loop_spec B n a x m (.var x) id hxm hnB (fun _ _ _ hlt => evalB_var (by omega))

/-- The same, with the three cells written out. -/
def demoWatched (a x m : String) : Com :=
  .seq (.assign m (.lit 3))
    (.seq (demo a x m)
      (.seq (.write (.get a (.lit 0)))
        (.seq (.write (.get a (.lit 1))) (.write (.get a (.lit 2))))))

/-- Two scalars, one array, two temporaries. -/
def layout : Lax759944Proofs.Legacy.Compile.Layout := ⟨["i", "m"], ["ar"], 2⟩

/-- The machine program. -/
def prog : Lax759944Proofs.Legacy.Ram.Program :=
  Lax759944Proofs.Legacy.Compile.compileProgram layout (demoWatched "ar" "i" "m")

/-- The layout covers the block, so the compilation is the one the
simulation theorem is about and not an accident. -/
theorem demoWatched_ok : Lax759944Proofs.Legacy.Compile.Com.Ok layout (demoWatched "ar" "i" "m") := by
  simp [demoWatched, demo, put, layout, Lax759944Proofs.Legacy.Compile.Com.Ok,
    Lax759944Proofs.Legacy.Compile.Cond.Ok, Lax759944Proofs.Legacy.Compile.condExpr, Lax759944Proofs.Legacy.Compile.Expr.Ok]

/-- Run it: the machine's memory starts zeroed, and the pass writes the
counter into each cell, so the three readings must be `0`, `1`, `2`. -/
def demoRun : Option (List ℕ × ℕ) := runOut 16 1000 prog (Lax759944Proofs.Legacy.Ram.initState []) 0

#guard demoRun = some ([0, 1, 2], 108)

/-! And the arithmetic on the other side of the abstraction: three turns
of a fill with the identity. -/

#guard arrOf 3 (upd (upd (upd (fun _ => 0) 0 0) 1 1) 2 2) = [0, 1, 2]

end Demo

end Fill

end Lax759944Proofs.Legacy.Reasoning.Lib
