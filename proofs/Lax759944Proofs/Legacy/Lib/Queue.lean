-- Adapted 2026-09-15 from word-ram-v4-33 at 0aa87e1f6e6add4abe4f4e0aff8fe4a28950b2ea.
-- Namespace relocated for use as a proof-only intermediate; semantics unchanged.
import Lax759944Proofs.Legacy.Lib.Basic

/-!
A first-in-first-out queue: one backing array holding the entries in
arrival order, and two scalars, a head and a tail.

Both breadth-first searches in the repo are built on one — Lax11's
components driver (`q` with `head`/`tail`, `CC.lean:60-81`) and Lax15's
rung-C solver (`q` with `head`/`tl`, `Program3.lean:293-337`) — and the
two are the same program twice. An enqueue is `q[tail] := w; tail :=
tail + 1`; a turn of the search reads `q[head]` at the top of its body
and does `head := head + 1` at the bottom; and the search itself is
`while head < tail do body`.

### The relation

`Queue a hd tl cap V h t f σ` is `Stack`'s relation with a second
pointer: the array named `a` is `arrOf cap f`, the scalar `hd` holds the
head `h`, the scalar `tl` holds the tail `t`, the window is well formed
(`h ≤ t ≤ cap`), and every entry that has ever been enqueued is smaller
than `V`. The live entries are `f h, …, f (t - 1)`, oldest first.

Three points, each forced by the consumers.

* **The entry bound runs over `i < t`, not over the live window.**
  Neither consumer ever overwrites a cell: the queue is *not* circular
  and is not reset between searches — Lax11's header says so in as many
  words, and rung C's says it again — so the head simply walks up
  through the array and the consumed entries stay where they are. Both
  invariants therefore read `∀ i < tail, Q i < n`, and that is what is
  stated here. Cells at or above the tail are unconstrained, exactly as
  in `Stack`.
* **`h` and `t` are parameters, not `σ.vars hd` and `σ.vars tl`.** They
  are what an operation's postcondition has to *change*, and the P3
  note's warning applies: an abstract parameter cannot be recovered from
  an intermediate state.
* **`V`, the entry bound, is `Stack`'s.** A read at the head owes
  `f h < B` and the relation is opaque to the walk's discharger, so the
  bound rides in the relation and the caller supplies `V ≤ B` once.
  Both consumers instantiate it with `n`.

### The operations, and why the plan's `advance` is two

The plan's table names the operations `push`, `advance` and `drain`.
`push` is verbatim what both consumers write. `advance` is not: in both
of them the read at the head and the bump of the head are *not
adjacent*, and deliberately so — the whole row scan of the dequeued
vertex sits between them, so that "everything before `head` has been
expanded" is an invariant of the scan too. Lax11's comment on
`expandBody` states the reason; rung C's `expandBody3` repeats it.

So the plan's `advance` ships as its two halves, `front` (read the head
cell into a scalar, moving nothing) and `advance` (move the head on,
reading nothing), and a caller whose two halves *are* adjacent writes
`.seq (front a hd r) (advance hd)` and hands `run_vcg` both
specifications. A combined `dequeue` would have been an export no
consumer can use.

### `drain`, and why it is a combinator with the body left open

`drain hd tl c` is `while head < tail do c`, and both consumers have it
as a self-contained loop: `CC.drain` and `Program3.drain3`. What they do
*not* have in common is the body, which in each case is the algorithm —
a full CSR row scan with enqueues. So the body cannot be the module's,
and `drain_spec` takes it as a parameter, in the same shape
`Spec.while_potential` takes it: an invariant, a potential, and a step
obligation with an existential cost. That is not a stylistic choice —
the cost of a turn is the dequeued vertex's degree, so no constant per
turn bounds it, and `Spec.while_count` (which is what `Trail.unwind`
uses) cannot state it.

What the combinator adds over `Spec.while_potential`, and the reason it
is worth exporting, is the two things both consumers hand-derive around
their loop: the loop condition is *defined* — which comes off the
relation, since `h ≤ t ≤ cap < B` — and the exit says `head = tail`
rather than leaving a false `evalB` to be read again. The step
obligation is likewise stated with `σ.vars hd < σ.vars tl` instead of
that condition's truth, which is the `simp at hc; omega` both consumers
open their step proof with.
-/

namespace Lax759944Proofs.Legacy.Reasoning.Lib

open Lax759944Proofs.Legacy.Imp

variable {B cap V h t i v : ℕ} {a hd tl x r y b : String} {f : ℕ → ℕ} {σ : Env}

/-! ### The relation -/

/-- `Queue a hd tl cap V h t f σ`: in `σ`, the array named `a` is the
length-`cap` array whose cell `i` is `f i`, the scalar named `hd` holds
the head `h`, the scalar named `tl` holds the tail `t`, the window is
well formed and fits in the array, and every entry enqueued so far is
smaller than `V`. The live entries are `f h, …, f (t - 1)`, oldest
first. -/
def Queue (a hd tl : String) (cap V h t : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  σ.arrs a = arrOf cap f ∧ σ.vars hd = h ∧ σ.vars tl = t ∧ h ≤ t ∧ t ≤ cap ∧
    ∀ i, i < t → f i < V

/-- The backing array. -/
theorem Queue.arr (hq : Queue a hd tl cap V h t f σ) : σ.arrs a = arrOf cap f := hq.1

/-- The head. -/
theorem Queue.head (hq : Queue a hd tl cap V h t f σ) : σ.vars hd = h := hq.2.1

/-- The tail. -/
theorem Queue.tail (hq : Queue a hd tl cap V h t f σ) : σ.vars tl = t := hq.2.2.1

/-- The window is well formed. -/
theorem Queue.le (hq : Queue a hd tl cap V h t f σ) : h ≤ t := hq.2.2.2.1

/-- The queue fits. -/
theorem Queue.le_cap (hq : Queue a hd tl cap V h t f σ) : t ≤ cap := hq.2.2.2.2.1

/-- Every entry enqueued so far is below the bound. -/
theorem Queue.entry (hq : Queue a hd tl cap V h t f σ) (hi : i < t) : f i < V :=
  hq.2.2.2.2.2 i hi

/-- The length, which is what a store's range condition asks for. -/
theorem Queue.length (hq : Queue a hd tl cap V h t f σ) : (σ.arrs a).length = cap := by
  rw [hq.arr, length_arrOf]

/-- Reading a cell. -/
theorem Queue.getD (hq : Queue a hd tl cap V h t f σ) (hi : i < cap) :
    (σ.arrs a).getD i 0 = f i := by
  rw [hq.arr, getD_arrOf f hi]

/-- **Every entry is a word as soon as `V` is**: the reason the bound
belongs in the relation rather than in every precondition, exactly as
`Ind.lt` and `Stack.lt`. -/
theorem Queue.lt (hq : Queue a hd tl cap V h t f σ) (hVB : V ≤ B) (hi : i < t) : f i < B :=
  lt_of_lt_of_le (hq.entry hi) hVB

/-- **The two pointers are two scalars.** A queue with something on it
cannot have its head and its tail be the same name, so `advance` asks
the caller nothing. -/
theorem Queue.ne_of_lt (hq : Queue a hd tl cap V h t f σ) (hlt : h < t) : hd ≠ tl := by
  rintro rfl
  have h₁ := hq.head
  have h₂ := hq.tail
  omega

/-- An assignment to any scalar but the two pointers leaves the queue
alone. -/
@[simp] theorem Queue.setVar_iff (a hd tl : String) (cap V h t : ℕ) (f : ℕ → ℕ) (σ : Env)
    (y : String) (v : ℕ) (hyh : y ≠ hd) (hyt : y ≠ tl) :
    Queue a hd tl cap V h t f (σ.setVar y v) ↔ Queue a hd tl cap V h t f σ := by
  simp [Queue, Ne.symm hyh, Ne.symm hyt]

theorem Queue.setVar (hq : Queue a hd tl cap V h t f σ) (hyh : y ≠ hd) (hyt : y ≠ tl) (v : ℕ) :
    Queue a hd tl cap V h t f (σ.setVar y v) :=
  (Queue.setVar_iff a hd tl cap V h t f σ y v hyh hyt).2 hq

/-- **The transport lemma.** The relation is a statement about one array
and two scalars, so any environment that agrees on those three satisfies
it. This is what carries a queue across a phase that touches none of
them — in both consumers, across the marking and labelling stores. -/
theorem Queue.of_eq (hq : Queue a hd tl cap V h t f σ) {σ' : Env}
    (harr : σ'.arrs a = σ.arrs a) (hhd : σ'.vars hd = σ.vars hd)
    (htl : σ'.vars tl = σ.vars tl) : Queue a hd tl cap V h t f σ' :=
  ⟨by rw [harr, hq.arr], by rw [hhd, hq.head], by rw [htl, hq.tail],
   hq.2.2.2.1, hq.2.2.2.2.1, hq.2.2.2.2.2⟩

/-- A store into another array leaves the queue alone. -/
theorem Queue.setArr_of_ne (hq : Queue a hd tl cap V h t f σ) (hb : b ≠ a) (k v : ℕ) :
    Queue a hd tl cap V h t f (σ.setArr b k v) :=
  ⟨by rw [arrs_setArr, if_neg (Ne.symm hb), hq.arr], hq.2.1, hq.2.2.1,
   hq.2.2.2.1, hq.2.2.2.2.1, hq.2.2.2.2.2⟩

/-- **Writing the cell at the tail.** The relation says nothing about
cells at or above the tail, so this asks nothing and changes only the
cell function. It is the first half of a push, and the whole of one arm
of a push onto several parallel queues. -/
theorem Queue.setBack (hq : Queue a hd tl cap V h t f σ) (v : ℕ) :
    Queue a hd tl cap V h t (upd f t v) (σ.setArr a t v) :=
  ⟨by rw [arrs_setArr, if_pos rfl, hq.arr, set_arrOf_eq_upd], hq.2.1, hq.2.2.1,
   hq.2.2.2.1, hq.2.2.2.2.1, fun i hi => by rw [upd_of_ne _ (by omega)]; exact hq.entry hi⟩

/-- **Taking that cell into the queue.** The second half of a push: the
tail moves up, and the new entry has to be within the bound. -/
theorem Queue.bump (hq : Queue a hd tl cap V h t f σ) (hdt : hd ≠ tl) (hcap : t < cap)
    (hv : f t < V) : Queue a hd tl cap V h (t + 1) f (σ.setVar tl (t + 1)) :=
  ⟨by rw [arrs_setVar, hq.arr], by rw [vars_setVar, if_neg hdt]; exact hq.head, by simp,
   by have := hq.le; omega, hcap, fun i hi => by
     rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
     · exact hq.entry hi
     · exact hv⟩

/-- **Moving the head on.** The consumed entry stays in the array —
nothing reads it again — so this is the whole of a dequeue as far as the
relation is concerned. -/
theorem Queue.step (hq : Queue a hd tl cap V h t f σ) (hlt : h < t) :
    Queue a hd tl cap V (h + 1) t f (σ.setVar hd (h + 1)) :=
  ⟨by rw [arrs_setVar, hq.arr], by simp,
   by rw [vars_setVar, if_neg (Ne.symm (hq.ne_of_lt hlt))]; exact hq.tail,
   hlt, hq.le_cap, hq.2.2.2.2.2⟩

/-! Everything from here on is this module's own — its list view, its
operations, their specifications and its worked example — so it lives in
the module's namespace. `Stack.push` and `Queue.push` are why. -/

namespace Queue

/-! ### The list view

Derived, on top of the relation and never inside it. `toList h t f` is
the live window, oldest entry first: the queue as the plan's table names
it. -/

/-- The live entries, oldest first. -/
def toList (h t : ℕ) (f : ℕ → ℕ) : List ℕ := arrOf (t - h) (fun i => f (h + i))

@[simp] theorem length_toList (h t : ℕ) (f : ℕ → ℕ) : (toList h t f).length = t - h := by
  simp [toList]

/-- An empty queue is the empty list — the exit condition of a drain. -/
@[simp] theorem toList_self (t : ℕ) (f : ℕ → ℕ) : toList t t f = [] := by simp [toList, arrOf]

/-- **A push appends at the far end.** With `toList_step` below — which
takes from the near one — this is first-in-first-out, and the contrast
with `Stack`, whose `toList_succ` appends where its `peek` reads. -/
theorem toList_push (h t : ℕ) (f : ℕ → ℕ) (v : ℕ) (hle : h ≤ t) :
    toList h (t + 1) (upd f t v) = toList h t f ++ [v] := by
  refine List.ext_getElem (by simp; omega) fun i hi _ => ?_
  simp only [length_toList] at hi
  by_cases hit : i = t - h
  · simp [toList, arrOf, hit, List.getElem_append_right, show h + (t - h) = t by omega]
  · rw [List.getElem_append_left (by simp; omega)]
    simp [toList, arrOf, upd_of_ne _ (show h + i ≠ t by omega)]

/-- What `front` reads and what `advance` leaves, in one equation. -/
theorem toList_step (h t : ℕ) (f : ℕ → ℕ) (hlt : h < t) :
    toList h t f = f h :: toList (h + 1) t f := by
  refine List.ext_getElem (by simp; omega) fun i hi _ => ?_
  cases i with
  | zero => simp [toList, arrOf]
  | succ i =>
      simp only [List.getElem_cons_succ]
      simp [toList, arrOf, show h + (i + 1) = h + 1 + i by omega]

/-! ### The operations

Four commands: the array, the two pointers and the scalar an entry comes
from or lands in are all parameters, and `drain`'s body is a parameter
too. `front` and `advance` are the plan's `advance` in its two halves —
see this file's header. -/

/-- Put the value of `x` at the back of the queue `a` whose tail is
`tl`. -/
def push (a tl x : String) : Com :=
  .seq (.store a (.var tl) (.var x)) (.assign tl (.add (.var tl) (.lit 1)))

/-- Read the entry at the front of the queue `a` into `r`, moving
nothing. -/
def front (a hd r : String) : Com := .assign r (.get a (.var hd))

/-- Take the front entry off, reading nothing. -/
def advance (hd : String) : Com := .assign hd (.add (.var hd) (.lit 1))

/-- Run `c` until the queue is empty. The body is the caller's: in both
consumers it is the expansion of the dequeued vertex, and it is what
moves the head. -/
def drain (hd tl : String) (c : Com) : Com := .while (.lt (.var hd) (.var tl)) c

/-! The frame conditions of the three straight-line operations, as `simp`
lemmas: a call site's array and pointers are bound variables, so
`Spec.frame`'s obligations are discharged there by `simp` and not by
`decide`. `drain`'s are the body's, so they are stated in terms of it. -/

@[simp] theorem wvars_push (a tl x : String) : (push a tl x).wvars = [tl] := by
  simp [push, Com.wvars]

@[simp] theorem warrs_push (a tl x : String) : (push a tl x).warrs = [a] := by
  simp [push, Com.warrs]

@[simp] theorem not_reads_push (a tl x : String) : ¬ (push a tl x).reads := by
  simp [push, Com.reads]

@[simp] theorem noWrite_push (a tl x : String) : (push a tl x).NoWrite := by
  simp [push, Com.NoWrite]

@[simp] theorem wvars_front (a hd r : String) : (front a hd r).wvars = [r] := by
  simp [front, Com.wvars]

@[simp] theorem warrs_front (a hd r : String) : (front a hd r).warrs = [] := by
  simp [front, Com.warrs]

@[simp] theorem not_reads_front (a hd r : String) : ¬ (front a hd r).reads := by
  simp [front, Com.reads]

@[simp] theorem noWrite_front (a hd r : String) : (front a hd r).NoWrite := by
  simp [front, Com.NoWrite]

@[simp] theorem wvars_advance (hd : String) : (advance hd).wvars = [hd] := by
  simp [advance, Com.wvars]

@[simp] theorem warrs_advance (hd : String) : (advance hd).warrs = [] := by
  simp [advance, Com.warrs]

@[simp] theorem not_reads_advance (hd : String) : ¬ (advance hd).reads := by
  simp [advance, Com.reads]

@[simp] theorem noWrite_advance (hd : String) : (advance hd).NoWrite := by
  simp [advance, Com.NoWrite]

@[simp] theorem wvars_drain (hd tl : String) (c : Com) : (drain hd tl c).wvars = c.wvars := by
  simp [drain, Com.wvars]

@[simp] theorem warrs_drain (hd tl : String) (c : Com) : (drain hd tl c).warrs = c.warrs := by
  simp [drain, Com.warrs]

@[simp] theorem reads_drain_iff (hd tl : String) (c : Com) :
    (drain hd tl c).reads ↔ c.reads := by
  simp [drain, Com.reads]

@[simp] theorem noWrite_drain_iff (hd tl : String) (c : Com) :
    (drain hd tl c).NoWrite ↔ c.NoWrite := by
  simp [drain, Com.NoWrite]

/-! ### The specifications -/

/-- What every operation needs: the relation, the entry bound inside the
word bound, and a tail that stays a word when it moves — which covers
the head too, the window being well formed. -/
abbrev Pre (a hd tl : String) (cap V h t B : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  Queue a hd tl cap V h t f σ ∧ V ≤ B ∧ t + 1 < B

/-- What a push needs on top of that: room in the array, an entry within
the bound, and two pointers that are two scalars — the one thing the
relation cannot supply for a queue that may be empty. -/
abbrev PushPre (a hd tl x : String) (cap V h t B : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  Pre a hd tl cap V h t B f σ ∧ t < cap ∧ σ.vars x < V

/-- What `front` and `advance` need on top of that: something on the
queue. -/
abbrev LivePre (a hd tl : String) (cap V h t B : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  Pre a hd tl cap V h t B f σ ∧ h < t

/-- What `push` leaves: one entry more, at the old tail. -/
abbrev PushPost (a hd tl x : String) (cap V h t : ℕ) (f : ℕ → ℕ) (σ σ' : Env) : Prop :=
  Queue a hd tl cap V h (t + 1) (upd f t (σ.vars x)) σ'

/-- What `front` leaves: the queue, and the oldest entry in `r`. -/
abbrev FrontPost (a hd tl r : String) (cap V h t : ℕ) (f : ℕ → ℕ) (_σ σ' : Env) : Prop :=
  Queue a hd tl cap V h t f σ' ∧ σ'.vars r = f h

/-- What `advance` leaves: the head one on. -/
abbrev AdvancePost (a hd tl : String) (cap V h t : ℕ) (f : ℕ → ℕ) (_σ σ' : Env) : Prop :=
  Queue a hd tl cap V (h + 1) t f σ'

/-- **The obligations of a front read**, in the forms the walk states
them: the index in range, and the cell a word both as a `List.getD` and
in the `getElem?` form the discharger's `simp` normalizes into. Shape
note 5; `Stack.TopRead` is the same package for the other end. -/
abbrev FrontRead (a hd tl : String) (cap V h t B : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  LivePre a hd tl cap V h t B f σ ∧ σ.vars hd < (σ.arrs a).length ∧
    (σ.arrs a).getD (σ.vars hd) 0 < B ∧ (σ.arrs a)[σ.vars hd]?.getD 0 < B ∧
    σ.vars hd < B ∧ σ.vars hd + 1 < B

/-- All of them come off the relation. -/
theorem frontRead_of_pre (hσ : LivePre a hd tl cap V h t B f σ) :
    FrontRead a hd tl cap V h t B f σ := by
  have hq := hσ.1.1
  have hcap := hq.le_cap
  have hval : (σ.arrs a).getD (σ.vars hd) 0 < B := by
    rw [hq.head, hq.getD (by omega)]
    exact hq.lt hσ.1.2.1 hσ.2
  exact ⟨hσ, by rw [hq.head, hq.length]; omega, hval,
    by rwa [← List.getD_eq_getElem?_getD], by rw [hq.head]; omega,
    by rw [hq.head]; have := hσ.1.2.2; omega⟩

/-- And what the read returns. -/
theorem front_getD (hq : Queue a hd tl cap V h t f σ) (hlt : h < t) :
    (σ.arrs a)[σ.vars hd]?.getD 0 = f h := by
  have := hq.le_cap
  rw [← List.getD_eq_getElem?_getD, hq.head, hq.getD (by omega)]

/-- **Pushing.** The store's range obligation is the relation's to
answer and the relation is opaque to the walk's discharger, so it is put
into the precondition first, in the array form the walk states it in —
shape note 5. -/
theorem push_spec (B cap V h t : ℕ) (a hd tl x : String) (f : ℕ → ℕ) (hdt : hd ≠ tl) :
    Spec B (PushPre a hd tl x cap V h t B f) (push a tl x)
      (PushPost a hd tl x cap V h t f) 7 := by
  refine Spec.pre (P := fun σ => PushPre a hd tl x cap V h t B f σ ∧
      σ.vars tl < (σ.arrs a).length ∧ σ.vars tl + 1 < B) ?_
    (fun σ hσ => ⟨hσ, by rw [hσ.1.1.tail, hσ.1.1.length]; exact hσ.2.1,
      by rw [hσ.1.1.tail]; exact hσ.1.2.2⟩)
  run_vcg
  have hq := ‹Queue a hd tl cap V h t f σ›
  simp only [vars_setArr, hq.tail]
  exact (hq.setBack _).bump hdt (by omega) (by simpa using ‹σ.vars x < V›)

/-- **Reading the front.** -/
theorem front_spec (B cap V h t : ℕ) (a hd tl r : String) (f : ℕ → ℕ)
    (hrh : r ≠ hd) (hrt : r ≠ tl) :
    Spec B (LivePre a hd tl cap V h t B f) (front a hd r)
      (FrontPost a hd tl r cap V h t f) 3 := by
  refine Spec.pre (P := FrontRead a hd tl cap V h t B f) ?_ (fun _ hσ => frontRead_of_pre hσ)
  run_vcg
  have hq := ‹Queue a hd tl cap V h t f σ›
  exact ⟨hq.setVar hrh hrt _, by simp [hq.front_getD ‹h < t›]⟩

/-- **Moving the head on.** -/
theorem advance_spec (B cap V h t : ℕ) (a hd tl : String) (f : ℕ → ℕ) :
    Spec B (LivePre a hd tl cap V h t B f) (advance hd)
      (AdvancePost a hd tl cap V h t f) 4 := by
  refine Spec.pre (P := fun σ => LivePre a hd tl cap V h t B f σ ∧ σ.vars hd + 1 < B) ?_
    (fun σ hσ => ⟨hσ, by rw [hσ.1.1.head]; have := hσ.1.2.2; have := hσ.2; omega⟩)
  run_vcg
  have hq := ‹Queue a hd tl cap V h t f σ›
  simpa [hq.head] using hq.step ‹h < t›

/-! #### The drain

The loop is the caller's, body and all — see this file's header. What
the combinator supplies is the loop condition, which the relation
decides, and the exit fact `head = tail`, which the false condition
alone does not give.

It ships in two forms over one proof. `drain_run` is the primitive and
says what `Run.while_potential` says — the cost is the potential's drop
plus the last test — which is what a drain nested inside a further
amortized loop needs, since it has to hand the credit its own potential
still holds on to whoever is paying. `drain_spec` is that with the
credit given up for a constant, which is what a `Spec` has to announce
and what a caller who pays for nothing else wants. Both potentials are
the caller's parameter `Φ`, so neither form exposes anything the other
hides. -/

/-- **Draining the queue, relationally.** From any state satisfying an
invariant that carries a queue, `while head < tail do c` runs to a state
satisfying the invariant with the queue empty, and the cost is bounded
by the potential's *drop* plus the loop's last test.

This is the primitive form, and it is the one a drain that sits inside a
*further* amortized loop needs: an outer loop's turn owes its own
potential a bound on what the inner loop cost, and `K ≤ Φ σ + 4` — what
the `Spec` below announces — throws away the credit `Φ σ'` still holds.
`Run.while_potential` gives the drop and this hands it on; the `Spec` is
the same statement with the exit credit dropped, for a caller who is not
paying anyone else.

The step obligation is `Run.while_potential`'s — existential cost and
all, since the cost of a turn is the dequeued entry's, and no constant
per turn bounds it — with the loop condition already read as an
inequality between the two pointers. -/
theorem drain_run (B cap V : ℕ) (a hd tl : String) (c : Com)
    (I : Env → Prop) (Φ : Env → ℕ)
    (hIQ : ∀ σ, I σ → ∃ f h t, Queue a hd tl cap V h t f σ) (hcapB : cap < B)
    (hstep : ∀ σ, I σ → σ.vars hd < σ.vars tl →
      ∃ σ' K', Run B c σ σ' K' ∧ I σ' ∧ 4 + K' + Φ σ' ≤ Φ σ)
    {σ : Env} (hI : I σ) :
    ∃ σ' K, Run B (drain hd tl c) σ σ' K ∧ I σ' ∧ σ'.vars hd = σ'.vars tl ∧
      K + Φ σ' ≤ Φ σ + 4 := by
  have hbounds : ∀ σ, I σ → σ.vars hd ≤ σ.vars tl ∧ σ.vars tl < B := by
    intro σ hI
    obtain ⟨f, h, t, hq⟩ := hIQ σ hI
    have h₁ := hq.head
    have h₂ := hq.tail
    have h₃ := hq.le
    have h₄ := hq.le_cap
    omega
  obtain ⟨σ', K, hrun, hI', hfalse, hpay⟩ :=
    Run.while_potential (B := B) (b := .lt (.var hd) (.var tl)) (c := c) I Φ
      (fun σ hI => evalB_condLt_vars (by have := hbounds σ hI; omega) (hbounds σ hI).2)
      (fun σ hI hc => by
        obtain ⟨σ', K', hrun, hI', hpay⟩ := hstep σ hI (lt_of_condLt_true hc)
        exact ⟨σ', K', hrun, hI', by simpa using hpay⟩)
      hI
  have h₁ := le_of_condLt_false hfalse
  have h₂ := (hbounds σ' hI').1
  exact ⟨σ', K, hrun, hI', by omega, by simpa using hpay⟩

/-- **Draining the queue.** The same loop as a specification: the cost
is the potential at entry plus the loop's last test, and the exit credit
of `drain_run` is given up in exchange for a constant a caller can
announce. -/
theorem drain_spec (B cap V K : ℕ) (a hd tl : String) (c : Com)
    {P : Env → Prop} (I : Env → Prop) (Φ : Env → ℕ)
    (hIQ : ∀ σ, I σ → ∃ f h t, Queue a hd tl cap V h t f σ) (hcapB : cap < B)
    (hstep : ∀ σ, I σ → σ.vars hd < σ.vars tl →
      ∃ σ' K', Run B c σ σ' K' ∧ I σ' ∧ 4 + K' + Φ σ' ≤ Φ σ)
    (hPI : ∀ σ, P σ → I σ) (hK : ∀ σ, P σ → Φ σ + 4 ≤ K) :
    Spec B P (drain hd tl c) (fun _ σ' => I σ' ∧ σ'.vars hd = σ'.vars tl) K := by
  intro σ hσ
  obtain ⟨σ', K', hrun, hI', hhd, hpay⟩ :=
    drain_run B cap V a hd tl c I Φ hIQ hcapB hstep (hPI σ hσ)
  have := hK σ hσ
  exact ⟨σ', hrun.mono (by omega), hI', hhd⟩

/-! ### The worked example

Enqueue two entries, look at the front, and drain. The two pushes take
their value from *different* scalars, because `run_vcg [·]` matches a
handed specification against the command it is about — see `Stack`'s
worked example, which is this one at the other end of the array: there
the peek sees the entry pushed last, here the front sees the entry
pushed first. -/

namespace Demo

/-- The drain of the example: its body only moves the head, so the loop
empties the queue and nothing else. A real consumer's body expands the
dequeued vertex first; that is the same loop with a bigger `c` and a
bigger potential. -/
theorem drainDemo_spec (B cap V w : ℕ) (a hd tl r : String) (g : ℕ → ℕ)
    (hcapB : cap < B) (h3B : 3 < B) (hVB : V ≤ B) (hrh : r ≠ hd) :
    Spec B (fun σ => Queue a hd tl cap V 0 2 g σ ∧ σ.vars r = w)
      (drain hd tl (advance hd))
      (fun _ σ' => σ'.vars hd = σ'.vars tl ∧ σ'.vars r = w) 20 := by
  refine (drain_spec B cap V 20 a hd tl (advance hd)
    (P := fun σ => Queue a hd tl cap V 0 2 g σ ∧ σ.vars r = w)
    (I := fun σ => Queue a hd tl cap V (σ.vars hd) 2 g σ ∧ σ.vars hd ≤ 2 ∧ σ.vars r = w)
    (Φ := fun σ => 8 * (2 - σ.vars hd))
    (fun σ hI => ⟨g, σ.vars hd, 2, hI.1⟩) hcapB ?_
    (fun σ hσ => ⟨by rw [hσ.1.head]; exact hσ.1, by rw [hσ.1.head]; omega, hσ.2⟩)
    (fun σ _ => show 8 * (2 - σ.vars hd) + 4 ≤ 20 by omega)).post
      (fun _ σ' _ hQ => ⟨hQ.2, hQ.1.2.2⟩)
  intro σ hI hlt
  have hq := hI.1
  have hlt' : σ.vars hd < 2 := by have := hq.tail; omega
  obtain ⟨σ', hrun, hpost⟩ := advance_spec B cap V (σ.vars hd) 2 a hd tl g σ
    ⟨⟨hq, hVB, by omega⟩, hlt'⟩
  have hhd : σ'.vars hd = σ.vars hd + 1 := hpost.head
  have hr : σ'.vars r = σ.vars r := hrun.frame_var r (by simp [hrh])
  refine ⟨σ', 4, hrun, ⟨by rw [hhd]; exact hpost, by omega, by rw [hr]; exact hI.2.2⟩, ?_⟩
  show 4 + 4 + 8 * (2 - σ'.vars hd) ≤ 8 * (2 - σ.vars hd)
  rw [hhd]; omega

/-- Enqueue `5`, enqueue `7`, read the front, drain. -/
def demo (a hd tl x y r : String) : Com :=
  .seq (.assign x (.lit 5))
    (.seq (push a tl x)
      (.seq (.assign y (.lit 7))
        (.seq (push a tl y)
          (.seq (front a hd r) (drain hd tl (advance hd))))))

/-- The block, by the specifications and nothing else. The head sees `5`
— the entry pushed *first* — and the drain leaves the queue empty. The
tails are literals because a specification's cell function and pointers
are fixed at elaboration; see the last paragraph of `Ind`'s header. -/
theorem demo_spec (B cap V : ℕ) (a hd tl x y r : String) (f : ℕ → ℕ)
    (hdt : hd ≠ tl) (hxh : x ≠ hd) (hxt : x ≠ tl) (hyh : y ≠ hd) (hyt : y ≠ tl)
    (hrh : r ≠ hd) (hrt : r ≠ tl) (h5 : 5 < V) (h7 : 7 < V) (hVB : V ≤ B)
    (h2cap : 2 ≤ cap) (hcapB : cap < B) (h3B : 3 < B) :
    Spec B (fun σ => Queue a hd tl cap V 0 0 f σ) (demo a hd tl x y r)
      (fun _ σ' => σ'.vars r = 5 ∧ σ'.vars hd = σ'.vars tl) 41 := by
  run_vcg [(push_spec B cap V 0 0 a hd tl x f hdt).frame,
      (push_spec B cap V 0 1 a hd tl y (upd f 0 5) hdt).frame,
      (front_spec B cap V 0 2 a hd tl r (upd (upd f 0 5) 1 7) hrh hrt).frame,
      (drainDemo_spec B cap V 5 a hd tl r (upd (upd f 0 5) 1 7)
        hcapB (by omega) hVB hrh).frame] <;>
    simp_all [Pre, PushPost, FrontPost] <;> omega

/-- The same, with the front entry and then the whole drained queue
written out. -/
def demoWatched (a hd tl x y r : String) : Com :=
  .seq (.assign x (.lit 5))
    (.seq (push a tl x)
      (.seq (.assign y (.lit 7))
        (.seq (push a tl y)
          (.seq (front a hd r)
            (.seq (.write (.var r))
              (drain hd tl
                (.seq (front a hd r) (.seq (.write (.var r)) (advance hd)))))))))

/-- Five scalars, one queue array, three temporaries. -/
def layout : Lax759944Proofs.Legacy.Compile.Layout := ⟨["hd", "tl", "x", "y", "r"], ["q"], 3⟩

/-- The machine program. -/
def prog : Lax759944Proofs.Legacy.Ram.Program :=
  Lax759944Proofs.Legacy.Compile.compileProgram layout (demoWatched "q" "hd" "tl" "x" "y" "r")

/-- The layout covers the block, so the compilation is the one the
simulation theorem is about and not an accident. -/
theorem demoWatched_ok :
    Lax759944Proofs.Legacy.Compile.Com.Ok layout (demoWatched "q" "hd" "tl" "x" "y" "r") := by
  simp [demoWatched, push, front, advance, drain, layout, Lax759944Proofs.Legacy.Compile.Com.Ok,
    Lax759944Proofs.Legacy.Compile.Cond.Ok, Lax759944Proofs.Legacy.Compile.condExpr, Lax759944Proofs.Legacy.Compile.Expr.Ok]

/-- Run it: the machine's memory starts zeroed, so both pointers start
at `0` and the queue starts empty. The front must read `5`, and the
drain must write the two entries out **in the order they went in** —
which is the whole difference from `Stack`'s example. -/
def demoRun : Option (List ℕ × ℕ) := runOut 16 2000 prog (Lax759944Proofs.Legacy.Ram.initState []) 0

#guard demoRun = some ([5, 5, 7], 111)

/-! And the same arithmetic on the other side of the abstraction: the
queue after the two pushes, what the front reads, and what is left after
one dequeue. -/

#guard toList 0 2 (upd (upd (fun _ => 0) 0 5) 1 7) = [5, 7]
#guard (toList 0 2 (upd (upd (fun _ => 0) 0 5) 1 7)).head? = some 5
#guard toList 1 2 (upd (upd (fun _ => 0) 0 5) 1 7) = [7]

end Demo

end Queue

end Lax759944Proofs.Legacy.Reasoning.Lib
