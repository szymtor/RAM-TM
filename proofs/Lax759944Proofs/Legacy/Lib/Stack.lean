-- Adapted 2026-09-15 from word-ram-v4-33 at 0aa87e1f6e6add4abe4f4e0aff8fe4a28950b2ea.
-- Namespace relocated for use as a proof-only intermediate; semantics unchanged.
import Lax759944Proofs.Legacy.Lib.Basic

/-!
A stack of numbers: a backing array holding the entries bottom-first,
and a scalar holding how many there are.

This is the shape of every search stack in the repo — Lax11's frame
stack in the vertex-cover driver (`stkU`, `stkV`, `stkP` with `top`) and
Lax15's in rung B (`stkV`, `stkB`, `stkT`, `stkP`, again with `top`) —
and both spell out by hand what a push does to the array and what a pop
leaves behind. Here that is proved once, and the three operations are
exported as specifications over `Com` definitions parameterized in the
array and the count they touch.

### The relation, and why it is not a `List`

The plan's table describes this module as "`List α` as array + count",
and `Ind`'s header has already recorded why the relation itself is
stated over `arrOf` and a cell function instead: a relation a downstream
`simp` chews on every line must be cheap. `Stack a t cap V h f σ` is an
equation between two lists, two scalar equations and a bounded `∀`.

The list is not lost, it is *derived*: `Stack.toList h f` is the first
`h` cells, top at the end, and `toList_succ` / `toList_dropLast` /
`toList_getLast` move a push, a pop and a peek across it. Top at the end
is the consumers' own convention — both drivers store their frames
bottom-up and read the top one at index `top - 1`, `frames.reverse[i]`
being the `i`-th cell.

Three parameters ride in the relation, each for a reason the operations
force.

* **`cap`, the backing array's length.** A push stores at index `h`, and
  the store's range obligation is `h < (σ.arrs a).length`; without the
  length in the relation the caller would owe that in array form at
  every call site.
* **`V`, a bound on the entries.** This is `Ind`'s bit condition in
  general form. A pop and a peek *read* a cell, so they owe `f i < B`,
  and the relation is opaque to the walk's discharger; carrying the
  bound pointwise means the caller supplies `V ≤ B` once — `Stack.lt` —
  instead of an array-form obligation per read. Consumers instantiate
  `V` with what they already know: `n` for a vertex, `k + 1` for a
  budget, `2` for a phase bit.
* **`h`, the height, as a parameter rather than `σ.vars t`.** The height
  is what a specification's postcondition has to *change*, and a
  composite states it as a parameter — the P3 note's warning: an
  abstract parameter cannot be recovered from an intermediate state.

### Pre-loading a read

Shape note 5 with one refinement the walk forces. A read whose index is
*not* the initial state's — `pop` decrements the height first — leaves
its value obligation to the discharger's `simp` pass, which normalizes
`List.getD` into `l[i]?.getD`. So the pre-loaded conjunct is given in
both forms, `(σ.arrs a).getD i 0 < B` and `(σ.arrs a)[i]?.getD 0 < B`,
the second by `List.getD_eq_getElem?_getD` off the first, and both are
packaged with the rest of a top-cell read's obligations as `TopRead`, so
that `pop` and `peek` pay for them once between them. `Queue` and `Csr`
will read the same way and want the same pair.

### Cells above the top are not constrained

A pop lowers the count and leaves the cell where it was, which is what
both drivers do, so the relation says nothing about cells at or above
`h`. That is also what lets `Stack.setTop` write one without disturbing
anything, and `Stack.raise` then take it into the stack.

### Parallel stacks

Neither consumer has a single-array stack: both have three or four
arrays sharing one count, pushed together. `push` is the single-array
operation, so a parallel push is not four `push`es — it is one raw
`.store` per array, which `run_vcg` walks, followed by one bump. The two
relation lemmas that step is made of are exported for exactly that use:
`Stack.setTop` for the store and `Stack.raise` for the bump. Whether the
retrofit wants a tuple-shaped module on top of them is a question for
P5, which will have the evidence; this module does not guess.
-/

namespace Lax759944Proofs.Legacy.Reasoning.Lib

open Lax759944Proofs.Legacy.Imp

variable {B cap V h h' i v : ℕ} {a t x r y b : String} {f : ℕ → ℕ} {σ : Env}

/-! ### The relation -/

/-- `Stack a t cap V h f σ`: in `σ`, the array named `a` is the
length-`cap` array whose cell `i` is `f i`, the scalar named `t` holds
`h`, the stack fits in the array, and every entry below the top is
smaller than `V`. The entries are `f 0, …, f (h - 1)`, bottom first. -/
def Stack (a t : String) (cap V h : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  σ.arrs a = arrOf cap f ∧ σ.vars t = h ∧ h ≤ cap ∧ ∀ i, i < h → f i < V

/-- The backing array. -/
theorem Stack.arr (hs : Stack a t cap V h f σ) : σ.arrs a = arrOf cap f := hs.1

/-- The count. -/
theorem Stack.height (hs : Stack a t cap V h f σ) : σ.vars t = h := hs.2.1

/-- The stack fits. -/
theorem Stack.le_cap (hs : Stack a t cap V h f σ) : h ≤ cap := hs.2.2.1

/-- Every entry is below the bound. -/
theorem Stack.entry (hs : Stack a t cap V h f σ) (hi : i < h) : f i < V := hs.2.2.2 i hi

/-- The length, which is what a store's range condition asks for. -/
theorem Stack.length (hs : Stack a t cap V h f σ) : (σ.arrs a).length = cap := by
  rw [hs.arr, length_arrOf]

/-- Reading a cell. -/
theorem Stack.getD (hs : Stack a t cap V h f σ) (hi : i < cap) :
    (σ.arrs a).getD i 0 = f i := by
  rw [hs.arr, getD_arrOf f hi]

/-- **Every entry is a word as soon as `V` is**: the reason the bound
belongs in the relation rather than in every precondition, exactly as
`Ind.lt`. -/
theorem Stack.lt (hs : Stack a t cap V h f σ) (hVB : V ≤ B) (hi : i < h) : f i < B :=
  lt_of_lt_of_le (hs.entry hi) hVB

/-- An assignment to any scalar but the count leaves the stack alone. -/
@[simp] theorem Stack.setVar_iff (a t : String) (cap V h : ℕ) (f : ℕ → ℕ) (σ : Env)
    (y : String) (v : ℕ) (hy : y ≠ t) :
    Stack a t cap V h f (σ.setVar y v) ↔ Stack a t cap V h f σ := by
  simp [Stack, Ne.symm hy]

theorem Stack.setVar (hs : Stack a t cap V h f σ) (hy : y ≠ t) (v : ℕ) :
    Stack a t cap V h f (σ.setVar y v) :=
  (Stack.setVar_iff a t cap V h f σ y v hy).2 hs

/-- **The transport lemma.** The relation is a statement about one
array and one scalar, so any environment that agrees on those two
satisfies it. This is what carries a stack across a phase that touches
neither — the `Rep.of_vars_eq` shape, from the frame conjuncts
`Spec.frame` hands a call site. -/
theorem Stack.of_eq (hs : Stack a t cap V h f σ) {σ' : Env}
    (harr : σ'.arrs a = σ.arrs a) (hvar : σ'.vars t = σ.vars t) :
    Stack a t cap V h f σ' :=
  ⟨by rw [harr, hs.arr], by rw [hvar, hs.height], hs.2.2.1, hs.2.2.2⟩

/-- A store into another array leaves the stack alone. -/
theorem Stack.setArr_of_ne (hs : Stack a t cap V h f σ) (hb : b ≠ a) (k v : ℕ) :
    Stack a t cap V h f (σ.setArr b k v) :=
  ⟨by rw [arrs_setArr, if_neg (Ne.symm hb), hs.arr], hs.2.1, hs.2.2.1, hs.2.2.2⟩

/-- **Writing the cell above the top.** The relation says nothing about
cells at or above the height, so this asks nothing and changes only the
cell function. It is the first half of a push, and the whole of one arm
of a parallel push. -/
theorem Stack.setTop (hs : Stack a t cap V h f σ) (v : ℕ) :
    Stack a t cap V h (upd f h v) (σ.setArr a h v) :=
  ⟨by rw [arrs_setArr, if_pos rfl, hs.arr, set_arrOf_eq_upd], hs.2.1, hs.2.2.1,
   fun i hi => by rw [upd_of_ne _ (by omega)]; exact hs.entry hi⟩

/-- **Taking the cell above the top into the stack.** The second half of
a push: the count moves up, and the new entry has to be within the
bound. -/
theorem Stack.raise (hs : Stack a t cap V h f σ) (hcap : h < cap) (hv : f h < V) :
    Stack a t cap V (h + 1) f (σ.setVar t (h + 1)) :=
  ⟨by rw [arrs_setVar, hs.arr], by simp, hcap, fun i hi => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact hs.entry hi
    · exact hv⟩

/-- **Lowering the count.** A pop, and equally a truncation to any
smaller height: the array does not move, so the entries that stay are
still bounded. -/
theorem Stack.shrink (hs : Stack a t cap V h f σ) (hle : h' ≤ h) :
    Stack a t cap V h' f (σ.setVar t h') :=
  ⟨by rw [arrs_setVar, hs.arr], by simp, le_trans hle hs.le_cap,
   fun i hi => hs.entry (lt_of_lt_of_le hi hle)⟩

/-! Everything from here on is this module's own — its list view, its
operations, their specifications and its worked example — so it lives in
the module's namespace. -/

namespace Stack

/-! ### The list view

Derived, on top of the relation and never inside it. `toList h f` is the
stack as the plan's table names it, a `List ℕ` with the top at the end,
and it is literally the backing array cut off at the height. -/

/-- The stack as a list, bottom first. -/
def toList (h : ℕ) (f : ℕ → ℕ) : List ℕ := arrOf h f

@[simp] theorem toList_zero (f : ℕ → ℕ) : toList 0 f = [] := by simp [toList, arrOf]

@[simp] theorem length_toList (h : ℕ) (f : ℕ → ℕ) : (toList h f).length = h := by
  simp [toList]

/-- The list is the array, cut off at the height. -/
theorem toList_eq_take {n : ℕ} (f : ℕ → ℕ) (h : ℕ) (hn : h ≤ n) :
    (arrOf n f).take h = toList h f := by
  refine List.ext_getElem (by simp [toList]; omega) fun i hi _ => ?_
  simp [toList, arrOf]

theorem toList_take (hs : Stack a t cap V h f σ) : (σ.arrs a).take h = toList h f := by
  rw [hs.arr, toList_eq_take f h hs.le_cap]

/-- **A push appends at the end**: the top of the stack is the last
entry of the list. -/
@[simp] theorem toList_succ (h : ℕ) (f : ℕ → ℕ) :
    toList (h + 1) f = toList h f ++ [f h] := by
  simp [toList, arrOf, List.range_succ]

/-- Cells at or above the height do not show in the list, so a `setTop`
is invisible until the count moves. -/
theorem toList_upd (h : ℕ) (f : ℕ → ℕ) (v : ℕ) : toList h (upd f h v) = toList h f := by
  refine List.ext_getElem (by simp) fun i hi _ => ?_
  have hih : i < h := by simpa [toList] using hi
  simp only [toList, arrOf, List.getElem_map, List.getElem_range]
  exact upd_of_ne v (by omega)

/-- What a push does to the list. -/
theorem toList_push (h : ℕ) (f : ℕ → ℕ) (v : ℕ) :
    toList (h + 1) (upd f h v) = toList h f ++ [v] := by
  rw [toList_succ, toList_upd, upd_self]

/-- What a pop does to the list. -/
theorem toList_dropLast (h : ℕ) (f : ℕ → ℕ) : (toList (h + 1) f).dropLast = toList h f := by
  simp [toList_succ]

/-- What a peek reads. -/
theorem toList_getLast (h : ℕ) (f : ℕ → ℕ) : (toList (h + 1) f).getLast (by simp) = f h := by
  simp [toList_succ]

/-! ### The operations

Three commands, each parameterized in the array it uses, the scalar
holding the count, and the scalar the entry comes from or lands in. -/

/-- Push the value of `x` on the stack `a` counted by `t`. -/
def push (a t x : String) : Com :=
  .seq (.store a (.var t) (.var x)) (.assign t (.add (.var t) (.lit 1)))

/-- Take the top entry of the stack `a` off into `r`. -/
def pop (a t r : String) : Com :=
  .seq (.assign t (.sub (.var t) (.lit 1))) (.assign r (.get a (.var t)))

/-- Read the top entry of the stack `a` into `r`, leaving it there. -/
def peek (a t r : String) : Com := .assign r (.get a (.sub (.var t) (.lit 1)))

/-! The frame conditions of the three, as `simp` lemmas: a call site's
array and count are bound variables, so `Spec.frame`'s obligations are
discharged there by `simp` and not by `decide`. -/

@[simp] theorem wvars_push (a t x : String) : (push a t x).wvars = [t] := by
  simp [push, Com.wvars]

@[simp] theorem warrs_push (a t x : String) : (push a t x).warrs = [a] := by
  simp [push, Com.warrs]

@[simp] theorem not_reads_push (a t x : String) : ¬ (push a t x).reads := by
  simp [push, Com.reads]

@[simp] theorem noWrite_push (a t x : String) : (push a t x).NoWrite := by
  simp [push, Com.NoWrite]

@[simp] theorem wvars_pop (a t r : String) : (pop a t r).wvars = [t, r] := by
  simp [pop, Com.wvars]

@[simp] theorem warrs_pop (a t r : String) : (pop a t r).warrs = [] := by
  simp [pop, Com.warrs]

@[simp] theorem not_reads_pop (a t r : String) : ¬ (pop a t r).reads := by
  simp [pop, Com.reads]

@[simp] theorem noWrite_pop (a t r : String) : (pop a t r).NoWrite := by
  simp [pop, Com.NoWrite]

@[simp] theorem wvars_peek (a t r : String) : (peek a t r).wvars = [r] := by
  simp [peek, Com.wvars]

@[simp] theorem warrs_peek (a t r : String) : (peek a t r).warrs = [] := by
  simp [peek, Com.warrs]

@[simp] theorem not_reads_peek (a t r : String) : ¬ (peek a t r).reads := by
  simp [peek, Com.reads]

@[simp] theorem noWrite_peek (a t r : String) : (peek a t r).NoWrite := by
  simp [peek, Com.NoWrite]

/-! ### The specifications -/

/-- What all three operations need: the relation, the entry bound inside
the word bound, and a count that stays a word when it moves. -/
abbrev Pre (a t : String) (cap V h B : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  Stack a t cap V h f σ ∧ V ≤ B ∧ h + 1 < B

/-- What a push needs on top of that: room in the array, and an entry
within the bound. -/
abbrev PushPre (a t x : String) (cap V h B : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  Pre a t cap V h B f σ ∧ h < cap ∧ σ.vars x < V

/-- What a pop and a peek need on top of that: something to read. -/
abbrev TopPre (a t : String) (cap V h B : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  Pre a t cap V h B f σ ∧ 0 < h

/-- What `push` leaves: one entry more, at the old top. -/
abbrev PushPost (a t x : String) (cap V h : ℕ) (f : ℕ → ℕ) (σ σ' : Env) : Prop :=
  Stack a t cap V (h + 1) (upd f h (σ.vars x)) σ'

/-- What `pop` leaves: one entry fewer, and the entry in `r`. -/
abbrev PopPost (a t r : String) (cap V h : ℕ) (f : ℕ → ℕ) (_σ σ' : Env) : Prop :=
  Stack a t cap V (h - 1) f σ' ∧ σ'.vars r = f (h - 1)

/-- What `peek` leaves: the stack, and the top entry in `r`. -/
abbrev PeekPost (a t r : String) (cap V h : ℕ) (f : ℕ → ℕ) (_σ σ' : Env) : Prop :=
  Stack a t cap V h f σ' ∧ σ'.vars r = f (h - 1)

/-- **The obligations of a top-cell read**, in the forms the walk states
them: the index in range, and the cell a word both as a `List.getD` and
in the `getElem?` form the discharger's `simp` normalizes into. Shape
note 5, packaged once because `pop` and `peek` both pay it. -/
abbrev TopRead (a t : String) (cap V h B : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  TopPre a t cap V h B f σ ∧ σ.vars t - 1 < (σ.arrs a).length ∧
    (σ.arrs a).getD (σ.vars t - 1) 0 < B ∧ (σ.arrs a)[σ.vars t - 1]?.getD 0 < B ∧
    σ.vars t + 1 < B

/-- All four come off the relation. -/
theorem topRead_of_pre (hσ : TopPre a t cap V h B f σ) : TopRead a t cap V h B f σ := by
  have hs := hσ.1.1
  have hcap := hs.le_cap
  have hval : (σ.arrs a).getD (σ.vars t - 1) 0 < B := by
    rw [hs.height, hs.getD (by omega)]
    exact hs.lt hσ.1.2.1 (by omega)
  exact ⟨hσ, by rw [hs.height, hs.length]; omega, hval,
    by rwa [← List.getD_eq_getElem?_getD], by rw [hs.height]; exact hσ.1.2.2⟩

/-- And what the read returns. -/
theorem top_getD (hs : Stack a t cap V h f σ) (h0 : 0 < h) :
    (σ.arrs a)[σ.vars t - 1]?.getD 0 = f (h - 1) := by
  have := hs.le_cap
  rw [← List.getD_eq_getElem?_getD, hs.height, hs.getD (by omega)]

/-- **Pushing.** The store's range obligation is the relation's to
answer and the relation is opaque to the walk's discharger, so it is put
into the precondition first, in the array form the walk states it in —
shape note 5. -/
theorem push_spec (B cap V h : ℕ) (a t x : String) (f : ℕ → ℕ) :
    Spec B (PushPre a t x cap V h B f) (push a t x) (PushPost a t x cap V h f) 7 := by
  refine Spec.pre (P := fun σ => PushPre a t x cap V h B f σ ∧
      σ.vars t < (σ.arrs a).length ∧ σ.vars t + 1 < B) ?_
    (fun σ hσ => ⟨hσ, by rw [hσ.1.1.height, hσ.1.1.length]; exact hσ.2.1,
      by rw [hσ.1.1.height]; exact hσ.1.2.2⟩)
  run_vcg
  have hs := ‹Stack a t cap V h f σ›
  simp only [vars_setArr, hs.height]
  exact (hs.setTop _).raise (by omega) (by simpa using ‹σ.vars x < V›)

/-- **Popping.** -/
theorem pop_spec (B cap V h : ℕ) (a t r : String) (f : ℕ → ℕ) (hrt : r ≠ t) :
    Spec B (TopPre a t cap V h B f) (pop a t r) (PopPost a t r cap V h f) 7 := by
  refine Spec.pre (P := TopRead a t cap V h B f) ?_ (fun _ hσ => topRead_of_pre hσ)
  run_vcg
  have hs := ‹Stack a t cap V h f σ›
  refine ⟨?_, by simp [hs.top_getD ‹0 < h›]⟩
  simpa [hs.height] using (hs.shrink (h' := h - 1) (by omega)).setVar hrt
    ((σ.arrs a).getD (h - 1) 0)

/-- **Peeking.** -/
theorem peek_spec (B cap V h : ℕ) (a t r : String) (f : ℕ → ℕ) (hrt : r ≠ t) :
    Spec B (TopPre a t cap V h B f) (peek a t r) (PeekPost a t r cap V h f) 5 := by
  refine Spec.pre (P := TopRead a t cap V h B f) ?_ (fun _ hσ => topRead_of_pre hσ)
  run_vcg
  have hs := ‹Stack a t cap V h f σ›
  exact ⟨hs.setVar hrt _, by simp [hs.top_getD ‹0 < h›]⟩

/-! ### The worked example

Push two entries, look at the top, take it off, look again. The two
pushes take their value from *different* scalars, because `run_vcg [·]`
matches a handed specification against the command it is about: two
`push a t x` in one block are one command, and the first specification
given would be used for both. Two operations on one structure compose
only when they are textually distinguishable — the same warning as
`Ind`'s, from the other side. -/

namespace Demo

/-- Push `5`, push `7`, peek, pop. -/
def demo (a t x y r : String) : Com :=
  .seq (.assign x (.lit 5))
    (.seq (push a t x)
      (.seq (.assign y (.lit 7))
        (.seq (push a t y) (.seq (peek a t r) (pop a t r)))))

/-- The block, by the three specifications and nothing else. The heights
are literals because a specification's cell function and height are fixed
at elaboration — see the last paragraph of `Ind`'s header. Note what the
final relation says: the popped cell still *holds* `7`, since a pop only
lowers the count, and it is the height that puts the cell out of the
stack. -/
theorem demo_spec (B cap V : ℕ) (a t x y r : String) (f : ℕ → ℕ)
    (hxt : x ≠ t) (hyt : y ≠ t) (hrt : r ≠ t) (h5 : 5 < V) (h7 : 7 < V) (hVB : V ≤ B)
    (h2 : 2 < cap) (h3B : 3 < B) :
    Spec B (fun σ => Stack a t cap V 0 f σ) (demo a t x y r)
      (fun _ σ' => σ'.vars r = 7 ∧ Stack a t cap V 1 (upd (upd f 0 5) 1 7) σ') 30 := by
  run_vcg [(push_spec B cap V 0 a t x f).frame,
      (push_spec B cap V 1 a t y (upd f 0 5)).frame,
      (peek_spec B cap V 2 a t r (upd (upd f 0 5) 1 7) hrt).frame,
      (pop_spec B cap V 2 a t r (upd (upd f 0 5) 1 7) hrt).frame] <;>
    simp_all [Pre, PushPost, PeekPost, PopPost] <;> omega

/-- The same, with the three readings written out. -/
def demoWatched (a t x y r : String) : Com :=
  .seq (.assign x (.lit 5))
    (.seq (push a t x)
      (.seq (.assign y (.lit 7))
        (.seq (push a t y)
          (.seq (peek a t r)
            (.seq (.write (.var r))
              (.seq (pop a t r)
                (.seq (.write (.var r))
                  (.seq (peek a t r) (.write (.var r))))))))))

/-- Four scalars, one stack array, two temporaries. -/
def layout : Lax759944Proofs.Legacy.Compile.Layout := ⟨["t", "x", "y", "r"], ["st"], 2⟩

/-- The machine program. -/
def prog : Lax759944Proofs.Legacy.Ram.Program :=
  Lax759944Proofs.Legacy.Compile.compileProgram layout (demoWatched "st" "t" "x" "y" "r")

/-- The layout covers the block, so the compilation is the one the
simulation theorem is about and not an accident. -/
theorem demoWatched_ok :
    Lax759944Proofs.Legacy.Compile.Com.Ok layout (demoWatched "st" "t" "x" "y" "r") := by
  simp [demoWatched, push, pop, peek, layout, Lax759944Proofs.Legacy.Compile.Com.Ok,
    Lax759944Proofs.Legacy.Compile.Expr.Ok]

/-- Run it: the machine's memory starts zeroed, so the count starts at
`0` and the stack starts empty. The peek must see `7`, the pop must take
`7` off, and the second peek must see `5`. -/
def demoRun : Option (List ℕ × ℕ) := runOut 16 1000 prog (Lax759944Proofs.Legacy.Ram.initState []) 0

#guard demoRun = some ([7, 7, 5], 82)

/-! And the same arithmetic on the other side of the abstraction. -/

#guard toList 2 (upd (upd (fun _ => 0) 0 5) 1 7) = [5, 7]
#guard (toList 2 (upd (upd (fun _ => 0) 0 5) 1 7)).getLast? = some 7
#guard (toList 2 (upd (upd (fun _ => 0) 0 5) 1 7)).dropLast = [5]

end Demo

end Stack

end Lax759944Proofs.Legacy.Reasoning.Lib
