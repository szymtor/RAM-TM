-- Adapted 2026-09-15 from word-ram-v4-33 at 0aa87e1f6e6add4abe4f4e0aff8fe4a28950b2ea.
-- Namespace relocated for use as a proof-only intermediate; semantics unchanged.
import Lax759944Proofs.Legacy.Lib.Basic

/-!
Indicator arrays: an array of zeros and ones, standing for the set of
positions it holds a one at.

This is the most-used data structure in the repo — Lax11's `mark` array
in the vertex-cover driver, its `seen` array in the connected-components
driver, and both of Lax15's rungs — and every one of them re-derived the
same three facts: that setting a cell to one is inserting into the set,
that setting it to zero is erasing, and that reading a cell tells
membership. Here they are proved once, and the three operations are
exported as specifications over `Com` definitions parameterized in the
names they touch, so that one proof serves `"mark"`, `"seen"` and
`"visited"` alike.

### The relation, and why it is not a `Finset`

The plan's table describes this module as "`Finset (Fin n)` as a 0/1
array". It is not, and the reason is the campaign's own watch item:
an abstraction relation that a downstream `simp` must chew on every
line has to be cheap, and `Finset`/`Multiset` machinery is not. `Ind a
n f σ` is an equation between two lists — `σ.arrs a = arrOf n f` — plus
a bounded `∀`. Nothing in it decides membership, so nothing in it can
be slow.

The set-shaped view is not lost, it is *derived*: `indOf` turns a
decidable predicate into a cell function, and the lemmas below move an
insert or an erase across it, including for a `Finset ℕ`. A consumer
that thinks in sets pairs `Ind a n f σ` with its own reading of `f` —
which is precisely what Lax15's `Rep` already writes,
`τ.arrs "mark" = arrOf n MK ∧ Indicator (marked C.frames) MK`, having
arrived at the same split by hand.

### The shape every `Lib` module follows

This is the first of five (`Stack`, `Trail`, `Queue`, `Csr` follow) and
fixes their common form. Read this list and `Spec.lean` and the next
module writes itself.

0. **One namespace per module inside `Lib`.** Everything a module owns
   — its operations, its `Pre` and its postconditions, its
   specifications, its derived view and its `Demo` — is declared in
   `Lib.Ind`, so that `Lib.Stack.push` and `Lib.Queue.push` can both
   exist and a downstream `open Lax759944Proofs.Legacy.Reasoning.Lib` stays
   collision-free. Only genuinely shared infrastructure sits in `Lib`
   itself, which today is `Basic.lean`'s `upd` and `runOut`. The
   abstraction relation is the one exception: it is *named* for the
   module, so `def Ind` and `namespace Ind` coexist and the relation's
   own lemmas are already `Ind.length`, `Ind.getD`, `Ind.setArr`.

1. **One abstraction relation, a plain `def`, over `arrOf` and a
   pointwise function.** It is what the goals should *show*, not what
   they should unfold to, so it is not an `abbrev`; the facts the
   operations need about it (`Ind.length`, `Ind.getD`, `Ind.setArr`)
   are proved once, next to it, so that no specification proof has to
   unfold it either. Whatever pointwise invariant the structure carries
   — here, that every cell is `0` or `1` — lives *in* the relation, so
   that the value bound of every operation comes out of `1 < B` alone.
   Two of those facts are not optional. A `@[simp] setVar_iff` is what
   carries the relation across the scalar assignments a caller's block
   is full of, and an `of_eq` — the relation holds in any environment
   agreeing on the names it mentions — is what carries it across a
   foreign phase, off the equations `Spec.frame` hands the call site.
   Without both, a composite cannot be closed and the worked example
   does not go through.

2. **Operations are `def`s of type `Com`, parameterized in every name
   they touch.** `mark (a x : String) : Com`, never a fixed `"mark"`.
   This is `readLoop`'s shape — the one piece of machine-level reuse
   this repo already had, used eight times — and it is what makes a
   module reusable at all. Costs are small numerals, read off
   `Expr.size` and checked by the tactic.

3. **Each operation exports one `Spec`, and its `wvars`, `warrs`,
   `reads` and `NoWrite` as `@[simp]`.** The `Spec` is what
   `run_vcg [·]` steps over at a call site. The four `simp` lemmas are
   what `Spec.frame` needs there: the array name is a bound variable,
   not a literal, so `by decide` does not apply and `by simp` must. The
   postcondition therefore says only what the operation *did*, and the
   composition idiom is `run_vcg [(op_spec …).frame, …]` — the frame
   conjuncts arrive as hypotheses in the same step, and `simp_all`
   carries every untouched scalar across.

4. **Pre- and postconditions are `abbrev`s.** `run_vcg` head-normalizes
   the postcondition, so an `abbrev` arrives as a conjunction
   `simp_all` can split and a `def` arrives opaque; on the way in the
   tactic splits the precondition the same way, to feed `omega`. One
   `Pre` per module, shared by its operations, keeps a caller's
   obligations uniform.

5. **An array read pre-loads its two obligations.** The walk owes
   `i < (σ.arrs a).length` and `(σ.arrs a).getD i 0 < B` at every
   `Expr.get`, and its discharger sees the relation as an opaque
   constant, so neither goes. Strengthen the precondition with both, in
   exactly that array form, by `Spec.pre` — `omega` then finds them
   verbatim and the proof stays one `run_vcg` and one `simp_all`. This
   is `test_spec` below, and every `Csr`, `Stack` and `Queue` read will
   want the same three lines.

   Two refinements, both learned from a read whose index is not the
   initial state's. The value bound has to be pre-loaded in **both**
   `getD` forms — `(σ.arrs a).getD i 0 < B` *and*
   `(σ.arrs a)[i]?.getD 0 < B`, the second off the first by
   `List.getD_eq_getElem?_getD` — because the discharger's `simp` pass
   normalizes the one into the other, and a discharger that succeeds on
   only some of a read's obligations comes back as a hard error from
   inside `run_vcg` rather than as a leftover goal. And a scalar bound
   has to be pre-loaded in **state form**, `σ.vars t + 1 < B` and not
   only the relation's `h + 1 < B`: the relation is opaque, so the
   abstract form does not reach `omega`. `Stack.TopRead` and
   `Queue.FrontRead` package both refinements, one per module.

6. **A derived section for the set-shaped view**, never the relation
   itself. `Finset` may appear here and nowhere else.

7. **A worked example, `#guard`-checked through the compiler and the
   machine.** A specification says what a program does; the guard shows
   it. The driver is `Lib.runOut`.

One shape note that is a warning rather than a rule: a specification's
`f` is fixed at elaboration, so two operations compose through
`run_vcg [·]` only when the index is *known* — the worked example
assigns a literal first for that reason. A composite at a symbolic
index is stated with the index as a parameter of the composite, not
recovered from an intermediate state.
-/

namespace Lax759944Proofs.Legacy.Reasoning.Lib

open Lax759944Proofs.Legacy.Imp

variable {B n i k : ℕ} {a x r : String} {f : ℕ → ℕ} {σ : Env}

/-! ### The relation -/

/-- `Ind a n f σ`: in `σ`, the array named `a` is the length-`n` array
whose cell `i` is `f i`, and every cell is `0` or `1`. The tracked set
is `f` in pointwise form — `i` is in it exactly when `f i = 1`. -/
def Ind (a : String) (n : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  σ.arrs a = arrOf n f ∧ ∀ i, i < n → f i ≤ 1

/-- The array, as a function. -/
theorem Ind.arr (h : Ind a n f σ) : σ.arrs a = arrOf n f := h.1

/-- Every cell is `0` or `1`. -/
theorem Ind.bit (h : Ind a n f σ) (hi : i < n) : f i ≤ 1 := h.2 i hi

/-- The length, which is what a store's range condition asks for. -/
theorem Ind.length (h : Ind a n f σ) : (σ.arrs a).length = n := by
  rw [h.arr, length_arrOf]

/-- Reading a cell. -/
theorem Ind.getD (h : Ind a n f σ) (hi : i < n) : (σ.arrs a).getD i 0 = f i := by
  rw [h.arr, getD_arrOf f hi]

/-- Every cell is a word as soon as `1` is: the reason the bit condition
belongs in the relation rather than in every precondition. -/
theorem Ind.lt (h : Ind a n f σ) (h1B : 1 < B) (hi : i < n) : f i < B :=
  lt_of_le_of_lt (h.bit hi) h1B

/-- Membership is a dichotomy, which is how a `mark[w] = 0` test is read
in a branch. -/
theorem Ind.eq_zero_or_one (h : Ind a n f σ) (hi : i < n) : f i = 0 ∨ f i = 1 := by
  have := h.bit hi; omega

/-- A scalar assignment leaves the indicator alone. -/
@[simp] theorem Ind.setVar_iff (a : String) (n : ℕ) (f : ℕ → ℕ) (σ : Env) (y : String) (v : ℕ) :
    Ind a n f (σ.setVar y v) ↔ Ind a n f σ := by simp [Ind]

theorem Ind.setVar (h : Ind a n f σ) (y : String) (v : ℕ) : Ind a n f (σ.setVar y v) :=
  (Ind.setVar_iff ..).2 h

/-- **The one fact the operations turn on**: storing `v` into cell `k`
updates the cell function at `k`, and the bit condition survives as long
as `v` is a bit. `mark` is `v = 1`, `unmark` is `v = 0`. -/
theorem Ind.setArr (h : Ind a n f σ) (k v : ℕ) (hv : v ≤ 1) :
    Ind a n (upd f k v) (σ.setArr a k v) :=
  ⟨by rw [arrs_setArr, if_pos rfl, h.arr, set_arrOf_eq_upd],
   fun i hi => upd_le hv (h.bit hi)⟩

/-- A store into another array leaves this one alone. -/
theorem Ind.setArr_of_ne (h : Ind a n f σ) {b : String} (hb : b ≠ a) (k v : ℕ) :
    Ind a n f (σ.setArr b k v) :=
  ⟨by rw [arrs_setArr, if_neg hb.symm, h.arr], h.2⟩

/-! Everything from here on is this module's own — its derived view, its
operations, their specifications and its worked example — so it lives in
the module's namespace. `Stack` and `Queue` will both want a `push`; only
`Basic.lean`'s module-agnostic pieces sit in `Lib` itself. -/

namespace Ind

/-! ### The set-shaped view

Derived, on top of the relation and never inside it. A consumer whose
tracked set is a `Finset` or a decidable predicate names its cell
function with `indOf` and moves its own set operations across with the
lemmas here; everything below the relation still sees only `arrOf` and
a function. -/

/-- The cell function of a set given as a decidable predicate. -/
def indOf (S : ℕ → Prop) [DecidablePred S] : ℕ → ℕ := fun i => if S i then 1 else 0

@[simp] theorem indOf_eq_one_iff (S : ℕ → Prop) [DecidablePred S] (i : ℕ) :
    indOf S i = 1 ↔ S i := by
  by_cases h : S i <;> simp [indOf, h]

@[simp] theorem indOf_eq_zero_iff (S : ℕ → Prop) [DecidablePred S] (i : ℕ) :
    indOf S i = 0 ↔ ¬ S i := by
  by_cases h : S i <;> simp [indOf, h]

theorem indOf_le_one (S : ℕ → Prop) [DecidablePred S] (i : ℕ) : indOf S i ≤ 1 := by
  by_cases h : S i <;> simp [indOf, h]

/-- An indicator array of a decidable predicate satisfies the relation
as soon as the array is right; the bit condition is free. -/
theorem of_indOf {S : ℕ → Prop} [DecidablePred S]
    (h : σ.arrs a = arrOf n (indOf S)) : Ind a n (indOf S) σ :=
  ⟨h, fun i _ => indOf_le_one S i⟩

/-- Setting a cell to one is inserting. -/
theorem upd_indOf_one (S : ℕ → Prop) [DecidablePred S] (k : ℕ) :
    upd (indOf S) k 1 = indOf (fun i => S i ∨ i = k) := by
  funext i; by_cases h : i = k <;> simp [indOf, h]

/-- Setting a cell to zero is erasing. -/
theorem upd_indOf_zero (S : ℕ → Prop) [DecidablePred S] (k : ℕ) :
    upd (indOf S) k 0 = indOf (fun i => S i ∧ i ≠ k) := by
  funext i; by_cases h : i = k <;> simp [indOf, h]

/-- The same for a set carried as a `Finset ℕ`, which is the form
Lax11's and Lax15's invariants use. -/
theorem upd_indOf_insert (M : Finset ℕ) (k : ℕ) :
    upd (indOf (· ∈ M)) k 1 = indOf (· ∈ insert k M) := by
  funext i; by_cases h : i = k <;> simp [indOf, h]

/-- And erasing from one. -/
theorem upd_indOf_erase (M : Finset ℕ) (k : ℕ) :
    upd (indOf (· ∈ M)) k 0 = indOf (· ∈ M.erase k) := by
  funext i; by_cases h : i = k <;> simp [indOf, h, Finset.mem_erase]

/-! ### The operations

Three commands, each parameterized in the array it touches, the scalar
holding the index, and — for `test` — the scalar the answer lands in.
Each is one construct, so each costs three. -/

/-- Read cell `x` of the indicator `a` into the scalar `r`. -/
def test (a x r : String) : Com := .assign r (.get a (.var x))

/-- Put cell `x` of the indicator `a` into the set. -/
def mark (a x : String) : Com := .store a (.var x) (.lit 1)

/-- Take cell `x` of the indicator `a` out of the set. -/
def unmark (a x : String) : Com := .store a (.var x) (.lit 0)

/-! The frame conditions of the three, as `simp` lemmas. A call site's
array name is a bound variable, so `Spec.frame`'s obligations are
discharged there by `simp` and not by `decide`. -/

@[simp] theorem wvars_test (a x r : String) : (test a x r).wvars = [r] := by
  simp [test, Com.wvars]

@[simp] theorem warrs_test (a x r : String) : (test a x r).warrs = [] := by
  simp [test, Com.warrs]

@[simp] theorem not_reads_test (a x r : String) : ¬ (test a x r).reads := by
  simp [test, Com.reads]

@[simp] theorem noWrite_test (a x r : String) : (test a x r).NoWrite := by
  simp [test, Com.NoWrite]

@[simp] theorem wvars_mark (a x : String) : (mark a x).wvars = [] := by
  simp [mark, Com.wvars]

@[simp] theorem warrs_mark (a x : String) : (mark a x).warrs = [a] := by
  simp [mark, Com.warrs]

@[simp] theorem not_reads_mark (a x : String) : ¬ (mark a x).reads := by
  simp [mark, Com.reads]

@[simp] theorem noWrite_mark (a x : String) : (mark a x).NoWrite := by
  simp [mark, Com.NoWrite]

@[simp] theorem wvars_unmark (a x : String) : (unmark a x).wvars = [] := by
  simp [unmark, Com.wvars]

@[simp] theorem warrs_unmark (a x : String) : (unmark a x).warrs = [a] := by
  simp [unmark, Com.warrs]

@[simp] theorem not_reads_unmark (a x : String) : ¬ (unmark a x).reads := by
  simp [unmark, Com.reads]

@[simp] theorem noWrite_unmark (a x : String) : (unmark a x).NoWrite := by
  simp [unmark, Com.NoWrite]

/-! ### The specifications -/

/-- What all three operations need: the relation, and an index that is
in range and is a word. -/
abbrev Pre (a x : String) (n B : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  Ind a n f σ ∧ σ.vars x < n ∧ σ.vars x < B

/-- What `test` leaves: the indicator untouched, and `r` holding the
cell — one exactly when the index is in the tracked set. -/
abbrev TestPost (a x r : String) (n : ℕ) (f : ℕ → ℕ) (σ σ' : Env) : Prop :=
  Ind a n f σ' ∧ σ'.vars r = f (σ.vars x) ∧ (σ'.vars r = 1 ↔ f (σ.vars x) = 1)

/-- What `mark` leaves: the index inserted. Everything it did *not*
touch is `Spec.frame`'s to say, not this postcondition's. -/
abbrev MarkPost (a x : String) (n : ℕ) (f : ℕ → ℕ) (σ σ' : Env) : Prop :=
  Ind a n (upd f (σ.vars x) 1) σ'

/-- What `unmark` leaves: the index erased. -/
abbrev UnmarkPost (a x : String) (n : ℕ) (f : ℕ → ℕ) (σ σ' : Env) : Prop :=
  Ind a n (upd f (σ.vars x) 0) σ'

/-- **Testing a cell.** The two obligations of an array read — that the
index is in range, and that the cell is a word — are the relation's to
answer, and the relation is opaque to the walk's discharger. So they are
put into the precondition first, in the array form the walk states them
in, where `omega` finds them verbatim; that is what keeps the proof to
the tactic and one `simp_all`. -/
theorem test_spec (B n : ℕ) (a x r : String) (f : ℕ → ℕ) (h1B : 1 < B) :
    Spec B (Pre a x n B f) (test a x r) (TestPost a x r n f) 3 := by
  refine Spec.pre (P := fun σ => Pre a x n B f σ ∧ σ.vars x < (σ.arrs a).length ∧
      (σ.arrs a).getD (σ.vars x) 0 < B) ?_
    (fun σ h => ⟨h, h.1.length ▸ h.2.1, by rw [h.1.getD h.2.1]; exact h.1.lt h1B h.2.1⟩)
  run_vcg; simp_all [Ind]

/-- **Marking a cell.** -/
theorem mark_spec (B n : ℕ) (a x : String) (f : ℕ → ℕ) (h1B : 1 < B) :
    Spec B (Pre a x n B f) (mark a x) (MarkPost a x n f) 3 := by
  run_vcg
  · exact Ind.setArr (by assumption) _ _ (by omega)
  · simp_all [Ind]

/-- **Unmarking a cell.** -/
theorem unmark_spec (B n : ℕ) (a x : String) (f : ℕ → ℕ) (h1B : 1 < B) :
    Spec B (Pre a x n B f) (unmark a x) (UnmarkPost a x n f) 3 := by
  run_vcg
  · exact Ind.setArr (by assumption) _ _ (by omega)
  · simp_all [Ind]

/-! ### The worked example

Set an index, mark it, read it back, unmark it. `demo` is the block the
specification is about; `demoWatched` is the same block with the two
readings written to the output tape, so that the machine can be seen
doing it. -/

namespace Demo

/-- Mark cell two, read it, unmark it. -/
def demo (a x r : String) : Com :=
  .seq (.assign x (.lit 2)) (.seq (mark a x) (.seq (test a x r) (unmark a x)))

/-- The block, by the three specifications and nothing else: `run_vcg`
steps over each operation and `Spec.frame` carries the index across the
`test`, which is the only thing any of them writes a scalar with. The
index is a literal because a specification's cell function is fixed at
elaboration — see the last paragraph of this file's header. -/
theorem demo_spec (B n : ℕ) (a x r : String) (f : ℕ → ℕ) (h1B : 1 < B) (h2B : 2 < B)
    (h2n : 2 < n) (hxr : x ≠ r) :
    Spec B (fun σ => Ind a n f σ) (demo a x r)
      (fun _ σ' => σ'.vars r = 1 ∧ Ind a n (upd (upd f 2 1) 2 0) σ') 11 := by
  run_vcg [(mark_spec B n a x f h1B).frame, (test_spec B n a x r (upd f 2 1) h1B).frame,
      (unmark_spec B n a x (upd f 2 1) h1B).frame] <;>
    simp_all [MarkPost, TestPost, UnmarkPost]

/-- The same, with both readings written out. -/
def demoWatched (a x r : String) : Com :=
  .seq (.assign x (.lit 2))
    (.seq (mark a x)
      (.seq (test a x r)
        (.seq (.write (.var r))
          (.seq (unmark a x) (.seq (test a x r) (.write (.var r)))))))

/-- Two scalars, one indicator array, two temporaries. -/
def layout : Lax759944Proofs.Legacy.Compile.Layout := ⟨["i", "r"], ["mk"], 2⟩

/-- The machine program. -/
def prog : Lax759944Proofs.Legacy.Ram.Program :=
  Lax759944Proofs.Legacy.Compile.compileProgram layout (demoWatched "mk" "i" "r")

/-- The layout covers the block, so the compilation is the one the
simulation theorem is about and not an accident. -/
theorem demoWatched_ok : Lax759944Proofs.Legacy.Compile.Com.Ok layout (demoWatched "mk" "i" "r") := by
  simp [demoWatched, mark, unmark, test, layout, Lax759944Proofs.Legacy.Compile.Com.Ok,
    Lax759944Proofs.Legacy.Compile.Expr.Ok]

/-- Run it: the machine's memory starts zeroed, which is an indicator of
the empty set, so the first reading must be one and the second zero. -/
def demoRun : Option (List ℕ × ℕ) := runOut 16 1000 prog (Lax759944Proofs.Legacy.Ram.initState []) 0

#guard demoRun = some ([1, 0], 43)

/-! And the arithmetic the example turns on, on the other side of the
abstraction: marking cell two of a four-cell indicator, reading it, and
unmarking it. -/

#guard arrOf 4 (upd (fun _ => 0) 2 1) = [0, 0, 1, 0]
#guard (arrOf 4 (upd (fun _ => 0) 2 1)).getD 2 0 = 1
#guard arrOf 4 (upd (upd (fun _ => 0) 2 1) 2 0) = [0, 0, 0, 0]

end Demo

end Ind

end Lax759944Proofs.Legacy.Reasoning.Lib
