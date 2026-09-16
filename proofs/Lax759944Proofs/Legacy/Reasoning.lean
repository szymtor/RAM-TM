-- Adapted 2026-09-15 from word-ram-v4-33 at 0aa87e1f6e6add4abe4f4e0aff8fe4a28950b2ea.
-- Namespace relocated for use as a proof-only intermediate; semantics unchanged.
import Lax759944Proofs.Legacy.Simulation

/-!
The reasoning kit: how an algorithm is actually proved in this stack.

A big-step derivation is the wrong object to hand a user. It fixes the
cost *on the nose* — the constructors produce sums like
`1 + b.size + k + k'`, which no bound is definitionally equal to — and
it forces every loop to be re-proved by hand from the two `while`
constructors. This layer fixes both, and nothing else:

`Run B c σ σ' K` says that `c`, started in `σ`, terminates in `σ'` at a
cost of **at most** `K`, with every value it produces below `B`. Every
construct gets a rule, the rules compose by adding bounds, and slack can
be introduced at any point (`Run.mono`) instead of being pushed to the
end.

The judgment is built on `BigStepB`, not on `BigStep`: one derivation
carries functional correctness, cost and the value bound together, so a
user proves one thing where the alternative — a `BigStep` derivation
plus a separately established bound on the values of the same run —
would have them build the same derivation twice and then argue that the
two are the same. Where a plain-semantics fact is wanted, it is
projected out by `BigStepB.bigStep` (`Run.bigStep` here); that is how
`Run.out_eq` is proved.

The bound is not an extra hypothesis on any rule. Every rule already
asks for the value of the expression it evaluates, and it asks for it in
the bounded form `e.evalB B σ = some v`; the `simp` lemmas of the first
sections turn such a goal, on concrete syntax, into arithmetic — the
value of the expression and of each of its subexpressions is below `B` —
which is exactly the obligation the design intends and no more.

The loop rule is the only one with content. It takes an invariant `I`
and a **potential** `Φ : Env → ℕ`, and asks that one iteration —
condition test included — pay for itself out of the potential:
`1 + b.size + K + Φ σ' ≤ Φ σ`. Termination and the cost bound then come
out together, because a potential that pays for a nonzero cost is also
a variant; the loop costs at most `Φ σ + 1 + b.size`, the extra term
being the test that fails. Amortized arguments are the reason for the
potential form: a graph scan cannot bound the cost of one outer
iteration by a constant, but it can pay for it out of "queue entries
left plus adjacency slots left". `Run.while_count` is the uniform-cost
special case, an invariant and a variant, for the loops where that
suffices.
-/

namespace Lax759944Proofs.Legacy.Reasoning

open Lax759944Proofs.Legacy.Imp Lax759944Proofs.Legacy.Compile

/-! ### Reading an updated environment

Every rule below produces an environment written as a chain of updates,
and every use reads a variable back out of such a chain. These are the
lemmas that collapse the chain; they are `simp` lemmas, so the reader
of an algorithm proof sees `simp` where a proof against the raw
semantics had explicit `Env.setVar` unfolding at every step. -/

@[simp] theorem vars_setVar (σ : Env) (x : String) (v : ℕ) (y : String) :
    (σ.setVar x v).vars y = if y = x then v else σ.vars y := rfl

@[simp] theorem arrs_setVar (σ : Env) (x : String) (v : ℕ) :
    (σ.setVar x v).arrs = σ.arrs := rfl

@[simp] theorem inp_setVar (σ : Env) (x : String) (v : ℕ) :
    (σ.setVar x v).inp = σ.inp := rfl

@[simp] theorem out_setVar (σ : Env) (x : String) (v : ℕ) :
    (σ.setVar x v).out = σ.out := rfl

@[simp] theorem vars_setArr (σ : Env) (a : String) (i v : ℕ) :
    (σ.setArr a i v).vars = σ.vars := rfl

@[simp] theorem arrs_setArr (σ : Env) (a : String) (i v : ℕ) (b : String) :
    (σ.setArr a i v).arrs b = if b = a then (σ.arrs a).set i v else σ.arrs b := rfl

@[simp] theorem inp_setArr (σ : Env) (a : String) (i v : ℕ) :
    (σ.setArr a i v).inp = σ.inp := rfl

@[simp] theorem out_setArr (σ : Env) (a : String) (i v : ℕ) :
    (σ.setArr a i v).out = σ.out := rfl

/-- A store never changes the length of any array, which is what the
range condition of the next store is about. -/
@[simp] theorem length_arrs_setArr (σ : Env) (a : String) (i v : ℕ) (b : String) :
    ((σ.setArr a i v).arrs b).length = (σ.arrs b).length := by
  rw [arrs_setArr]; split
  · subst_vars; exact List.length_set ..
  · rfl

/-! ### Arrays as functions

An IMP+ array is a list, but an invariant wants to say what is *at*
each position, not what the list is. `arrOf n f` is the array of length
`n` whose entry `i` is `f i`; an invariant then names the function, a
store updates the function at a point, and a read is a function
application. -/

/-- The array of length `n` whose `i`-th entry is `f i`. -/
def arrOf (n : ℕ) (f : ℕ → ℕ) : List ℕ := (List.range n).map f

@[simp] theorem length_arrOf (n : ℕ) (f : ℕ → ℕ) : (arrOf n f).length = n := by
  simp [arrOf]

@[simp] theorem getElem?_arrOf {n i : ℕ} (f : ℕ → ℕ) (h : i < n) :
    (arrOf n f)[i]? = some (f i) := by
  simp [arrOf, h]

/-- An array that has just been created is the constant function: this
is the shape in which `initEnv` hands its arrays over. -/
theorem replicate_eq_arrOf (n v : ℕ) : List.replicate n v = arrOf n (fun _ => v) := by
  simp [arrOf, List.map_const']

/-- Two functions that agree below `n` give the same array: what an
array holds above its own length is not a question. This is what lets a
phase lemma state its result as a *named* function rather than as an
existential over functions that agree where it matters. -/
theorem arrOf_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) :
    arrOf n f = arrOf n g := by
  refine List.ext_getElem (by simp) fun k h₁ _ => ?_
  simp only [arrOf, List.length_map, List.length_range] at h₁
  simp [arrOf, h k h₁]

/-- Reading an entry back out of the list an array is. -/
@[simp] theorem getD_arrOf {n i : ℕ} (f : ℕ → ℕ) (h : i < n) :
    (arrOf n f).getD i 0 = f i := by
  simp [List.getD_eq_getElem?_getD, getElem?_arrOf f h]

/-- Storing into an array updates the function it comes from. -/
theorem set_arrOf {n i : ℕ} (f : ℕ → ℕ) (v : ℕ) :
    (arrOf n f).set i v = arrOf n (fun k => if k = i then v else f k) := by
  refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
  rw [List.getElem_set]
  by_cases hk : k = i
  · subst hk; simp [arrOf]
  · simp [arrOf, hk, Ne.symm hk]

/-! ### Bounded evaluation of concrete syntax

The side condition of every rule below is a bounded evaluation
`e.evalB B σ = some v`. On the concrete syntax of an actual program
these lemmas reduce such a goal to arithmetic: the value of every
subexpression is exhibited, and what is left to prove is that each of
them is below `B`. This is the whole of the value-bound obligation the
pipeline asks for, and it arrives one expression at a time, where the
values are in front of the reader, rather than as a separate pass over
the program. -/

@[simp] theorem evalB_lit_iff {B n v : ℕ} {σ : Env} :
    (Expr.lit n).evalB B σ = some v ↔ v = n ∧ n < B := by
  rw [Expr.evalB, fit_eq_some]

@[simp] theorem evalB_var_iff {B : ℕ} {x : String} {σ : Env} {v : ℕ} :
    (Expr.var x).evalB B σ = some v ↔ v = σ.vars x ∧ σ.vars x < B := by
  rw [Expr.evalB, fit_eq_some]

@[simp] theorem evalB_get_iff {B : ℕ} {a : String} {i : Expr} {σ : Env} {v : ℕ} :
    (Expr.get a i).evalB B σ = some v ↔
      ∃ k, i.evalB B σ = some k ∧ (σ.arrs a)[k]? = some v ∧ v < B := by
  rw [Expr.evalB]
  simp only [Option.bind_eq_some_iff, fit_eq_some]
  constructor
  · rintro ⟨k, hk, u, hu, rfl, hlt⟩; exact ⟨k, hk, hu, hlt⟩
  · rintro ⟨k, hk, hu, hlt⟩; exact ⟨k, hk, v, hu, rfl, hlt⟩

@[simp] theorem evalB_bin_iff {B : ℕ} {op : Bop} {e f : Expr} {σ : Env} {v : ℕ} :
    (Expr.bin op e f).evalB B σ = some v ↔
      ∃ m n, e.evalB B σ = some m ∧ f.evalB B σ = some n ∧ v = op.apply m n ∧ v < B := by
  rw [Expr.evalB]
  simp only [Option.bind_eq_some_iff, fit_eq_some]
  constructor
  · rintro ⟨m, hm, n, hn, rfl, hlt⟩; exact ⟨m, n, hm, hn, rfl, hlt⟩
  · rintro ⟨m, n, hm, hn, rfl, hlt⟩; exact ⟨m, hm, n, hn, rfl, hlt⟩

@[simp] theorem evalB_condEq_iff {B : ℕ} {e f : Expr} {σ : Env} {r : Bool} :
    (Cond.eq e f).evalB B σ = some r ↔
      ∃ m n, e.evalB B σ = some m ∧ f.evalB B σ = some n ∧ r = (m == n) := by
  rw [Cond.evalB]
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨m, hm, n, hn, rfl⟩; exact ⟨m, n, hm, hn, rfl⟩
  · rintro ⟨m, n, hm, hn, rfl⟩; exact ⟨m, hm, n, hn, rfl⟩

@[simp] theorem evalB_condLt_iff {B : ℕ} {e f : Expr} {σ : Env} {r : Bool} :
    (Cond.lt e f).evalB B σ = some r ↔
      ∃ m n, e.evalB B σ = some m ∧ f.evalB B σ = some n ∧ r = decide (m < n) := by
  rw [Cond.evalB]
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨m, hm, n, hn, rfl⟩; exact ⟨m, n, hm, hn, rfl⟩
  · rintro ⟨m, n, hm, hn, rfl⟩; exact ⟨m, hm, n, hn, rfl⟩

/-! ### Introducing a bounded evaluation

The lemmas above are what `simp` needs; these are what `exact` needs.
The side condition of a rule is `e.evalB B σ = some v` with `v` already
named by the caller, and the side condition of the loop rule is the
weaker `∃ v, b.evalB B σ = some v` — a condition whose two operands
have values has one too, whichever it is. Stated as introduction rules
these are discharged by naming the value of each subexpression and its
bound, which is what a caller has in hand, instead of by first guessing
the truth value of the condition and then unfolding it again. -/

theorem evalB_lit {B n : ℕ} {σ : Env} (h : n < B) : (Expr.lit n).evalB B σ = some n :=
  fit_self h

theorem evalB_var {B : ℕ} {x : String} {σ : Env} (h : σ.vars x < B) :
    (Expr.var x).evalB B σ = some (σ.vars x) := fit_self h

theorem evalB_get {B : ℕ} {a : String} {i : Expr} {σ : Env} {k v : ℕ}
    (hi : i.evalB B σ = some k) (hk : (σ.arrs a)[k]? = some v) (hv : v < B) :
    (Expr.get a i).evalB B σ = some v := by
  rw [Expr.evalB, hi, Option.bind_some, hk, Option.bind_some, fit_self hv]

theorem evalB_bin {B : ℕ} {op : Bop} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : op.apply m n < B) :
    (Expr.bin op e f).evalB B σ = some (op.apply m n) := by
  rw [Expr.evalB, he, Option.bind_some, hf, Option.bind_some, fit_self h]

theorem evalB_condEq {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) :
    (Cond.eq e f).evalB B σ = some (m == n) := by
  rw [Cond.evalB, he, Option.bind_some, hf, Option.map_some]

theorem evalB_condLt {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) :
    (Cond.lt e f).evalB B σ = some (decide (m < n)) := by
  rw [Cond.evalB, he, Option.bind_some, hf, Option.map_some]

/-- The `hdef` obligation of the loop rule for an equality test, with
the truth value characterized: the caller supplies the two operands and
gets back both that the condition evaluates and what its value means. -/
theorem evalB_condEq_isSome {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) :
    ∃ v, (Cond.eq e f).evalB B σ = some v ∧ (v = true ↔ m = n) :=
  ⟨_, evalB_condEq he hf, by simp⟩

/-- The `hdef` obligation of the loop rule for an order test, with the
truth value characterized. -/
theorem evalB_condLt_isSome {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) :
    ∃ v, (Cond.lt e f).evalB B σ = some v ∧ (v = true ↔ m < n) :=
  ⟨_, evalB_condLt he hf, by simp⟩

/-- The `hdef` obligation for the commonest loop condition of all, two
scalars compared: nothing is asked but that both are below the bound. -/
theorem evalB_condLt_vars {B : ℕ} {x y : String} {σ : Env}
    (hx : σ.vars x < B) (hy : σ.vars y < B) :
    ∃ v, (Cond.lt (.var x) (.var y)).evalB B σ = some v :=
  ⟨_, evalB_condLt (evalB_var hx) (evalB_var hy)⟩

/-- The `hdef` obligation for a scalar compared against a literal. -/
theorem evalB_condLt_var_lit {B : ℕ} {x : String} {n : ℕ} {σ : Env}
    (hx : σ.vars x < B) (hn : n < B) :
    ∃ v, (Cond.lt (.var x) (.lit n)).evalB B σ = some v :=
  ⟨_, evalB_condLt (evalB_var hx) (evalB_lit hn)⟩

/-! ### Counting the size of concrete syntax

An algorithm proof should never be told what a concrete expression
costs; with these the cost of a straight-line block is arithmetic on
numerals. The nine named operators get a lemma each alongside the one
for `bin`, so that a cost computation on a program written with the
abbreviations is simplified by lemmas carrying the same names. -/

@[simp] theorem size_lit (n : ℕ) : (Expr.lit n).size = 1 := rfl
@[simp] theorem size_var (x : String) : (Expr.var x).size = 1 := rfl
@[simp] theorem size_get (a : String) (i : Expr) : (Expr.get a i).size = i.size + 1 := rfl
@[simp] theorem size_bin (op : Bop) (e f : Expr) :
    (Expr.bin op e f).size = e.size + f.size + 1 := rfl
@[simp] theorem size_add (e f : Expr) : (Expr.add e f).size = e.size + f.size + 1 := rfl
@[simp] theorem size_sub (e f : Expr) : (Expr.sub e f).size = e.size + f.size + 1 := rfl
@[simp] theorem size_mul (e f : Expr) : (Expr.mul e f).size = e.size + f.size + 1 := rfl
@[simp] theorem size_div (e f : Expr) : (Expr.div e f).size = e.size + f.size + 1 := rfl
@[simp] theorem size_and (e f : Expr) : (Expr.and e f).size = e.size + f.size + 1 := rfl
@[simp] theorem size_or (e f : Expr) : (Expr.or e f).size = e.size + f.size + 1 := rfl
@[simp] theorem size_xor (e f : Expr) : (Expr.xor e f).size = e.size + f.size + 1 := rfl
@[simp] theorem size_shiftl (e f : Expr) : (Expr.shiftl e f).size = e.size + f.size + 1 := rfl
@[simp] theorem size_shiftr (e f : Expr) : (Expr.shiftr e f).size = e.size + f.size + 1 := rfl
@[simp] theorem size_condEq (e f : Expr) : (Cond.eq e f).size = e.size + f.size + 1 := rfl
@[simp] theorem size_condLt (e f : Expr) : (Cond.lt e f).size = e.size + f.size + 1 := rfl

/-! ### The bounded judgment -/

/-- `Run B c σ σ' K`: started in `σ`, the command `c` terminates in `σ'`
at a cost of at most `K`, every value it produces staying below `B`.
This is the judgment every algorithm proof is written in; the cost is a
bound rather than a value, so the arithmetic of the cost model never has
to be matched syntactically. -/
def Run (B : ℕ) (c : Com) (σ σ' : Env) (K : ℕ) : Prop := ∃ k ≤ K, BigStepB B c σ σ' k

theorem Run.of_bigStepB {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStepB B c σ σ' k) :
    Run B c σ σ' k := ⟨k, le_rfl, h⟩

/-- The plain semantics underneath a `Run`, for the facts that are
about the run and not about the bound. -/
theorem Run.bigStep {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K) :
    ∃ k ≤ K, BigStep c σ σ' k := by
  obtain ⟨k, hk, hbs⟩ := h; exact ⟨k, hk, hbs.bigStep⟩

/-- Slack may be taken at any point in a proof, not only at the end. -/
theorem Run.mono {B : ℕ} {c : Com} {σ σ' : Env} {K K' : ℕ} (h : Run B c σ σ' K) (hK : K ≤ K') :
    Run B c σ σ' K' := by
  obtain ⟨k, hk, hbs⟩ := h; exact ⟨k, hk.trans hK, hbs⟩

/-- The final environment matters only up to equality, and rules
produce it in whatever shape the update chain has. -/
theorem Run.congr {B : ℕ} {c : Com} {σ σ' σ'' : Env} {K : ℕ} (h : Run B c σ σ' K)
    (hσ : σ' = σ'') : Run B c σ σ'' K := hσ ▸ h

/-- A run consumes the input tape, so a bound on it is preserved. -/
theorem Run.inpBounded {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K)
    (hσ : σ.InpBounded B) : σ'.InpBounded B := by
  obtain ⟨_, _, hbs⟩ := h; exact hbs.inpBounded hσ

theorem Run.skip {B : ℕ} {σ : Env} : Run B .skip σ σ 1 := .of_bigStepB .skip

theorem Run.assign {B : ℕ} {σ : Env} {x : String} {e : Expr} {v : ℕ}
    (h : e.evalB B σ = some v) :
    Run B (.assign x e) σ (σ.setVar x v) (1 + e.size) := .of_bigStepB (.assign h)

theorem Run.store {B : ℕ} {σ : Env} {a : String} {i e : Expr} {idx v : ℕ}
    (hi : i.evalB B σ = some idx) (he : e.evalB B σ = some v)
    (hidx : idx < (σ.arrs a).length) :
    Run B (.store a i e) σ (σ.setArr a idx v) (1 + i.size + e.size) :=
  .of_bigStepB (.store hi he hidx)

theorem Run.read {B : ℕ} {σ : Env} {x : String} {v : ℕ} {rest : List ℕ}
    (h : σ.inp = v :: rest) :
    Run B (.read x) σ { σ.setVar x v with inp := rest } 1 := .of_bigStepB (.read h)

theorem Run.write {B : ℕ} {σ : Env} {e : Expr} {v : ℕ} (h : e.evalB B σ = some v) :
    Run B (.write e) σ { σ with out := σ.out ++ [v] } (1 + e.size) := .of_bigStepB (.write h)

theorem Run.seq {B : ℕ} {c d : Com} {σ σ' σ'' : Env} {K K' : ℕ}
    (h : Run B c σ σ' K) (h' : Run B d σ' σ'' K') : Run B (.seq c d) σ σ'' (K + K') := by
  obtain ⟨k, hk, hbs⟩ := h
  obtain ⟨k', hk', hbs'⟩ := h'
  exact ⟨k + k', by omega, .seq hbs hbs'⟩

theorem Run.ite_true {B : ℕ} {b : Cond} {c d : Com} {σ σ' : Env} {K : ℕ}
    (hb : b.evalB B σ = some true) (h : Run B c σ σ' K) :
    Run B (.ite b c d) σ σ' (1 + b.size + K) := by
  obtain ⟨k, hk, hbs⟩ := h
  exact ⟨1 + b.size + k, by omega, .ite_true hb hbs⟩

theorem Run.ite_false {B : ℕ} {b : Cond} {c d : Com} {σ σ' : Env} {K : ℕ}
    (hb : b.evalB B σ = some false) (h : Run B d σ σ' K) :
    Run B (.ite b c d) σ σ' (1 + b.size + K) := by
  obtain ⟨k, hk, hbs⟩ := h
  exact ⟨1 + b.size + k, by omega, .ite_false hb hbs⟩

theorem Run.while_false {B : ℕ} {b : Cond} {c : Com} {σ : Env}
    (hb : b.evalB B σ = some false) : Run B (.while b c) σ σ (1 + b.size) :=
  .of_bigStepB (.while_false hb)

/-! ### The loop rule -/

/-- **The while rule.** Given an invariant `I` whose condition always
evaluates below the bound, and a potential `Φ` out of which one
iteration — the condition test included — pays for itself, the loop
terminates in a state that still satisfies `I` and fails the condition,
at a cost of at most `Φ σ + 1 + b.size`.

Termination is not a separate obligation: an iteration costs at least
one unit, so a potential that pays for it strictly decreases. The
potential form is what makes amortized bounds direct — the cost of a
single iteration need not be bounded at all, only the total.

The conclusion bounds the cost by the potential *drop*, not by the
potential at entry. That is what lets one loop's leftover potential pay
for what happens after it: a nested search whose outer sweep and inner
searches draw on the same budget could not be assembled from the weaker
form, since the outer proof would have to count the inner potential
twice. -/
theorem Run.while_potential {B : ℕ} {b : Cond} {c : Com} (I : Env → Prop) (Φ : Env → ℕ)
    (hdef : ∀ σ, I σ → ∃ v, b.evalB B σ = some v)
    (hstep : ∀ σ, I σ → b.evalB B σ = some true →
      ∃ σ' K, Run B c σ σ' K ∧ I σ' ∧ 1 + b.size + K + Φ σ' ≤ Φ σ)
    {σ : Env} (hI : I σ) :
    ∃ σ' K, Run B (.while b c) σ σ' K ∧ I σ' ∧ b.evalB B σ' = some false ∧
      K + Φ σ' ≤ Φ σ + 1 + b.size := by
  suffices H : ∀ n σ, I σ → Φ σ ≤ n →
      ∃ σ' K, Run B (.while b c) σ σ' K ∧ I σ' ∧ b.evalB B σ' = some false ∧
        K + Φ σ' ≤ Φ σ + 1 + b.size from H (Φ σ) σ hI le_rfl
  clear hI σ
  intro n
  induction n with
  | zero =>
      intro σ hI hΦ
      obtain ⟨v, hv⟩ := hdef σ hI
      cases v with
      | false => exact ⟨σ, _, Run.while_false hv, hI, hv, by omega⟩
      | true =>
          obtain ⟨σ₁, K, hrun, _, hpay⟩ := hstep σ hI hv
          omega
  | succ n ih =>
      intro σ hI hΦ
      obtain ⟨v, hv⟩ := hdef σ hI
      cases v with
      | false => exact ⟨σ, _, Run.while_false hv, hI, hv, by omega⟩
      | true =>
          obtain ⟨σ₁, K, hrun, hI₁, hpay⟩ := hstep σ hI hv
          obtain ⟨σ', K', hrun', hI', hfalse, hpay'⟩ := ih σ₁ hI₁ (by omega)
          obtain ⟨k, hk, hbs⟩ := hrun
          obtain ⟨k', hk', hbs'⟩ := hrun'
          exact ⟨σ', 1 + b.size + k + k', ⟨1 + b.size + k + k', le_rfl,
            .while_true hv hbs hbs'⟩, hI', hfalse, by omega⟩

/-- **The counted while rule**, the common case: an invariant, a
variant that strictly decreases, and one bound `P` on the cost of an
iteration. -/
theorem Run.while_count {B : ℕ} {b : Cond} {c : Com} (I : Env → Prop) (V : Env → ℕ) (P : ℕ)
    (hdef : ∀ σ, I σ → ∃ v, b.evalB B σ = some v)
    (hstep : ∀ σ, I σ → b.evalB B σ = some true → ∃ σ', Run B c σ σ' P ∧ I σ' ∧ V σ' < V σ)
    {σ : Env} (hI : I σ) :
    ∃ σ', Run B (.while b c) σ σ' ((1 + b.size + P) * V σ + 1 + b.size) ∧ I σ' ∧
      b.evalB B σ' = some false := by
  have key : ∀ τ, I τ → b.evalB B τ = some true →
      ∃ τ' K, Run B c τ τ' K ∧ I τ' ∧
        1 + b.size + K + (1 + b.size + P) * V τ' ≤ (1 + b.size + P) * V τ := by
    intro τ hIτ hv
    obtain ⟨τ', hrun, hI', hV⟩ := hstep τ hIτ hv
    refine ⟨τ', P, hrun, hI', ?_⟩
    calc 1 + b.size + P + (1 + b.size + P) * V τ'
        = (1 + b.size + P) * (V τ' + 1) := by ring
      _ ≤ (1 + b.size + P) * V τ := Nat.mul_le_mul_left _ hV
  obtain ⟨σ', K, hrun, hI', hfalse, hpay⟩ :=
    Run.while_potential I (fun σ => (1 + b.size + P) * V σ) hdef key hI
  exact ⟨σ', hrun.mono (by omega), hI', hfalse⟩

/-! ### The one frame condition that is worth having generically

A phase lemma states its own frame conditions on the variables and
arrays it touches, because those differ from phase to phase. The output
tape is the exception: almost every phase leaves it alone, and it is
syntactically evident which ones do. So it is stated once, for all
commands that contain no `write`, and no invariant has to carry it. -/

/-- The command contains no `write`. -/
def _root_.Lax759944Proofs.Legacy.Imp.Com.NoWrite : Com → Prop
  | .skip => True
  | .assign _ _ => True
  | .store _ _ _ => True
  | .read _ => True
  | .write _ => False
  | .seq c d => c.NoWrite ∧ d.NoWrite
  | .ite _ c d => c.NoWrite ∧ d.NoWrite
  | .while _ c => c.NoWrite

/-- `skip` contains no `write`.

The statement is the trivial case and is not what the lemma is for: the
`simp` in its proof creates the equation lemmas of `NoWrite` — and the
splitter of its match — *in this package*. They are created on first
use, in the module that uses them, and the use is `simp [Com.NoWrite]`
in whatever algorithm proof invokes `BigStep.out_eq`; done there, in
another package, it leaves that package holding declarations named
under `Lax759944Proofs.Legacy`, which the archive's namespace rule rejects. Asking
here is enough: every later `simp [Com.NoWrite]` finds the equations
among its imports and creates nothing. -/
theorem _root_.Lax759944Proofs.Legacy.Imp.Com.noWrite_skip : Com.skip.NoWrite := by
  simp [Com.NoWrite]

/-- A command that contains no `write` leaves the output tape alone. -/
theorem _root_.Lax759944Proofs.Legacy.Imp.BigStep.out_eq {c : Com} {σ σ' : Env} {k : ℕ}
    (h : BigStep c σ σ' k) : c.NoWrite → σ'.out = σ.out := by
  induction h with
  | skip => intro _; rfl
  | assign _ => intro _; rfl
  | store _ _ _ => intro _; rfl
  | seq _ _ ih ih' => intro hc; rw [ih' hc.2, ih hc.1]
  | ite_true _ _ ih => intro hc; exact ih hc.1
  | ite_false _ _ ih => intro hc; exact ih hc.2
  | while_true _ _ _ ih ih' => intro hc; rw [ih' hc, ih hc]
  | while_false _ => intro _; rfl
  | read _ => intro _; rfl
  | write _ => intro hc; exact absurd hc not_false

theorem Run.out_eq {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K)
    (hc : c.NoWrite) : σ'.out = σ.out := by
  obtain ⟨_, _, hbs⟩ := h.bigStep; exact hbs.out_eq hc

end Lax759944Proofs.Legacy.Reasoning
