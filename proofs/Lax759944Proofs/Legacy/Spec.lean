-- Adapted 2026-09-15 from word-ram-v4-33 at 0aa87e1f6e6add4abe4f4e0aff8fe4a28950b2ea.
-- Namespace relocated for use as a proof-only intermediate; semantics unchanged.
import Lax759944Proofs.Legacy.Frame

/-!
Specifications: what a phase of a program does, as an object that
composes.

`Run` is a judgment about *one* pair of environments. A phase lemma
written directly in it has to be stated as an existential — "there are
`ρ'` and `K` with `Run B c ρ ρ' K` and `K ≤ 30` and these frame
conditions and this disjunction of cases" — and composing two of them is
`obtain` on the first, `obtain` on the second, and a hand-assembled
`refine` for the result. Every phase lemma in the repo has that shape,
and every use of one pays for it twice: once to take the existential
apart, once to put the successor back together.

`Spec B P c Q K` packages the same content as a *predicate on the
program*: from any state satisfying `P`, the command `c` runs to a state
standing in relation `Q` to it, at a cost of at most `K`. The
existential moves inside the definition, and with it the `obtain`s: two
phases compose by `Spec.seq`, which is a term, not a tactic block.

Three decisions are worth stating, since they are what make the
interface fit this repo rather than a textbook.

* **`Q` is relational.** A phase lemma says `ρ'.vars "ro" = ρ.vars "ro"
  + 1`, not `ρ'.vars "ro" = 7`; a postcondition that could not mention
  the initial environment would force every such statement through an
  auxiliary variable. So `Q : Env → Env → Prop`, initial environment
  first.
* **The cost is one number, an upper bound.** It rides in the `Run`,
  where it is already an upper bound, so `Spec.mono` is slack-taking and
  nothing else. Loops whose cost is amortized state their potential in
  the loop rule and export a constant, which is what the phase lemmas of
  the repo already do.
* **`B` is a parameter of the whole interface**, not an implicit
  argument recovered from the goal. `B` occurs in no hypothesis that
  determines it — a phase lemma with no `< B` side condition left it
  entirely undetermined and the caller had to write `(B := B)` by
  hand. In a `Spec` it is the first explicit argument.

The frame rule of `Frame.lean` enters through `Spec.frame`, which
strengthens any specification with the four frame conditions its command
allows, read off the syntax. A composed phase therefore never
re-establishes a frame condition: it inherits one for the `seq` it is.
-/

namespace Lax759944Proofs.Legacy.Reasoning

open Lax759944Proofs.Legacy.Imp

variable {B : ℕ} {P P' : Env → Prop} {Q Q' R : Env → Env → Prop} {c d : Com} {K K' : ℕ}

/-- `Spec B P c Q K`: started in any state satisfying `P`, the command
`c` terminates in a state standing in relation `Q` to the one it started
in, at a cost of at most `K`, every value it produces staying below
`B`. -/
def Spec (B : ℕ) (P : Env → Prop) (c : Com) (Q : Env → Env → Prop) (K : ℕ) : Prop :=
  ∀ σ, P σ → ∃ σ', Run B c σ σ' K ∧ Q σ σ'

/-- Using a specification: it is a function, so this is definitional,
but naming it keeps `Spec` opaque at the call sites that do not need to
know how it is built. -/
theorem Spec.run (h : Spec B P c Q K) {σ : Env} (hσ : P σ) :
    ∃ σ', Run B c σ σ' K ∧ Q σ σ' := h σ hσ

/-- The bridge every existing phase lemma crosses. Their shape is
`∃ σ' K', Run B c σ σ' K' ∧ K' ≤ K ∧ Q σ σ'`, with the cost bound as a
separate conjunct; `Run`'s cost is already an upper bound, so the two
say the same thing. -/
theorem Spec.of_exists (h : ∀ σ, P σ → ∃ σ' K', Run B c σ σ' K' ∧ K' ≤ K ∧ Q σ σ') :
    Spec B P c Q K := by
  intro σ hσ
  obtain ⟨σ', K', hr, hK, hq⟩ := h σ hσ
  exact ⟨σ', hr.mono hK, hq⟩

/-! ### The structural rules -/

/-- Slack in the cost. -/
theorem Spec.mono (h : Spec B P c Q K) (hK : K ≤ K') : Spec B P c Q K' := by
  intro σ hσ
  obtain ⟨σ', hr, hq⟩ := h σ hσ
  exact ⟨σ', hr.mono hK, hq⟩

/-- **The rule of consequence**: strengthen the precondition, weaken the
postcondition, loosen the cost. The postcondition may be weakened using
the precondition, which is what a relational `Q` usually needs. -/
theorem Spec.conseq (h : Spec B P c Q K) (hP : ∀ σ, P' σ → P σ)
    (hQ : ∀ σ σ', P' σ → Q σ σ' → Q' σ σ') (hK : K ≤ K') : Spec B P' c Q' K' := by
  intro σ hσ
  obtain ⟨σ', hr, hq⟩ := h σ (hP σ hσ)
  exact ⟨σ', hr.mono hK, hQ σ σ' hσ hq⟩

/-- Strengthening the precondition alone. -/
theorem Spec.pre (h : Spec B P c Q K) (hP : ∀ σ, P' σ → P σ) : Spec B P' c Q K :=
  h.conseq hP (fun _ _ _ hq => hq) le_rfl

/-- Weakening the postcondition alone. -/
theorem Spec.post (h : Spec B P c Q K) (hQ : ∀ σ σ', P σ → Q σ σ' → Q' σ σ') :
    Spec B P c Q' K :=
  h.conseq (fun _ hσ => hσ) hQ le_rfl

/-- **The frame rule.** Any specification also says that the command
left alone every scalar it cannot assign to, every array it cannot store
into, the input tape if it contains no `read`, and the output tape if it
contains no `write`. Nothing is asked of the caller: the four facts are
read off the syntax of `c` by `Frame.lean`, and a call site discharges
`y ∉ c.wvars` by `decide`.

This is what makes composition cheap. The `seq` of two phases inherits
the frame of the `seq`, so a phase that touches only the marks does not
have to re-establish anything about the stack. -/
theorem Spec.frame (h : Spec B P c Q K) :
    Spec B P c (fun σ σ' => Q σ σ' ∧
      (∀ y, y ∉ c.wvars → σ'.vars y = σ.vars y) ∧
      (∀ a, a ∉ c.warrs → σ'.arrs a = σ.arrs a) ∧
      (¬ c.reads → σ'.inp = σ.inp) ∧
      (c.NoWrite → σ'.out = σ.out)) K := by
  intro σ hσ
  obtain ⟨σ', hr, hq⟩ := h σ hσ
  exact ⟨σ', hr, hq, fun y hy => hr.frame_var y hy, fun a ha => hr.frame_arr a ha,
    fun hc => hr.frame_inp hc, fun hc => hr.out_eq hc⟩

/-! ### The rules of the language -/

theorem Spec.skip : Spec B P .skip (fun σ σ' => σ' = σ) 1 :=
  fun σ _ => ⟨σ, Run.skip, rfl⟩

/-- An assignment, with the value named as a function of the state the
caller is in. -/
theorem Spec.assign {x : String} {e : Expr} {f : Env → ℕ}
    (h : ∀ σ, P σ → e.evalB B σ = some (f σ)) :
    Spec B P (.assign x e) (fun σ σ' => σ' = σ.setVar x (f σ)) (1 + e.size) :=
  fun σ hσ => ⟨_, Run.assign (h σ hσ), rfl⟩

/-- A store, with the index and the value named as functions of the
state. -/
theorem Spec.store {a : String} {i e : Expr} {idx f : Env → ℕ}
    (hi : ∀ σ, P σ → i.evalB B σ = some (idx σ)) (he : ∀ σ, P σ → e.evalB B σ = some (f σ))
    (hidx : ∀ σ, P σ → idx σ < (σ.arrs a).length) :
    Spec B P (.store a i e) (fun σ σ' => σ' = σ.setArr a (idx σ) (f σ)) (1 + i.size + e.size) :=
  fun σ hσ => ⟨_, Run.store (hi σ hσ) (he σ hσ) (hidx σ hσ), rfl⟩

/-! The two tape operations. Both are stated the way `assign` and
`store` are — the caller names what the operation moves as a function of
the state it is in — and both are relational in the tape they touch,
since a phase says how the tape it was handed *changed*, never what it
is. -/

/-- **A read**: the head of the input tape goes into `x`, and the tape
loses it. The caller names the head and what is left; naming them is the
side condition, since a read from an exhausted tape has no derivation
at all. -/
theorem Spec.read {x : String} {v : Env → ℕ} {rest : Env → List ℕ}
    (h : ∀ σ, P σ → σ.inp = v σ :: rest σ) :
    Spec B P (.read x) (fun σ σ' => σ' = { σ.setVar x (v σ) with inp := rest σ }) 1 :=
  fun σ hσ => ⟨_, Run.read (h σ hσ), rfl⟩

/-- **A write**: the value of the expression is appended to the output
tape. The value is named as a function of the state, and being below the
bound is part of naming it — `evalB` is the bounded evaluation. -/
theorem Spec.write {e : Expr} {f : Env → ℕ}
    (h : ∀ σ, P σ → e.evalB B σ = some (f σ)) :
    Spec B P (.write e) (fun σ σ' => σ' = { σ with out := σ.out ++ [f σ] }) (1 + e.size) :=
  fun σ hσ => ⟨_, Run.write (h σ hσ), rfl⟩

/-- **Sequencing**, the rule the interface exists for. `hmid` says the
first phase lands in the second's precondition, `hpost` composes the two
relations into the one wanted; neither mentions a `Run`, and the result
is a term. -/
theorem Spec.seq (h : Spec B P c Q K) (h' : Spec B P' d Q' K')
    (hmid : ∀ σ σ', P σ → Q σ σ' → P' σ')
    (hpost : ∀ σ σ' σ'', P σ → Q σ σ' → Q' σ' σ'' → R σ σ'') :
    Spec B P (.seq c d) R (K + K') := by
  intro σ hσ
  obtain ⟨σ', hr, hq⟩ := h σ hσ
  obtain ⟨σ'', hr', hq'⟩ := h' σ' (hmid σ σ' hσ hq)
  exact ⟨σ'', hr.seq hr', hpost σ σ' σ'' hσ hq hq'⟩

/-- Sequencing with the composite relation left as an existential over
the intermediate state, for when the caller has nothing better to say
about it. -/
theorem Spec.seq' (h : Spec B P c Q K) (h' : Spec B P' d Q' K')
    (hmid : ∀ σ σ', P σ → Q σ σ' → P' σ') :
    Spec B P (.seq c d) (fun σ σ'' => ∃ σ', Q σ σ' ∧ Q' σ' σ'') (K + K') :=
  h.seq h' hmid (fun _ σ' _ _ hq hq' => ⟨σ', hq, hq'⟩)

/-- **The conditional.** Both branches carry the truth of the test in
their precondition, which is how a branch proves what it needs about the
state it runs in. The cost is the larger branch's, taken by `Spec.mono`
on the smaller one first. -/
theorem Spec.ite {b : Cond} (hdef : ∀ σ, P σ → ∃ v, b.evalB B σ = some v)
    (ht : Spec B (fun σ => P σ ∧ b.evalB B σ = some true) c Q K)
    (hf : Spec B (fun σ => P σ ∧ b.evalB B σ = some false) d Q K) :
    Spec B P (.ite b c d) Q (1 + b.size + K) := by
  intro σ hσ
  obtain ⟨v, hv⟩ := hdef σ hσ
  cases v with
  | true =>
      obtain ⟨σ', hr, hq⟩ := ht σ ⟨hσ, hv⟩
      exact ⟨σ', Run.ite_true hv hr, hq⟩
  | false =>
      obtain ⟨σ', hr, hq⟩ := hf σ ⟨hσ, hv⟩
      exact ⟨σ', Run.ite_false hv hr, hq⟩

/-! ### The loop rules

`Run.while_potential` stays the primitive: its step obligation carries
an existential cost, which is exactly what an amortized loop needs and
what a `Spec`'s fixed `K` cannot express. What the rules here add is the
packaging — the loop's own cost, which depends on the state it starts
in, is discharged against `K` once, by the caller, at the top. -/

/-- **The loop, with a potential.** The step obligation is
`Run.while_potential`'s, unchanged. The conclusion is a `Spec`: the
caller bounds the potential at entry by `K` and never mentions it
again. -/
theorem Spec.while_potential {b : Cond} (I : Env → Prop) (Φ : Env → ℕ)
    (hdef : ∀ σ, I σ → ∃ v, b.evalB B σ = some v)
    (hstep : ∀ σ, I σ → b.evalB B σ = some true →
      ∃ σ' K, Run B c σ σ' K ∧ I σ' ∧ 1 + b.size + K + Φ σ' ≤ Φ σ)
    (hPI : ∀ σ, P σ → I σ) (hK : ∀ σ, P σ → Φ σ + 1 + b.size ≤ K) :
    Spec B P (.while b c) (fun _ σ' => I σ' ∧ b.evalB B σ' = some false) K := by
  intro σ hσ
  obtain ⟨σ', K₀, hr, hI, hfalse, hpay⟩ := Run.while_potential I Φ hdef hstep (hPI σ hσ)
  exact ⟨σ', hr.mono (by have := hK σ hσ; omega), hI, hfalse⟩

/-- **The counted loop**: an invariant, a variant that drops, one cost
bound per turn. The body is given as a `Spec`, so a loop whose body is
built from phases is assembled entirely in this interface. -/
theorem Spec.while_count {b : Cond} (I : Env → Prop) (V : Env → ℕ) (Kb : ℕ)
    (hdef : ∀ σ, I σ → ∃ v, b.evalB B σ = some v)
    (hbody : Spec B (fun σ => I σ ∧ b.evalB B σ = some true) c
      (fun σ σ' => I σ' ∧ V σ' < V σ) Kb)
    (hPI : ∀ σ, P σ → I σ) (hK : ∀ σ, P σ → (1 + b.size + Kb) * V σ + 1 + b.size ≤ K) :
    Spec B P (.while b c) (fun _ σ' => I σ' ∧ b.evalB B σ' = some false) K := by
  refine Spec.while_potential I (fun σ => (1 + b.size + Kb) * V σ) hdef ?_ hPI hK
  intro σ hI hv
  obtain ⟨σ', hr, hI', hV⟩ := hbody σ ⟨hI, hv⟩
  refine ⟨σ', Kb, hr, hI', ?_⟩
  calc 1 + b.size + Kb + (1 + b.size + Kb) * V σ'
      = (1 + b.size + Kb) * (V σ' + 1) := by ring
    _ ≤ (1 + b.size + Kb) * V σ := Nat.mul_le_mul_left _ hV

/-! ### Reading a comparison of two scalars

The loop condition of every scan in the repo is `x < m` on two scalars.
These say what its truth and its falsity mean, which `Spec.forRange`
needs and which every hand-written loop proof was re-deriving. -/

/-- What the truth of `x < y` says. -/
theorem lt_of_condLt_true {B : ℕ} {x y : String} {ρ : Env}
    (h : (Cond.lt (.var x) (.var y)).evalB B ρ = some true) : ρ.vars x < ρ.vars y := by
  simp only [evalB_condLt_iff, evalB_var_iff] at h
  obtain ⟨a, b, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  simpa using hr.symm

/-- And what its falsity says. -/
theorem le_of_condLt_false {B : ℕ} {x y : String} {ρ : Env}
    (h : (Cond.lt (.var x) (.var y)).evalB B ρ = some false) : ρ.vars y ≤ ρ.vars x := by
  simp only [evalB_condLt_iff, evalB_var_iff] at h
  obtain ⟨a, b, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  have := hr.symm
  simp only [decide_eq_false_iff_not, not_lt] at this
  exact this

/-- **The counted scan**, `while x < m do c` where the body moves `x` up
by one and `m` holds `N` throughout. This is the shape of every flat
pass in the repo, and here it costs neither a potential nor a variant:
the caller owes a body specification and the two bounds `x ≤ N` and
`x, m < B` that the invariant already carries.

The postcondition is the one the caller wants after a scan — the
invariant, with the counter *at* the bound, rather than a failed
condition to be read again.

The two counter names and the cost are **explicit**, because nothing but
the conclusion determines them: a use whose result is consumed by an
`obtain` has no expected type, so with `x` and `m` implicit the
invariant's own hypotheses — `∀ σ, I σ → σ.vars x < B` — are asked to
elaborate against a metavariable and fail. `B`, `P` and `c` stay
implicit; the body specification determines all three. -/
theorem Spec.forRange (x m : String) (I : Env → Prop) (N Kb K : ℕ)
    (hxB : ∀ σ, I σ → σ.vars x < B) (hmB : ∀ σ, I σ → σ.vars m < B)
    (hm : ∀ σ, I σ → σ.vars m = N) (hxN : ∀ σ, I σ → σ.vars x ≤ N)
    (hbody : Spec B (fun σ => I σ ∧ σ.vars x < N) c
      (fun σ σ' => I σ' ∧ σ'.vars x = σ.vars x + 1) Kb)
    (hPI : ∀ σ, P σ → I σ) (hK : ∀ σ, P σ → (Kb + 4) * (N - σ.vars x) + 4 ≤ K) :
    Spec B P (.while (.lt (.var x) (.var m)) c) (fun _ σ' => I σ' ∧ σ'.vars x = N) K := by
  have hsize : (Cond.lt (Expr.var x) (Expr.var m)).size = 3 := by simp
  refine ((Spec.while_potential (b := .lt (.var x) (.var m)) (c := c) I
    (fun σ => (Kb + 4) * (N - σ.vars x))
    (fun σ hI => evalB_condLt_vars (hxB σ hI) (hmB σ hI)) ?_ hPI ?_).post ?_)
  · intro σ hI hv
    have hlt : σ.vars x < N := by
      have := lt_of_condLt_true hv
      rw [hm σ hI] at this
      exact this
    obtain ⟨σ', hr, hI', hx'⟩ := hbody σ ⟨hI, hlt⟩
    refine ⟨σ', Kb, hr, hI', ?_⟩
    show 1 + 3 + Kb + (Kb + 4) * (N - σ'.vars x) ≤ (Kb + 4) * (N - σ.vars x)
    have hdrop : N - σ'.vars x + 1 = N - σ.vars x := by rw [hx']; omega
    exact le_of_eq (by rw [← hdrop]; ring)
  · intro σ hσ
    show (Kb + 4) * (N - σ.vars x) + 1 + 3 ≤ K
    have h := hK σ hσ
    have hre : (Kb + 4) * (N - σ.vars x) + 1 + 3 = (Kb + 4) * (N - σ.vars x) + 4 := by ring
    rw [hre]
    exact h
  · intro σ σ' _ hq
    refine ⟨hq.1, ?_⟩
    have := le_of_condLt_false hq.2
    have h₁ := hm σ' hq.1
    have h₂ := hxN σ' hq.1
    omega

/-- **The counted scan from zero**, `x := 0; while x < m do c`, which is
what a flat pass over an array is actually written as: `Spec.forRange`
starts wherever the counter happens to stand, and every site in the repo
starts it at zero on the line before.

Nothing is asked about the initial state but that the invariant holds
once the counter has been zeroed — which is where a caller's "the array
is the right length and nothing of it is filled in yet" goes. The two
bounds `Spec.forRange` wants of the counter follow from `N < B` and the
invariant's own `x ≤ N` and `m = N`, so a counter phase owes neither;
and the cost is not a parameter but a *result*, `(Kb + 4) · N + 6`, the
loop's `(Kb + 4) · N + 4` plus the two the initialisation costs.

A caller whose precondition is not literally this one composes with
`Spec.pre`; there is deliberately no `P` and no `K` to be left
undetermined here. -/
theorem Spec.forRangeZero (x m : String) (I : Env → Prop) (N Kb : ℕ) (hNB : N < B)
    (hxN : ∀ σ, I σ → σ.vars x ≤ N) (hm : ∀ σ, I σ → σ.vars m = N)
    (hbody : Spec B (fun σ => I σ ∧ σ.vars x < N) c
      (fun σ σ' => I σ' ∧ σ'.vars x = σ.vars x + 1) Kb) :
    Spec B (fun σ => I (σ.setVar x 0))
      (.seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) c))
      (fun _ σ' => I σ' ∧ σ'.vars x = N) ((Kb + 4) * N + 6) := by
  intro σ hσ
  obtain ⟨σ', hrun, hI', hxN'⟩ :=
    (Spec.forRange x m I N Kb ((Kb + 4) * N + 4)
      (fun _ hτ => lt_of_le_of_lt (hxN _ hτ) hNB) (fun _ hτ => hm _ hτ ▸ hNB) hm hxN hbody
      (fun _ h => h)
      (fun _ _ => Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) 4)).run hσ
  exact ⟨σ', (Run.seq (Run.assign (v := 0) (by simp; omega)) hrun).mono (by simp; omega),
    hI', hxN'⟩

end Lax759944Proofs.Legacy.Reasoning
