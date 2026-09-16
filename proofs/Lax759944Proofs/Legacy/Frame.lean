-- Adapted 2026-09-15 from word-ram-v4-33 at 0aa87e1f6e6add4abe4f4e0aff8fe4a28950b2ea.
-- Namespace relocated for use as a proof-only intermediate; semantics unchanged.
import Lax759944Proofs.Legacy.Reasoning

/-!
The frame rule: what a run *cannot* have changed, read off its syntax.

Almost every statement about a phase of an algorithm is half functional
and half negative. The functional half says what the phase computed; the
negative half says that everything else is where it was. Written by
hand, the negative half is a universally quantified conjunct per lemma —
`∀ y, y ≠ "ro" → y ≠ "cnted" → ρ'.vars y = ρ.vars y` — which the caller
then has to destructure again at every use, and which has to be
re-established by hand every time two phases are composed.

It need not be written at all. Which scalars a command may assign to,
which arrays it may store into, and whether it touches the input tape
are all *syntactic*, and the environment of `Imp` is aliasing-free, so
the syntactic answer is the true one. This file computes the three
answers as `Com.wvars`, `Com.warrs` and `Com.reads`, and proves the
three frame theorems by the induction that `BigStep.out_eq` already
does for the output tape.

A call site then pays `by decide` — or `by simp`, which is faster on
long lists of string literals — against the concrete syntax of its own
program, in place of carrying and destructuring a quantified hypothesis.
The four `Env` fields are covered uniformly: `vars` by `Run.frame_var`,
`arrs` by `Run.frame_arr`, `inp` by `Run.frame_inp` and `out` by
`Run.out_eq` of `Reasoning`, whose `Com.NoWrite` is the same idea
predating this file.

The lists are over-approximations, deliberately: `wvars` of an `ite`
unions both branches rather than asking which one runs, and `while`
takes its body's whether or not the loop turns at all. A frame condition
is wanted for names the command never mentions, and for those the crude
answer is already exact.
-/

namespace Lax759944Proofs.Legacy.Imp

/-- The scalar variables a command may assign to. Both branches of an
`ite` count, and the body of a `while` counts once. -/
def Com.wvars : Com → List String
  | .skip => []
  | .assign x _ => [x]
  | .store _ _ _ => []
  | .seq c d => c.wvars ++ d.wvars
  | .ite _ c d => c.wvars ++ d.wvars
  | .while _ c => c.wvars
  | .read x => [x]
  | .write _ => []

/-- The arrays a command may store into. -/
def Com.warrs : Com → List String
  | .skip => []
  | .assign _ _ => []
  | .store a _ _ => [a]
  | .seq c d => c.warrs ++ d.warrs
  | .ite _ c d => c.warrs ++ d.warrs
  | .while _ c => c.warrs
  | .read _ => []
  | .write _ => []

/-- The command contains a `read`, so it may consume the input tape. -/
def Com.reads : Com → Prop
  | .skip => False
  | .assign _ _ => False
  | .store _ _ _ => False
  | .seq c d => c.reads ∨ d.reads
  | .ite _ c d => c.reads ∨ d.reads
  | .while _ c => c.reads
  | .read _ => True
  | .write _ => False

/-- `Com.reads` is decided by the same recursion that defines it, so a
call site discharges `¬ c.reads` on concrete syntax by `decide`. -/
def Com.decReads : (c : Com) → Decidable c.reads
  | .skip => decidable_of_iff False (by rw [Com.reads])
  | .assign _ _ => decidable_of_iff False (by rw [Com.reads])
  | .store _ _ _ => decidable_of_iff False (by rw [Com.reads])
  | .seq c d =>
      have := c.decReads
      have := d.decReads
      decidable_of_iff (c.reads ∨ d.reads) (by rw [Com.reads])
  | .ite _ c d =>
      have := c.decReads
      have := d.decReads
      decidable_of_iff (c.reads ∨ d.reads) (by rw [Com.reads])
  | .while _ c =>
      have := c.decReads
      decidable_of_iff c.reads (by rw [Com.reads])
  | .read _ => decidable_of_iff True (by rw [Com.reads])
  | .write _ => decidable_of_iff False (by rw [Com.reads])

instance : DecidablePred Com.reads := Com.decReads

/-- `Com.NoWrite` of `Reasoning` — the output tape's frame condition,
which predates this file — decided by the same recursion, so all four
`Env` fields are framed by one `by decide` apiece. -/
def Com.decNoWrite : (c : Com) → Decidable c.NoWrite
  | .skip => decidable_of_iff True (by rw [Com.NoWrite])
  | .assign _ _ => decidable_of_iff True (by rw [Com.NoWrite])
  | .store _ _ _ => decidable_of_iff True (by rw [Com.NoWrite])
  | .seq c d =>
      have := c.decNoWrite
      have := d.decNoWrite
      decidable_of_iff (c.NoWrite ∧ d.NoWrite) (by rw [Com.NoWrite])
  | .ite _ c d =>
      have := c.decNoWrite
      have := d.decNoWrite
      decidable_of_iff (c.NoWrite ∧ d.NoWrite) (by rw [Com.NoWrite])
  | .while _ c =>
      have := c.decNoWrite
      decidable_of_iff c.NoWrite (by rw [Com.NoWrite])
  | .read _ => decidable_of_iff True (by rw [Com.NoWrite])
  | .write _ => decidable_of_iff False (by rw [Com.NoWrite])

instance : DecidablePred Com.NoWrite := Com.decNoWrite

/-! ### Equation lemmas, materialized here

`Com.wvars`, `Com.warrs` and `Com.reads` are defined by `match`, so
their equation lemmas and match splitters are created on first use.
Downstream a first use is `simp [Com.wvars]` inside some algorithm
proof, and creating them there leaves *that* package holding
declarations named under `Lax759944Proofs.Legacy`, which the archive's namespace
rule rejects. These three trivial statements ask for them here; every
later `simp` finds them among its imports and creates nothing. This is
the standing kit rule, and it applies to every match-defined function
this kit ever exports. -/

@[simp] theorem Com.wvars_skip : Com.skip.wvars = [] := by simp [Com.wvars]

@[simp] theorem Com.warrs_skip : Com.skip.warrs = [] := by simp [Com.warrs]

@[simp] theorem Com.not_reads_skip : ¬ Com.skip.reads := by simp [Com.reads]

end Lax759944Proofs.Legacy.Imp

namespace Lax759944Proofs.Legacy.Reasoning

open Lax759944Proofs.Legacy.Imp

/-! ### The three frame theorems

Each is the induction of `BigStep.out_eq`, driven by the syntactic
over-approximation instead of by a hand-written predicate. They are
stated on `BigStep` — where the induction lives — and then on `Run`,
which is what an algorithm proof has in hand. -/

/-- A run leaves every scalar the command cannot assign to alone. -/
theorem _root_.Lax759944Proofs.Legacy.Imp.BigStep.vars_eq {c : Com} {σ σ' : Env} {k : ℕ}
    (h : BigStep c σ σ' k) {y : String} (hy : y ∉ c.wvars) : σ'.vars y = σ.vars y := by
  induction h with
  | skip => rfl
  | assign _ => simp only [Com.wvars, List.mem_singleton] at hy; simp [Env.setVar, hy]
  | store _ _ _ => rfl
  | seq _ _ ih ih' =>
      simp only [Com.wvars, List.mem_append, not_or] at hy
      rw [ih' hy.2, ih hy.1]
  | ite_true _ _ ih => simp only [Com.wvars, List.mem_append, not_or] at hy; exact ih hy.1
  | ite_false _ _ ih => simp only [Com.wvars, List.mem_append, not_or] at hy; exact ih hy.2
  | while_true _ _ _ ih ih' =>
      simp only [Com.wvars] at hy
      rw [ih' (by simpa [Com.wvars] using hy), ih hy]
  | while_false _ => rfl
  | read _ => simp only [Com.wvars, List.mem_singleton] at hy; simp [Env.setVar, hy]
  | write _ => rfl

/-- A run leaves every array the command cannot store into alone. -/
theorem _root_.Lax759944Proofs.Legacy.Imp.BigStep.arrs_eq {c : Com} {σ σ' : Env} {k : ℕ}
    (h : BigStep c σ σ' k) {a : String} (ha : a ∉ c.warrs) : σ'.arrs a = σ.arrs a := by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => simp only [Com.warrs, List.mem_singleton] at ha; simp [Env.setArr, ha]
  | seq _ _ ih ih' =>
      simp only [Com.warrs, List.mem_append, not_or] at ha
      rw [ih' ha.2, ih ha.1]
  | ite_true _ _ ih => simp only [Com.warrs, List.mem_append, not_or] at ha; exact ih ha.1
  | ite_false _ _ ih => simp only [Com.warrs, List.mem_append, not_or] at ha; exact ih ha.2
  | while_true _ _ _ ih ih' =>
      simp only [Com.warrs] at ha
      rw [ih' (by simpa [Com.warrs] using ha), ih ha]
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

/-- A run of a command containing no `read` leaves the input tape
alone. -/
theorem _root_.Lax759944Proofs.Legacy.Imp.BigStep.inp_eq {c : Com} {σ σ' : Env} {k : ℕ}
    (h : BigStep c σ σ' k) (hr : ¬ c.reads) : σ'.inp = σ.inp := by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => rfl
  | seq _ _ ih ih' =>
      simp only [Com.reads, not_or] at hr
      rw [ih' hr.2, ih hr.1]
  | ite_true _ _ ih => simp only [Com.reads, not_or] at hr; exact ih hr.1
  | ite_false _ _ ih => simp only [Com.reads, not_or] at hr; exact ih hr.2
  | while_true _ _ _ ih ih' =>
      simp only [Com.reads] at hr
      rw [ih' (by simpa [Com.reads] using hr), ih hr]
  | while_false _ => rfl
  | read _ => exact absurd (by rw [Com.reads]; trivial) hr
  | write _ => rfl

/-- **The frame rule for scalars.** A name outside `c.wvars` has the
value it had. On concrete syntax the hypothesis is `by decide`.

The name is explicit: these are used inside `rw` chains, where the
alternative is an `(y := _)` at every step. -/
theorem Run.frame_var {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K)
    (y : String) (hy : y ∉ c.wvars) : σ'.vars y = σ.vars y := by
  obtain ⟨_, _, hbs⟩ := h.bigStep; exact hbs.vars_eq hy

/-- **The frame rule for arrays.** -/
theorem Run.frame_arr {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K)
    (a : String) (ha : a ∉ c.warrs) : σ'.arrs a = σ.arrs a := by
  obtain ⟨_, _, hbs⟩ := h.bigStep; exact hbs.arrs_eq ha

/-- **The frame rule for the input tape.** -/
theorem Run.frame_inp {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K)
    (hr : ¬ c.reads) : σ'.inp = σ.inp := by
  obtain ⟨_, _, hbs⟩ := h.bigStep; exact hbs.inp_eq hr

/-- The frame rule for scalars, through a syntactic inclusion. A phase
of a larger program is framed by the larger program's list, so a caller
carrying `y ∉ c.wvars` frames every sub-phase of `c` by one lemma. The
inclusion is `by decide` on concrete syntax, and is worth proving once
per pair rather than at every use. -/
theorem Run.frame_var_sub {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K)
    (y : String) {l : List String} (hsub : c.wvars ⊆ l) (hy : y ∉ l) :
    σ'.vars y = σ.vars y :=
  h.frame_var y fun hm => hy (hsub hm)

/-- A name framed off a command differs from every name the command
assigns to. This is how a frame hypothesis meets a lemma stated in
disequalities: `notMem_wvars_ne hy (by decide) : y ≠ "j"`. -/
theorem _root_.Lax759944Proofs.Legacy.Imp.notMem_wvars_ne {c : Com} {y z : String}
    (hy : y ∉ c.wvars) (hz : z ∈ c.wvars) : y ≠ z :=
  fun h => hy (h.symm ▸ hz)

/-- The scalars a command may assign to are finitely many, so a frame
condition over *all* names outside the list is one `funext` away when a
caller wants the whole function rather than one entry. -/
theorem Run.frame_vars_eqOn {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K)
    (hc : c.wvars = []) : σ'.vars = σ.vars :=
  funext fun y => h.frame_var y (by simp [hc])

/-- Likewise for the arrays. -/
theorem Run.frame_arrs_eqOn {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K)
    (hc : c.warrs = []) : σ'.arrs = σ.arrs :=
  funext fun a => h.frame_arr a (by simp [hc])

end Lax759944Proofs.Legacy.Reasoning
