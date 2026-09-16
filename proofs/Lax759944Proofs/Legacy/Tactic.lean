-- Adapted 2026-09-15 from word-ram-v4-33 at 0aa87e1f6e6add4abe4f4e0aff8fe4a28950b2ea.
-- Namespace relocated for use as a proof-only intermediate; semantics unchanged.
import Lax759944Proofs.Legacy.Spec

/-!
`run_vcg`: symbolic execution of a concrete `Com`, as a tactic.

A straight-line block of IMP+ is proved by hand the same way every time.
Apply `Run.assign` or `Run.store`, exhibit the value of the expression
one subexpression at a time, prove each of those values below `B`, chain
the pieces with `Run.seq`, split on every `ite`, and finish with
`Run.mono` against the cost the statement announces. `countBlock_spec`
in Lax15 is five lines of program and was twenty-one lines of proof;
`seenBlock_spec` is seven lines of program and was fifty-one. None of it
is mathematics.

`run_vcg` does the walk. What is left for the reader is exactly the two
things the walk cannot know: what the block *computed* — one goal per
control-flow path, in the environment the path ends in — and, where the
precondition is not literally a hypothesis, why each value stayed below
the bound.

Three implementation decisions are what make it usable.

* **The derivation is a `have` chain, not one term.** Every atomic run
  and every combination is `assert`ed as a named hypothesis and the
  consumed pieces are cleared. A single nested `Run.seq`/`Run.ite`
  application over a chain of `setVar`-bound environments blows the whnf
  heartbeat limit — this was learned the hard way — and the chain also
  keeps the local context of the goals the user sees down to a single
  `Run`.
* **The value bound is discharged where it arises, or deferred.** Each
  `_ < B` obligation is tried with `omega`, then with `simp` followed by
  `omega`, against the precondition as it stands at that point of the
  walk. What neither closes is handed back as a goal, in the branch it
  came from, with that branch's case hypotheses in scope — which is what
  a bound like `ρ.vars "cnted" = 0 → ρ.vars "u" < ρ.vars "w" →
  ρ.vars "ro" + 1 < B` needs.
* **A branch's case hypothesis is inaccessible.** Splitting `ite`s
  generate `ρ.vars "cnted" = 0` and its negation; naming them would
  invent names the user has to guess and that shift when the program
  does. They are in scope for `simp_all`, `omega` and `‹_›`, and that is
  the whole interface.

The two tape operations are walked like the rest. A `write` is an
`assign` whose value lands on the output tape, and asks nothing beyond
the value bound evaluating its expression already owes. A `read` is the
one command that can fail to have a derivation at all — the tape may be
exhausted — so it owes `σ.inp ≠ []`, taken from the precondition the way
an array's range condition is, and names what it read by `headD` and
`tail` the way an array read is named by `getD`.

Loops are deliberately not walked: `Spec.while_potential`,
`Spec.while_count` and `Spec.forRange` want an invariant and a potential,
which is content and not bookkeeping. A loop enters a block the way any
already-proved phase does — `run_vcg [my_loop_spec]` steps over the
command the specification is about, owing its precondition and giving
back its postcondition. Handed nothing, the tactic stops at the loop
with an error naming it, rather than guessing.
-/

namespace Lax759944Proofs.Legacy.Reasoning

open Lax759944Proofs.Legacy.Imp

/-! ### The rules the walk emits

The kit's own rules take their arguments implicitly, which is right for
a human and wrong for a metaprogram: an implicit that the premises do
not determine — the assigned variable of `Run.assign`, the untaken
branch of `Run.ite_true` — comes back as an unassigned metavariable. So
the walk emits these instead. They are the same rules with every
argument explicit and in a fixed order, plus the two conveniences a
symbolic execution wants: an operator's value in normal form (`m + n`,
not `Bop.add.apply m n`) and a condition's truth already decided. -/

namespace RunStep

/-! #### Evaluating an expression -/

theorem eval_lit (B n : ℕ) (σ : Env) (h : n < B) :
    (Expr.lit n).evalB B σ = some n := evalB_lit h

theorem eval_var (B : ℕ) (σ : Env) (x : String) (h : σ.vars x < B) :
    (Expr.var x).evalB B σ = some (σ.vars x) := evalB_var h

/-- An array read, with the value named by `getD` rather than left as an
existential: the walk owes the range condition anyway, and `getD` is the
form every invariant in the repo reads an array in. -/
theorem eval_get (B : ℕ) (σ : Env) (a : String) (i : Expr) (k : ℕ)
    (hi : i.evalB B σ = some k) (hk : k < (σ.arrs a).length)
    (h : (σ.arrs a).getD k 0 < B) :
    (Expr.get a i).evalB B σ = some ((σ.arrs a).getD k 0) := by
  refine evalB_get hi ?_ h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

theorem eval_add (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m + n < B) :
    (Expr.bin .add e f).evalB B σ = some (m + n) := evalB_bin he hf h

theorem eval_sub (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m - n < B) :
    (Expr.bin .sub e f).evalB B σ = some (m - n) := evalB_bin he hf h

theorem eval_mul (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m * n < B) :
    (Expr.bin .mul e f).evalB B σ = some (m * n) := evalB_bin he hf h

theorem eval_div (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m / n < B) :
    (Expr.bin .div e f).evalB B σ = some (m / n) := evalB_bin he hf h

theorem eval_and (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : Nat.land m n < B) :
    (Expr.bin .and e f).evalB B σ = some (Nat.land m n) := evalB_bin he hf h

theorem eval_or (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : Nat.lor m n < B) :
    (Expr.bin .or e f).evalB B σ = some (Nat.lor m n) := evalB_bin he hf h

theorem eval_xor (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : Nat.xor m n < B) :
    (Expr.bin .xor e f).evalB B σ = some (Nat.xor m n) := evalB_bin he hf h

theorem eval_shiftl (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m * 2 ^ n < B) :
    (Expr.bin .shiftl e f).evalB B σ = some (m * 2 ^ n) := evalB_bin he hf h

theorem eval_shiftr (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m / 2 ^ n < B) :
    (Expr.bin .shiftr e f).evalB B σ = some (m / 2 ^ n) := evalB_bin he hf h

/-! #### Deciding a condition

The walk splits on the *arithmetic* proposition, not on the `Bool` the
semantics returns, so that the hypothesis the user is left with is
`ρ.vars "cnted" = 0` and not `(Cond.eq _ _).evalB B ρ = some true`. -/

theorem cond_eq_true (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m = n) :
    (Cond.eq e f).evalB B σ = some true := by
  rw [evalB_condEq he hf, h]; simp

theorem cond_eq_false (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : ¬ m = n) :
    (Cond.eq e f).evalB B σ = some false := by
  rw [evalB_condEq he hf]; simp [h]

theorem cond_lt_true (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : m < n) :
    (Cond.lt e f).evalB B σ = some true := by
  rw [evalB_condLt he hf]; simp [h]

theorem cond_lt_false (B : ℕ) (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) (h : ¬ m < n) :
    (Cond.lt e f).evalB B σ = some false := by
  rw [evalB_condLt he hf]; simp [h]

/-! #### Running a command -/

theorem skip (B : ℕ) (σ : Env) : Run B .skip σ σ 1 := Run.skip

theorem assign (B : ℕ) (σ : Env) (x : String) (e : Expr) (v : ℕ)
    (h : e.evalB B σ = some v) :
    Run B (.assign x e) σ (σ.setVar x v) (1 + e.size) := Run.assign h

theorem store (B : ℕ) (σ : Env) (a : String) (i e : Expr) (idx v : ℕ)
    (hi : i.evalB B σ = some idx) (he : e.evalB B σ = some v)
    (hidx : idx < (σ.arrs a).length) :
    Run B (.store a i e) σ (σ.setArr a idx v) (1 + i.size + e.size) := Run.store hi he hidx

/-- **A read**, with the head of the tape and what is left of it named
by `headD` and `tail` rather than left as an existential — the same
choice `eval_get` makes, and for the same reason: the walk owes the side
condition anyway, and a hypothesis about the tape is then an equation
between two concrete lists. The side condition is that the tape is not
exhausted; a read from an exhausted tape has no derivation at all, so
this is the one command whose *definedness* the precondition has to
carry. -/
theorem read (B : ℕ) (σ : Env) (x : String) (h : σ.inp ≠ []) :
    Run B (.read x) σ { σ.setVar x (σ.inp.headD 0) with inp := σ.inp.tail } 1 := by
  refine Run.read (v := σ.inp.headD 0) (rest := σ.inp.tail) ?_
  cases hl : σ.inp with
  | nil => exact absurd hl h
  | cons v rest => simp

/-- **A write**: the value goes on the end of the output tape. Its being
below the bound is `evalB`'s obligation, so a write asks nothing beyond
what evaluating its expression already did. -/
theorem write (B : ℕ) (σ : Env) (e : Expr) (v : ℕ) (h : e.evalB B σ = some v) :
    Run B (.write e) σ { σ with out := σ.out ++ [v] } (1 + e.size) := Run.write h

theorem seq (B : ℕ) (c d : Com) (σ σ' σ'' : Env) (K K' : ℕ)
    (h : Run B c σ σ' K) (h' : Run B d σ' σ'' K') :
    Run B (.seq c d) σ σ'' (K + K') := h.seq h'

/-! #### A specification that covers a prefix of a block

Program text is right-nested: `a; (b; (c; d))`. So a specification about
*two* commands is about no node of a three-command block — it is about
`.seq a b`, which the block does not contain — and a walk that can only
match a whole node or a suffix cannot use it. `Csr.loadRow_spec` is
exactly that specification, and the block it was written for opens with
a command of its own.

`SeqSplit p r w` says that the block `w` runs the commands of `p`, in
order, and then `r`; `seq_split` is the `seq` rule for that
decomposition. Inverting a `seq` is what makes it work, and `Run` is not
an inductive — it is a cost bound over `BigStepB` — so the inversion
happens at the level the semantics is defined on. -/

/-- `SeqSplit p r w`: the block `w` runs the commands of `p` and then
`r`. Both are right-nested; what `p` does not have is a last command
ending the block. -/
inductive SeqSplit : Com → Com → Com → Prop
  /-- The prefix's last command, with the remainder behind it. -/
  | one (a r : Com) : SeqSplit a r (.seq a r)
  /-- One more command in front of the prefix. -/
  | cons (a p r w : Com) (h : SeqSplit p r w) : SeqSplit (.seq a p) r (.seq a w)

/-- **Taking a `seq` apart.** The two halves' costs are known only to add
up to at most the whole's, since a `Run`'s cost is a bound and not a
value. -/
theorem seq_inv (B : ℕ) (c d : Com) (σ σ'' : Env) (K : ℕ) (h : Run B (.seq c d) σ σ'' K) :
    ∃ σ' K₁ K₂, Run B c σ σ' K₁ ∧ Run B d σ' σ'' K₂ ∧ K₁ + K₂ ≤ K := by
  obtain ⟨k, hk, hbs⟩ := h
  cases hbs with
  | seq h₁ h₂ => exact ⟨_, _, _, ⟨_, le_rfl, h₁⟩, ⟨_, le_rfl, h₂⟩, hk⟩

/-- **Stepping over a prefix.** A run of the prefix and a run of what
follows it make a run of the block they split, at the sum of their
costs — which is `seq` again, rebracketed as often as the prefix is
long. -/
theorem seq_split (B : ℕ) (p r w : Com) (hs : SeqSplit p r w) :
    ∀ (σ σ₁ σ₂ : Env) (K₁ K₂ : ℕ), Run B p σ σ₁ K₁ → Run B r σ₁ σ₂ K₂ →
      Run B w σ σ₂ (K₁ + K₂) := by
  induction hs with
  | one a r => intro σ σ₁ σ₂ K₁ K₂ h₁ h₂; exact h₁.seq h₂
  | cons a p r w _ ih =>
      intro σ σ₁ σ₂ K₁ K₂ h₁ h₂
      obtain ⟨σ', Ka, Kb, ha, hb, hk⟩ := seq_inv B a p σ σ₁ K₁ h₁
      exact (ha.seq (ih σ' σ₁ σ₂ Kb K₂ hb h₂)).mono (by omega)

theorem ite_true (B : ℕ) (b : Cond) (c d : Com) (σ σ' : Env) (K : ℕ)
    (hb : b.evalB B σ = some true) (h : Run B c σ σ' K) :
    Run B (.ite b c d) σ σ' (1 + b.size + K) := Run.ite_true hb h

theorem ite_false (B : ℕ) (b : Cond) (c d : Com) (σ σ' : Env) (K : ℕ)
    (hb : b.evalB B σ = some false) (h : Run B d σ σ' K) :
    Run B (.ite b c d) σ σ' (1 + b.size + K) := Run.ite_false hb h

theorem mono (B : ℕ) (c : Com) (σ σ' : Env) (K K' : ℕ)
    (h : Run B c σ σ' K) (hK : K ≤ K') : Run B c σ σ' K' := h.mono hK

/-- Using a specification the caller handed the walk. `Spec.run` with
its arguments explicit, so that a sub-program the walk must not unfold —
a loop, or a phase already proved — enters as an opaque step. -/
theorem use (B : ℕ) (P : Env → Prop) (c : Com) (Q : Env → Env → Prop) (K : ℕ)
    (h : Spec B P c Q K) (σ : Env) (hσ : P σ) : ∃ σ', Run B c σ σ' K ∧ Q σ σ' := h σ hσ

end RunStep

/-! ### The walk -/

section Meta

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

namespace RunVCG

/-- What the walk carries: the value bound, the specifications it may
step over, and the obligations it could not close on the spot. -/
structure Cfg where
  /-- The value bound `B` of the goal. -/
  B : Lean.Expr
  /-- Deferred `_ < B` (and array-range) obligations, in walk order. -/
  side : IO.Ref (Array MVarId)
  /-- Every specification the caller supplied, in the order given. The
  walk consumes this list as it goes — see `useSpec` — and carries the
  part still unconsumed separately; this field is the whole of it, kept
  for the error message. -/
  specs : Array Lean.Expr := #[]

private def errorCount (log : MessageLog) : Nat :=
  log.unreported.foldl (init := 0) fun n m => if m.severity matches .error then n + 1 else n

/-- Close a goal with the standard discharger, reporting whether it
worked and leaving the state untouched — including the message log —
when it did not.

Three things have to be got right, and the obvious spelling gets none of
them.

* **The attempt must not be allowed to recover.** `Lean.Elab.Tactic.run`
  starts a *fresh* tactic context, and `Context.recover` defaults to
  `true` there, so a `withoutRecover` on the outside has no effect. With
  recovery on, a discharger that gets part of the way — `simp` normalizes
  the goal, the `omega` behind `<;>` then fails — does not fail: the `<;>`
  elaborator logs `omega`'s error and `admitGoal`s the obligation with
  `sorryAx`, then throws the abort exception. So the recover flag is
  cleared *inside* `run`.
* **An abort is not a success.** `run` catches the abort exception on
  purpose and answers with the unsolved goals, which after `admitGoal` is
  the empty list. An empty goal list is therefore not evidence that the
  obligation was proved; that the assignment is free of `sorryAx` is.
* **The message log is part of the state.** An error logged by a recovered
  failure survives an exception, so a failed attempt is checked for new
  errors and `SavedState.restore` — which does roll the log back — puts
  them away.

Together these are what makes an undischargeable obligation come back as
a goal for the user instead of as an error at the `run_vcg` call. -/
def tryClose (g : MVarId) (stx : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  let errs := errorCount (← Core.getMessageLog)
  let ok ←
    try
      let gs ← Lean.Elab.Tactic.run g (withoutRecover (evalTactic stx))
      if !gs.isEmpty then pure false
      else if errorCount (← Core.getMessageLog) > errs then pure false
      else pure !(← instantiateMVars (mkMVar g)).hasSorry
    catch _ => pure false
  unless ok do s.restore
  return ok

/-- The discharger for a value-bound obligation: the precondition
verbatim, or the precondition after the environment chain is collapsed. -/
def sideTac : TacticM (TSyntax `tactic) := `(tactic| first | omega | (simp <;> omega))

/-- The discharger for the one arithmetic goal the walk creates itself,
`accumulated cost ≤ announced cost`, on concrete syntax.

`simp` normalizes the sizes of the expressions the walk went through to
numerals and `omega` does the arithmetic. The two must be tried
*together*: a `simp` that leaves the goal open still succeeds as a
tactic, so `first | simp | (simp <;> omega)` never reaches its second
branch, and an announced cost with a term in it — `30 * deg x v + 19`,
where the walk stepped over a loop whose cost is that term — was
reported as an unprovable cost bound rather than handed to `omega`. -/
def costTac : TacticM (TSyntax `tactic) := `(tactic| first | (simp <;> omega) | simp | omega)

/-- The discharger for the one obligation that is not arithmetic: that
the input tape a `read` is about is not exhausted. `omega` knows nothing
about lists, so this one takes the precondition's own conjunct
(`assumption`) or the same conjunct after the walk's chain of `setVar`s
is collapsed off the tape (`simp_all`). -/
def inpTac : TacticM (TSyntax `tactic) := `(tactic| first | assumption | simp_all)

/-- A value-bound obligation: tried at once, deferred if it does not go.
`tac` overrides the standard discharger, which is what the tape
condition of a `read` needs. -/
def mkSide (cfg : Cfg) (mv : MVarId) (ty : Lean.Expr) (tac : Option (TSyntax `tactic) := none) :
    TacticM Lean.Expr := mv.withContext do
  let m ← mkFreshExprSyntheticOpaqueMVar ty
  let tac ← match tac with | some t => pure t | none => sideTac
  unless ← tryClose m.mvarId! tac do
    cfg.side.modify (·.push m.mvarId!)
  return m

/-- One link of the `have` chain: assert `val` under its own type, and
hand back the hypothesis together with the goal that follows it. -/
def mkHave (mv : MVarId) (n : Name) (val : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr × MVarId) := mv.withContext do
  let ty ← instantiateMVars (← inferType val)
  let mv₁ ← mv.assert n ty val
  let (f, mv₂) ← mv₁.intro1P
  return (mkFVar f, ty, mv₂)

/-- Drop a run hypothesis that has been folded into a larger one. The
context a user is handed then holds one `Run`, not the twelve the walk
went through. -/
def dropRun (mv : MVarId) (h : Lean.Expr) : MetaM MVarId := do
  if let .fvar f := h then
    try mv.clear f catch _ => return mv
  else return mv

private def natLt (a b : Lean.Expr) : MetaM Lean.Expr := mkAppM ``LT.lt #[a, b]

/-- The value of a concrete expression, with a proof that it evaluates
to it. Every `_ < B` the evaluation needs becomes a side obligation. -/
partial def evalE (cfg : Cfg) (mv : MVarId) (σ e : Lean.Expr) :
    TacticM (Lean.Expr × Lean.Expr) := mv.withContext do
  let e ← withReducible <| whnf e
  match e.getAppFnArgs with
  | (``Lax759944Proofs.Legacy.Imp.Expr.lit, #[n]) =>
      let h ← mkSide cfg mv (← natLt n cfg.B)
      return (n, mkAppN (mkConst ``RunStep.eval_lit) #[cfg.B, n, σ, h])
  | (``Lax759944Proofs.Legacy.Imp.Expr.var, #[x]) =>
      let v := mkApp2 (mkConst ``Lax759944Proofs.Legacy.Imp.Env.vars) σ x
      let h ← mkSide cfg mv (← natLt v cfg.B)
      return (v, mkAppN (mkConst ``RunStep.eval_var) #[cfg.B, σ, x, h])
  | (``Lax759944Proofs.Legacy.Imp.Expr.get, #[a, i]) =>
      let (k, hi) ← evalE cfg mv σ i
      let arr := mkApp2 (mkConst ``Lax759944Proofs.Legacy.Imp.Env.arrs) σ a
      let len ← mkAppM ``List.length #[arr]
      let hk ← mkSide cfg mv (← natLt k len)
      let v ← mkAppM ``List.getD #[arr, k, mkNatLit 0]
      let h ← mkSide cfg mv (← natLt v cfg.B)
      return (v, mkAppN (mkConst ``RunStep.eval_get) #[cfg.B, σ, a, i, k, hi, hk, h])
  | (``Lax759944Proofs.Legacy.Imp.Expr.bin, #[op, e₁, e₂]) =>
      let (m, h₁) ← evalE cfg mv σ e₁
      let (n, h₂) ← evalE cfg mv σ e₂
      let op ← withReducible <| whnf op
      let (rule, v) ← match op.getAppFnArgs with
        | (``Lax759944Proofs.Legacy.Imp.Bop.add, _) => pure (``RunStep.eval_add, ← mkAppM ``HAdd.hAdd #[m, n])
        | (``Lax759944Proofs.Legacy.Imp.Bop.sub, _) => pure (``RunStep.eval_sub, ← mkAppM ``HSub.hSub #[m, n])
        | (``Lax759944Proofs.Legacy.Imp.Bop.mul, _) => pure (``RunStep.eval_mul, ← mkAppM ``HMul.hMul #[m, n])
        | (``Lax759944Proofs.Legacy.Imp.Bop.div, _) => pure (``RunStep.eval_div, ← mkAppM ``HDiv.hDiv #[m, n])
        | (``Lax759944Proofs.Legacy.Imp.Bop.and, _) => pure (``RunStep.eval_and, ← mkAppM ``Nat.land #[m, n])
        | (``Lax759944Proofs.Legacy.Imp.Bop.or, _) => pure (``RunStep.eval_or, ← mkAppM ``Nat.lor #[m, n])
        | (``Lax759944Proofs.Legacy.Imp.Bop.xor, _) => pure (``RunStep.eval_xor, ← mkAppM ``Nat.xor #[m, n])
        | (``Lax759944Proofs.Legacy.Imp.Bop.shiftl, _) =>
            pure (``RunStep.eval_shiftl, ← mkAppM ``HMul.hMul #[m, ← mkAppM ``HPow.hPow #[mkNatLit 2, n]])
        | (``Lax759944Proofs.Legacy.Imp.Bop.shiftr, _) =>
            pure (``RunStep.eval_shiftr, ← mkAppM ``HDiv.hDiv #[m, ← mkAppM ``HPow.hPow #[mkNatLit 2, n]])
        | _ => throwError "run_vcg: unrecognized operator {op}"
      let h ← mkSide cfg mv (← natLt v cfg.B)
      return (v, mkAppN (mkConst rule) #[cfg.B, σ, e₁, e₂, m, n, h₁, h₂, h])
  | _ => throwError "run_vcg: cannot evaluate the expression {e}"

/-- The final environment and the cost of a `Run B c σ σ' K`. -/
private def runParts (ty : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  match ty.getAppFnArgs with
  | (``Run, #[_, _, _, σ', K]) => return (σ', K)
  | _ => throwError "run_vcg: not a Run judgment: {ty}"

/-- Is `h` a `Spec` at the walk's bound about the command `c`? If so, its
five arguments. -/
private def specAbout (cfg : Cfg) (c h : Lean.Expr) : MetaM (Option (Array Lean.Expr)) := do
  let ty ← instantiateMVars (← inferType h)
  let (``Spec, args@#[Bs, _, cs, _, _]) := ty.getAppFnArgs | return none
  unless ← isDefEq Bs cfg.B do return none
  unless ← isDefEq cs c do return none
  return some args

/-- The specification to step over `c` with, and what is left of the
list after it: **the first one not yet consumed**. Two commands with the
same text therefore take two different specifications, in the order they
were handed over.

When every specification about `c` has already been consumed the first
one is reused, and the list is left alone. That is what lets a phase
that a block invokes `n` times be handed over once — the reading a
single specification for a repeated call has to have — while `n`
specifications for `n` calls are still matched up in order. -/
private def pickSpec (cfg : Cfg) (c : Lean.Expr) (specs : Array Lean.Expr) :
    MetaM (Option (Lean.Expr × Array Lean.Expr × Array Lean.Expr)) := do
  for i in [:specs.size] do
    let h := specs[i]!
    if let some args ← specAbout cfg c h then
      return some (h, args, specs.extract 0 i ++ specs.extract (i + 1) specs.size)
  for h in cfg.specs do
    if let some args ← specAbout cfg c h then
      return some (h, args, specs)
  return none

/-! #### Blocks as lists of commands

What a prefix match needs: the commands of a right-nested block in
order, the block back from a nonempty list of them, and the `SeqSplit`
derivation that says a given prefix of the list is followed by the rest.
All three are syntax, so they are `Lean.Expr` surgery and no `MVarId` is
involved beyond reading the local context. -/

/-- The commands of a right-nested block, in order: `a; (b; c)` gives
`[a, b, c]`. Anything that is not a `seq` is a block of one command. -/
private partial def flattenSeq (c : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let c ← whnf c
  match c.getAppFnArgs with
  | (``Lax759944Proofs.Legacy.Imp.Com.seq, #[c₁, c₂]) => return #[c₁] ++ (← flattenSeq c₂)
  | _ => return #[c]

private def mkSeq (a b : Lean.Expr) : Lean.Expr :=
  mkApp2 (mkConst ``Lax759944Proofs.Legacy.Imp.Com.seq) a b

/-- The right-nested block of a nonempty list of commands. -/
private def nestSeq (cs : Array Lean.Expr) : Lean.Expr :=
  cs.pop.foldr mkSeq cs[cs.size - 1]!

/-- The derivation that the nonempty prefix `ps` is followed by `r`,
together with the block the two of them split. Built from the prefix's
last command outwards, which is the direction `SeqSplit.cons` adds
commands in. -/
private def mkSplit (ps : Array Lean.Expr) (r : Lean.Expr) : Lean.Expr × Lean.Expr :=
  let last := ps[ps.size - 1]!
  let rec go (i : Nat) (p w h : Lean.Expr) : Lean.Expr × Lean.Expr :=
    match i with
    | 0 => (h, w)
    | i + 1 =>
        let a := ps[i]!
        go i (mkSeq a p) (mkSeq a w)
          (mkAppN (mkConst ``RunStep.SeqSplit.cons) #[a, p, r, w, h])
  go (ps.size - 1) last (mkSeq last r)
    (mkAppN (mkConst ``RunStep.SeqSplit.one) #[last, r])

mutual

/-- If one of the supplied specifications is about this command, use it:
its precondition becomes an obligation, its postcondition a hypothesis,
and the walk resumes in the state it left, with that specification
struck off the list it carries. -/
partial def useSpec (cfg : Cfg) (mv : MVarId) (c σ : Lean.Expr) (specs : Array Lean.Expr)
    (kont : MVarId → Lean.Expr → Lean.Expr → Lean.Expr → Array Lean.Expr →
      TacticM (List MVarId)) :
    TacticM (Option (List MVarId)) := mv.withContext do
  let some (h, #[Bs, P, cs, Q, Ks], rest) ← pickSpec cfg c specs | return none
  let ty ← instantiateMVars (← inferType h)
  let hP ← mkFreshExprSyntheticOpaqueMVar (← whnfR (mkApp P σ))
  cfg.side.modify (·.push hP.mvarId!)
  let use := mkAppN (mkConst ``RunStep.use) #[Bs, P, cs, Q, Ks, h, σ, hP]
  let (hex, _, mv) ← mkHave mv `hspec use
  let .fvar hexF := hex | throwError "run_vcg: internal error"
  let #[s₁] ← mv.cases hexF | throwError "run_vcg: cannot open {ty}"
  let #[σ', .fvar hAnd] := s₁.fields | throwError "run_vcg: cannot open {ty}"
  let #[s₂] ← s₁.mvarId.cases hAnd | throwError "run_vcg: cannot open {ty}"
  let #[hrun, _] := s₂.fields | throwError "run_vcg: cannot open {ty}"
  return some (← kont s₂.mvarId σ' Ks hrun rest)

/-- **A specification about a prefix of this block.** The block's
commands are assembled into prefixes — two commands, then three, and so
on, stopping one short of the whole block, which the caller has already
tried as a node — and each prefix is offered to the specifications the
walk still carries. The first prefix one of them is about is stepped
over by it; what follows the prefix is then walked as a block of its
own, and the two are joined by `RunStep.seq_split`.

Shortest prefix first, and specifications in the order they were handed
over: a two-command specification therefore wins over a three-command
one about the same opening, and nothing here changes what a whole node
or a single command matches. -/
partial def usePrefix (cfg : Cfg) (mv : MVarId) (c₁ c₂ σ : Lean.Expr)
    (specs : Array Lean.Expr)
    (kont : MVarId → Lean.Expr → Lean.Expr → Lean.Expr → Array Lean.Expr →
      TacticM (List MVarId)) :
    TacticM (Option (List MVarId)) := do
  let cs ← mv.withContext do return #[c₁] ++ (← flattenSeq c₂)
  for k in [2:cs.size] do
    let ps := cs.extract 0 k
    let p := nestSeq ps
    let r := nestSeq (cs.extract k cs.size)
    unless (← mv.withContext <| pickSpec cfg p specs).isSome do continue
    let (hs, w) := mkSplit ps r
    return ← useSpec cfg mv p σ specs fun mv₁ σ₁ K₁ h₁ specs₁ =>
      exec cfg mv₁ r σ₁ specs₁ fun mv₂ σ₂ K₂ h₂ specs₂ => do
        let val := mkAppN (mkConst ``RunStep.seq_split)
          #[cfg.B, p, r, w, hs, σ, σ₁, σ₂, K₁, K₂, h₁, h₂]
        let (h, ty, mv₃) ← mkHave mv₂ `hrun val
        let mv₃ ← dropRun mv₃ h₁
        let mv₃ ← dropRun mv₃ h₂
        let (σ', K) ← runParts ty
        kont mv₃ σ' K h specs₂
  return none

/-- Walk `c` from `σ`, and hand the continuation the goal it is left
with, the environment the command ends in, the cost it accumulated, the
hypothesis carrying the derivation, and the specifications still
unconsumed. An `ite` calls the continuation once per branch — each
branch starting from the same specifications, since the branches are
alternative paths and not successive commands; the goals of all branches
are concatenated. -/
partial def exec (cfg : Cfg) (mv : MVarId) (c σ : Lean.Expr) (specs : Array Lean.Expr)
    (kont : MVarId → Lean.Expr → Lean.Expr → Lean.Expr → Array Lean.Expr →
      TacticM (List MVarId)) :
    TacticM (List MVarId) := do
  -- A supplied specification wins over the syntax: that is how a loop, or
  -- a phase already proved, is stepped over instead of unfolded.
  if let some r ← useSpec cfg mv c σ specs kont then return r
  let c ← mv.withContext <| whnf c
  match c.getAppFnArgs with
  | (``Lax759944Proofs.Legacy.Imp.Com.skip, _) =>
      let val := mkAppN (mkConst ``RunStep.skip) #[cfg.B, σ]
      let (h, ty, mv) ← mkHave mv `hrun val
      let (σ', K) ← runParts ty
      kont mv σ' K h specs
  | (``Lax759944Proofs.Legacy.Imp.Com.assign, #[x, e]) =>
      let (v, he) ← evalE cfg mv σ e
      let val := mkAppN (mkConst ``RunStep.assign) #[cfg.B, σ, x, e, v, he]
      let (h, ty, mv) ← mkHave mv `hrun val
      let (σ', K) ← runParts ty
      kont mv σ' K h specs
  | (``Lax759944Proofs.Legacy.Imp.Com.store, #[a, i, e]) =>
      let (idx, hi) ← evalE cfg mv σ i
      let (v, he) ← evalE cfg mv σ e
      let arr := mkApp2 (mkConst ``Lax759944Proofs.Legacy.Imp.Env.arrs) σ a
      let len ← mv.withContext <| mkAppM ``List.length #[arr]
      let hidx ← mkSide cfg mv (← mv.withContext <| natLt idx len)
      let val := mkAppN (mkConst ``RunStep.store) #[cfg.B, σ, a, i, e, idx, v, hi, he, hidx]
      let (h, ty, mv) ← mkHave mv `hrun val
      let (σ', K) ← runParts ty
      kont mv σ' K h specs
  | (``Lax759944Proofs.Legacy.Imp.Com.read, #[x]) =>
      let inp := mkApp (mkConst ``Lax759944Proofs.Legacy.Imp.Env.inp) σ
      let nil ← mv.withContext <| mkAppOptM ``List.nil #[mkConst ``Nat]
      let hne ← mkSide cfg mv (← mv.withContext <| mkAppM ``Ne #[inp, nil]) (← inpTac)
      let val := mkAppN (mkConst ``RunStep.read) #[cfg.B, σ, x, hne]
      let (h, ty, mv) ← mkHave mv `hrun val
      let (σ', K) ← runParts ty
      kont mv σ' K h specs
  | (``Lax759944Proofs.Legacy.Imp.Com.write, #[e]) =>
      let (v, he) ← evalE cfg mv σ e
      let val := mkAppN (mkConst ``RunStep.write) #[cfg.B, σ, e, v, he]
      let (h, ty, mv) ← mkHave mv `hrun val
      let (σ', K) ← runParts ty
      kont mv σ' K h specs
  | (``Lax759944Proofs.Legacy.Imp.Com.seq, #[c₁, c₂]) =>
      -- A handed specification about a *prefix* of this block wins over
      -- walking its first command alone: the block is right-nested, so a
      -- specification about two commands is about no node of it.
      if let some gs ← usePrefix cfg mv c₁ c₂ σ specs kont then return gs
      exec cfg mv c₁ σ specs fun mv₁ σ₁ K₁ h₁ specs₁ =>
        exec cfg mv₁ c₂ σ₁ specs₁ fun mv₂ σ₂ K₂ h₂ specs₂ => do
          let val := mkAppN (mkConst ``RunStep.seq) #[cfg.B, c₁, c₂, σ, σ₁, σ₂, K₁, K₂, h₁, h₂]
          let (h, ty, mv₃) ← mkHave mv₂ `hrun val
          let mv₃ ← dropRun mv₃ h₁
          let mv₃ ← dropRun mv₃ h₂
          let (σ', K) ← runParts ty
          kont mv₃ σ' K h specs₂
  | (``Lax759944Proofs.Legacy.Imp.Com.ite, #[b, c₁, c₂]) =>
      let bw ← mv.withContext <| whnf b
      let (e₁, e₂, trueRule, falseRule, isEq) ← match bw.getAppFnArgs with
        | (``Lax759944Proofs.Legacy.Imp.Cond.eq, #[e₁, e₂]) =>
            pure (e₁, e₂, ``RunStep.cond_eq_true, ``RunStep.cond_eq_false, true)
        | (``Lax759944Proofs.Legacy.Imp.Cond.lt, #[e₁, e₂]) =>
            pure (e₁, e₂, ``RunStep.cond_lt_true, ``RunStep.cond_lt_false, false)
        | _ => throwError "run_vcg: cannot evaluate the condition {b}"
      let (m, h₁) ← evalE cfg mv σ e₁
      let (n, h₂) ← evalE cfg mv σ e₂
      let p := if isEq then
          mkAppN (mkConst ``Eq [Level.one]) #[mkConst ``Nat, m, n]
        else
          mkAppN (mkConst ``LT.lt [Level.zero]) #[mkConst ``Nat, mkConst ``instLTNat, m, n]
      let (sT, sF) ← mv.byCases p (← mkFreshUserName `hcase)
      let branch (sB : ByCasesSubgoal) (rule : Name) (body : Lean.Expr) (pos : Bool) := do
        let mvB := sB.mvarId
        let hc := mkFVar sB.fvarId
        let hb := mkAppN (mkConst rule) #[cfg.B, σ, e₁, e₂, m, n, h₁, h₂, hc]
        exec cfg mvB body σ specs fun mv' σ' K' h' specs' => do
          let rule' := if pos then ``RunStep.ite_true else ``RunStep.ite_false
          let val := mkAppN (mkConst rule') #[cfg.B, b, c₁, c₂, σ, σ', K', hb, h']
          let (h, ty, mv'') ← mkHave mv' `hrun val
          let mv'' ← dropRun mv'' h'
          let (σ'', K) ← runParts ty
          kont mv'' σ'' K h specs'
      let gsT ← branch sT trueRule c₁ true
      let gsF ← branch sF falseRule c₂ false
      return gsT ++ gsF
  | _ =>
      let hint :=
        if cfg.specs.isEmpty then
          m!"(a loop is stepped over by handing run_vcg a Spec for it: \
            `run_vcg [my_loop_spec]`)"
        else
          m!"(no specification handed to run_vcg is about it: {specs.size} of \
            {cfg.specs.size} still unconsumed on this path, and none of the {cfg.specs.size} \
            has this command. A loop is stepped over only by a Spec whose command is \
            syntactically the one here.)"
      throwError "run_vcg: no rule for {c}\n{hint}"

end

/-! ### Recognizing the goal

Two shapes are accepted. `Spec B P c Q K` is the interface of `Spec.lean`
and is what a new phase lemma is stated in; the walk introduces the
initial state and takes the precondition apart, so that its conjuncts are
in scope for the value-bound obligations. `∃ σ' K', Run B c σ σ' K' ∧
K' ≤ K ∧ Q σ σ'` is the shape every phase lemma written before `Spec.lean`
has, and is accepted so that the tactic can be pointed at one without
restating it. -/

/-- Take a conjunctive precondition apart, so `omega` can see its parts.
Stops at anything that is not an `And`. -/
partial def splitAnds (mv : MVarId) (f : FVarId) : MetaM MVarId := do
  let old ← mv.withContext f.getType
  let ty ← mv.withContext do whnfR old
  match ty.and? with
  | some _ =>
      -- `cases` reduces the type itself, and it renumbers the hypotheses it
      -- reverts, so the decl must not be rewritten first.
      match ← mv.cases f with
      | #[s] =>
          match s.fields with
          | #[.fvar f₁, .fvar f₂] => splitAnds (← splitAnds s.mvarId f₁) f₂
          | _ => return s.mvarId
      | _ => return mv
  | none =>
      -- A precondition that is not a conjunction is still an application of
      -- the predicate; `omega` wants it beta-reduced.
      if ty == old then return mv else mv.changeLocalDecl f ty

/-- The goal shapes the walk closes. -/
inductive Shape
  /-- `∃ σ', Run B c σ σ' K ∧ Q σ σ'`, what `Spec` unfolds to. -/
  | spec
  /-- `∃ σ' K', Run B c σ σ' K' ∧ K' ≤ K ∧ Q σ σ'`, the legacy shape. -/
  | legacy

end RunVCG

open RunVCG in
/-- **Symbolically execute a concrete block of IMP+.**

The goal is a `Spec B P c Q K` — or the existential shape phase lemmas
had before `Spec`, or either of those with the state already introduced —
whose command `c` is built from `skip`, `assign`, `store`, `read`,
`write`, `seq` and `ite`. `run_vcg` runs it: it introduces the initial
state, takes the precondition apart, applies the rule of every construct
in turn as a `have`, splits every conditional on its test, and discharges
the announced cost bound.

What is left is one goal per control-flow path — the postcondition, in
the environment that path ends in, with the path's case hypotheses in
scope — followed by the value-bound obligations `omega` could not read
straight off the precondition. `simp_all` and `omega` are what close
them; `run_vcg <;> simp_all <;> omega` is the whole proof of a block
whose postcondition is a case analysis.

An obligation the discharger cannot close *entirely* is handed back
whole, in the state it arose in: a discharger that gets part of the way
leaves nothing behind, and never reports its failure as an error at the
`run_vcg` call.

`run_vcg [h₁, h₂]` walks around the commands `h₁` and `h₂` specify
instead of into them. That is how a `while` — whose invariant and
potential are content, not bookkeeping — and a phase already proved
enter a block: each becomes one step, owing its precondition and giving
back its postcondition.

**The specifications are consumed in order.** At each command the walk
takes the first specification in the list that is about *that* command,
and strikes it off; the next command with the same text takes the next
one. So a block that runs one operation twice under the same variable
names is proved by handing over two specifications, `run_vcg [first,
second]`, and they are used left to right — which is the only way to say
anything different about the two occurrences.

**A specification may cover a prefix of a block.** Program text is
right-nested — `a; (b; (c; d))` — so a specification about two commands
is about no *node* of a longer block. At each block the walk therefore
assembles the block's commands into prefixes, shortest first, and offers
each to the specifications it still carries before walking the block's
first command alone; the prefix a specification is about is stepped over
by it, and the rest of the block is walked. That is what lets a
two-command kit operation — `Csr.loadRow`, whose second read follows its
first write — enter in the middle of a block whose other commands the
walk handles itself.

Consumption runs along a path, not across the program: the two branches
of an `ite` each start from the specifications that reached the `ite`,
because they are alternatives and not successive commands.

Once every specification about a command has been consumed, a further
occurrence of that command reuses the first of them. That is what lets a
phase a block invokes `n` times be specified once — `run_vcg [phase]`
for `phase; phase` says the same thing about both — while `n`
specifications for `n` occurrences are still matched up in order.

A `while`, or any other command the walk has no rule for, with no
specification about it is an error naming the command, and says how many
of the specifications handed over are still unconsumed. -/
syntax (name := runVcg) "run_vcg" (" [" term,* "]")? : tactic

open RunVCG in
@[tactic runVcg] def evalRunVcg : Tactic := fun stx => do
  let side ← IO.mkRef (#[] : Array MVarId)
  let mv ← getMainGoal
  let specs ← mv.withContext do
    match stx with
    | `(tactic| run_vcg [$ts,*]) => ts.getElems.mapM fun t => elabTerm t none
    | _ => pure #[]
  -- `Spec B P c Q K` is a definition; unfold it and introduce.
  let mv ← mv.withContext do
    let t := (← instantiateMVars (← mv.getType)).consumeMData
    if t.isAppOf ``Spec then
      let t' ← withTransparency .default (whnf t)
      let mv ← mv.change t'
      let (_, mv) ← mv.intro1P
      let (f, mv) ← mv.intro1P
      splitAnds mv f
    else pure mv
  -- The goal a `have` leaves behind carries `mdata` (the `noImplicitLambda`
  -- annotation the `have` elaborator puts on the type it hands the rest of
  -- the proof). It is invisible when the goal is printed and fatal to a
  -- syntactic match, so it comes off before the shape is read: a block whose
  -- proof opens with a `have` is otherwise reported as "not an existential"
  -- over a goal that visibly is one.
  let target ← mv.withContext do
    return (← instantiateMVars (← mv.getType)).consumeMData
  -- Read `B`, `c`, `σ` and the announced cost off the target.
  let some (envTy, p) := target.app2? ``Exists
    | throwError "run_vcg: the goal is not an existential over the final state:\n{target}"
  let (shape, B, c, σ, K) ← lambdaTelescope p fun xs body => do
    unless xs.size == 1 do throwError "run_vcg: unexpected goal shape"
    match body.and? with
    | some (runTy, _) =>
        match runTy.getAppFnArgs with
        | (``Run, #[B, c, σ, _, K]) => pure (Shape.spec, B, c, σ, K)
        | _ => throwError "run_vcg: the goal does not begin with a Run judgment:\n{body}"
    | none =>
        match body.app2? ``Exists with
        | some (_, q) =>
            lambdaTelescope q fun _ body' => do
              match body'.and? with
              | some (runTy, rest) =>
                  match runTy.getAppFnArgs, rest.and? with
                  | (``Run, #[B, c, σ, _, _]), some (le, _) =>
                      match le.getAppFnArgs with
                      | (``LE.le, #[_, _, _, K]) => pure (Shape.legacy, B, c, σ, K)
                      | _ => throwError "run_vcg: no cost bound in\n{body'}"
                  | _, _ => throwError "run_vcg: unexpected goal shape:\n{body'}"
              | none => throwError "run_vcg: unexpected goal shape:\n{body'}"
        | none => throwError "run_vcg: unexpected goal shape:\n{body}"
  let cfg : Cfg := { B := B, side := side, specs := specs }
  let main ← exec cfg mv c σ specs fun mv' σf Kf hrun _ => mv'.withContext do
    let leTy ← mkAppM ``LE.le #[Kf, K]
    let leM ← mkFreshExprSyntheticOpaqueMVar leTy
    let runTerm := mkAppN (mkConst ``RunStep.mono) #[B, c, σ, σf, Kf, K, hrun, leM]
    unless ← tryClose leM.mvarId! (← costTac) do
      throwError "run_vcg: cannot prove the cost bound {leTy}"
    match shape with
    | .spec =>
        let pApp ← whnfR (mkApp p σf)
        let some (runGoal, qTy) := pApp.and?
          | throwError "run_vcg: unexpected goal shape:\n{pApp}"
        let qM ← mkFreshExprSyntheticOpaqueMVar (← whnfR qTy)
        let andTerm := mkAppN (mkConst ``And.intro) #[runGoal, qTy, runTerm, qM]
        mv'.assign (mkAppN (mkConst ``Exists.intro [Level.one]) #[envTy, p, σf, andTerm])
        let qG ← dropRun qM.mvarId! hrun
        return [qG]
    | .legacy =>
        let pApp ← whnfR (mkApp p σf)
        let some (_, q) := pApp.app2? ``Exists
          | throwError "run_vcg: unexpected goal shape:\n{pApp}"
        let inner ← whnfR (mkApp q Kf)
        let some (runGoal, rest) := inner.and?
          | throwError "run_vcg: unexpected goal shape:\n{inner}"
        let some (leGoal, qTy) := rest.and?
          | throwError "run_vcg: unexpected goal shape:\n{rest}"
        let leM' ← mkFreshExprSyntheticOpaqueMVar leGoal
        unless ← tryClose leM'.mvarId! (← costTac) do
          throwError "run_vcg: cannot prove the cost bound {leGoal}"
        let qM ← mkFreshExprSyntheticOpaqueMVar (← whnfR qTy)
        let hrun' ← do
          if ← isDefEq (← inferType hrun) runGoal then pure hrun else pure runTerm
        let restTerm := mkAppN (mkConst ``And.intro) #[leGoal, qTy, leM', qM]
        let andTerm := mkAppN (mkConst ``And.intro) #[runGoal, rest, hrun', restTerm]
        mv'.assign (mkAppN (mkConst ``Exists.intro [Level.one]) #[envTy, p, σf,
          mkAppN (mkConst ``Exists.intro [Level.one]) #[mkConst ``Nat, q, Kf, andTerm]])
        let qG ← dropRun qM.mvarId! hrun
        return [qG]
  replaceMainGoal (main ++ (← side.get).toList)

end Meta

/-! ### Worked examples

Small kit-local programs, so that the kit documents its own tactic. Each
is the whole proof: the tactic, and one combinator for what it leaves. -/

namespace Example

open Lax759944Proofs.Legacy.Imp

/-- An assignment: one goal, the postcondition in the updated
environment. -/
example (B : ℕ) : Spec B (fun ρ => ρ.vars "x" + 1 < B) (.assign "y" (.add (.var "x") (.lit 1)))
    (fun ρ ρ' => ρ'.vars "y" = ρ.vars "x" + 1) 4 := by
  run_vcg; simp

/-- A sequence: the walk threads the environment, and the cost of the
block is checked against the announced bound. -/
example (B : ℕ) : Spec B (fun ρ => ρ.vars "x" + 1 < B)
    (.seq (.assign "y" (.add (.var "x") (.lit 1))) (.assign "z" (.var "y")))
    (fun ρ ρ' => ρ'.vars "z" = ρ.vars "x" + 1) 6 := by
  run_vcg; simp

/-- A conditional: two goals, each with its branch's test in scope. -/
example (B : ℕ) (h : 1 < B) :
    Spec B (fun ρ => ρ.vars "x" < B ∧ ρ.vars "y" < B)
      (.ite (.lt (.var "x") (.var "y")) (.assign "m" (.lit 1)) (.assign "m" (.lit 0)))
      (fun ρ ρ' => (ρ'.vars "m" = 1 ↔ ρ.vars "x" < ρ.vars "y")) 7 := by
  run_vcg <;> simp_all

/-- A store: the range condition joins the value bounds as an
obligation. -/
example (B : ℕ) (h : 1 < B) :
    Spec B (fun ρ => ρ.vars "i" < B ∧ ρ.vars "i" < (ρ.arrs "a").length)
      (.store "a" (.var "i") (.lit 1))
      (fun ρ ρ' => ρ'.arrs "a" = (ρ.arrs "a").set (ρ.vars "i") 1) 4 := by
  run_vcg; simp

/-- Nested conditionals over a block that assigns in one leaf only —
the shape of a phase lemma, at kit scale. Four paths, four goals. -/
example (B : ℕ) (h : 1 < B) :
    Spec B (fun ρ => ρ.vars "c" < B ∧ ρ.vars "u" < B ∧ ρ.vars "w" < B ∧ ρ.vars "n" + 1 < B)
      (.ite (.eq (.var "c") (.lit 0))
        (.ite (.lt (.var "u") (.var "w"))
          (.seq (.assign "n" (.add (.var "n") (.lit 1))) (.assign "c" (.lit 1)))
          .skip)
        .skip)
      (fun ρ ρ' => (ρ.vars "c" = 0 ∧ ρ.vars "u" < ρ.vars "w" ∧ ρ'.vars "n" = ρ.vars "n" + 1) ∨
        ρ'.vars "n" = ρ.vars "n") 20 := by
  run_vcg <;> simp_all

/-- A read: the tape's head lands in the variable and the tape loses it.
The precondition carries the one thing the walk cannot know — that there
is a head — and carries it in the form a caller has it in, an equation
naming the head and the rest. No bound is owed: a read produces no
value, it moves one, and what a tape holds is `Env.InpBounded`'s
business. -/
example (B : ℕ) (v : ℕ) (rest : List ℕ) :
    Spec B (fun ρ => ρ.inp = v :: rest) (.read "t")
      (fun _ ρ' => ρ'.vars "t" = v ∧ ρ'.inp = rest) 1 := by
  run_vcg; simp_all

/-- A proof that opens the state itself and derives what the walk will
need before starting it — the shape of a loop body, whose invariant is a
definition the discharger cannot see into. The walk is happy to be
handed an already-introduced goal, `have`s and all.

It also shows what a `read` leaves behind: the walk names the value
`ρ.inp.headD 0`, so the bound on what was read is *not* the caller's
`v < B` until the tape equation has been used, and comes back as a goal
like any other bound the precondition does not carry verbatim. -/
example (B : ℕ) (v : ℕ) (rest : List ℕ) :
    Spec B (fun ρ => ρ.inp = v :: rest ∧ v < B) (.seq (.read "t") (.write (.var "t")))
      (fun ρ ρ' => ρ'.out = ρ.out ++ [v]) 3 := by
  rintro ρ ⟨hinp, hvB⟩
  have hne : ρ.inp ≠ [] := by rw [hinp]; simp
  run_vcg
  · simp [hinp]
  · simp [hinp, hvB]

/-! A sub-program the walk must not unfold — a loop, or a phase already
proved — enters as one step, by handing `run_vcg` its specification. The
precondition of the specification becomes an obligation and its
postcondition a hypothesis; the walk resumes in the state it leaves. -/

/-- A one-command sub-program, standing in for a phase. -/
def bump : Com := .assign "n" (.add (.var "n") (.lit 1))

/-- Its specification, itself proved by the walk. -/
theorem bump_spec (B : ℕ) :
    Spec B (fun ρ => ρ.vars "n" + 1 < B) bump
      (fun ρ ρ' => ρ'.vars "n" = ρ.vars "n" + 1) 4 := by
  run_vcg; simp

example (B : ℕ) :
    Spec B (fun ρ => ρ.vars "n" + 2 < B) (.seq bump bump)
      (fun ρ ρ' => ρ'.vars "n" = ρ.vars "n" + 2) 8 := by
  run_vcg [bump_spec B] <;> omega

/-- The same mechanism is what a `while` uses: `Spec.while_potential`,
`Spec.while_count` or `Spec.forRange` proves the loop, and the block it
sits in is walked around it. -/
example (B : ℕ) (loop : Com)
    (hloop : Spec B (fun ρ => ρ.vars "n" < B) loop (fun _ ρ' => ρ'.vars "n" = 0) 100) :
    Spec B (fun ρ => ρ.vars "n" < B ∧ 1 < B) (.seq loop (.assign "d" (.lit 1)))
      (fun _ ρ' => ρ'.vars "n" = 0 ∧ ρ'.vars "d" = 1) 102 := by
  run_vcg [hloop] <;> simp_all

/-- Two occurrences of one sub-program, told apart. `bump_at` says what
`bump` does from a *named* starting value, so the two occurrences want
two different instances of it, and `run_vcg` consumes them left to
right: the first `bump` is stepped over by `bump_at B 0` and the second
by `bump_at B 1`. Matching by command text alone would take the first
one twice — `bump` is literally the same term in both positions — and
leave the second occurrence claiming to start from `0`. -/
theorem bump_at (B n : ℕ) :
    Spec B (fun ρ => ρ.vars "n" = n ∧ n + 1 < B) bump
      (fun _ ρ' => ρ'.vars "n" = n + 1) 4 := by
  run_vcg; simp_all

example (B : ℕ) :
    Spec B (fun ρ => ρ.vars "n" = 0 ∧ 2 < B) (.seq bump bump)
      (fun _ ρ' => ρ'.vars "n" = 2) 8 := by
  run_vcg [bump_at B 0, bump_at B 1] <;> omega

/-- Two commands as one sub-program — the shape of `Csr.loadRow`, whose
pair of reads is one specification because the second reads a scalar the
first wrote. -/
def bump2 : Com := .seq bump bump

theorem bump2_spec (B : ℕ) :
    Spec B (fun ρ => ρ.vars "n" + 2 < B) bump2
      (fun ρ ρ' => ρ'.vars "n" = ρ.vars "n" + 2) 8 := by
  run_vcg [bump_spec B] <;> omega

/-- **A specification covering a prefix of the block.** The block is
`bump; (bump; d := 1)`, so the two `bump`s are not a node of it — they
are a prefix, and matching a handed specification against nodes alone
would walk into them. `run_vcg` assembles the prefix, steps over it with
`bump2_spec`, and walks the assignment that is left. -/
example (B : ℕ) :
    Spec B (fun ρ => ρ.vars "n" + 2 < B ∧ 1 < B)
      (.seq bump (.seq bump (.assign "d" (.lit 1))))
      (fun ρ ρ' => ρ'.vars "n" = ρ.vars "n" + 2 ∧ ρ'.vars "d" = 1) 10 := by
  run_vcg [bump2_spec B] <;> simp_all

/-- The prefix match does not disturb the order specifications are
consumed in: the two-command specification takes the first two commands
and the one-command specifications that follow it are still matched left
to right against what is left. -/
example (B : ℕ) :
    Spec B (fun ρ => ρ.vars "n" = 0 ∧ 4 < B) (.seq bump (.seq bump (.seq bump bump)))
      (fun _ ρ' => ρ'.vars "n" = 4) 16 := by
  run_vcg [bump2_spec B, bump_at B 2, bump_at B 3] <;> omega

/-- A value bound the walk cannot get at: the element an array read
produces is below `B` for a reason the precondition does not carry, so
neither `omega` nor `simp` then `omega` closes `_ < B`. It comes back as
a goal, in the state it arose in, and the reader discharges it — the
walk's other two obligations here, `ρ.vars "i" < B` for the index and
`ρ.vars "i" < (ρ.arrs "a").length` for the range, `omega` still reads
straight off the precondition.

This is the case a partially-succeeding discharger used to lose: `simp`
would normalize `List.getD` to `getElem?`, `omega` would fail on the
normalized goal, and the failure surfaced as an error at `run_vcg`
rather than as this goal. -/
example (B : ℕ) (helem : ∀ ρ : Env, (ρ.arrs "a").getD (ρ.vars "i") 0 < B) :
    Spec B (fun ρ => ρ.vars "i" < B ∧ ρ.vars "i" < (ρ.arrs "a").length)
      (.assign "y" (.get "a" (.var "i")))
      (fun ρ ρ' => ρ'.vars "y" = (ρ.arrs "a").getD (ρ.vars "i") 0) 5 := by
  run_vcg
  · simp
  · exact helem _

end Example

end Lax759944Proofs.Legacy.Reasoning
