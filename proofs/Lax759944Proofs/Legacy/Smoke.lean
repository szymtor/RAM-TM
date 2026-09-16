-- Adapted 2026-09-15 from word-ram-v4-33 at 0aa87e1f6e6add4abe4f4e0aff8fe4a28950b2ea.
-- Namespace relocated for use as a proof-only intermediate; semantics unchanged.
import Lax759944Proofs.Legacy.Transfer

/-!
The pipeline, end to end, on three programs.

These are tests of the tower, not of the algorithms. Each of the three
states one `Solves` predicate — layout, cost and value bound — and cashes
it in for a `ComputesInTime` of the concept by one application of the
transfer theorem, so that the hypothesis bundle is known to be
dischargeable and the conclusion is known to be a statement about the
machine that was submitted.

The three are chosen to exercise the parts that could be wrong
independently: `echo` writes inside a loop, so the output tape is part of
the loop invariant; `sum` accumulates, so its value bound is a genuine
statement about the input rather than about its length; `square` uses
`mul` and a shift, the operators no example downstream depends on, so
that they are known to flow through the compiler and the bounded
semantics.

What a program costs in this style is visible here: the invariant, the
loop step, the exit argument, and one arithmetic line for the constant.
The value bound adds one conjunct per quantity to the invariant, and
nothing else — the `evalB` obligations of the rules are discharged by
`simp` together with the functional ones, out of the same facts.
-/

namespace Lax759944Proofs.Legacy.Smoke

open Lax759944Proofs.Legacy.Ram Lax759944Proofs.Legacy.RamComputes Lax759944Proofs.Legacy.Imp Lax759944Proofs.Legacy.Compile
open Lax759944Proofs.Legacy.Reasoning Lax759944Proofs.Legacy.Transfer

/-! ### Echo: copy a length-prefixed input to the output -/

namespace Echo

/-- `i < n`, the loop condition. -/
def cond : Cond := .lt (.var "i") (.var "n")

/-- Read the next number, write it, count it. -/
def body : Com :=
  .seq (.read "v") (.seq (.write (.var "v")) (.assign "i" (.add (.var "i") (.lit 1))))

/-- Read the count, then copy that many numbers. -/
def com : Com :=
  .seq (.read "n") (.seq (.assign "i" (.lit 0)) (.while cond body))

/-- Three scalars, no arrays, two temporaries. -/
def layout : Layout := ⟨["n", "i", "v"], [], 2⟩

/-- The machine program. -/
def prog : Program := compileProgram layout com

/-- Length-prefixed inputs. -/
def dom : Set (List ℕ) := {x : List ℕ | ∃ xs, x = xs.length :: xs}

theorem com_ok : Com.Ok layout com := by
  simp [com, body, cond, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem const_eq : layout.const = 10 := by
  simp [Layout.const]

/-- The loop invariant: the counter has the input still to be read left
to go, what was written is what was read, and both the counter's target
and the numbers still to come are below the bound. -/
def Inv (B : ℕ) (σ₀ τ : Env) : Prop :=
  τ.vars "n" = τ.vars "i" + τ.inp.length ∧ τ.vars "n" < B ∧
    (∀ v ∈ τ.inp, v < B) ∧ τ.out ++ τ.inp = σ₀.out ++ σ₀.inp

/-- The loop copies whatever the input still holds, at a cost of at most
11 per number. -/
theorem loop_run {B : ℕ} (σ₀ : Env) (hI : Inv B σ₀ σ₀) :
    ∃ σ', Run B (.while cond body) σ₀ σ' (11 * σ₀.inp.length + 4) ∧
      σ'.out = σ₀.out ++ σ₀.inp := by
  have hstep : ∀ τ : Env, Inv B σ₀ τ → cond.evalB B τ = some true →
      ∃ τ', Run B body τ τ' 7 ∧ Inv B σ₀ τ' ∧ τ'.inp.length < τ.inp.length := by
    rintro τ ⟨hn, hnB, hinpB, hout⟩ hcond
    have hlt : τ.vars "i" < τ.vars "n" := by simp [cond] at hcond; omega
    obtain ⟨v, rest, hinp⟩ : ∃ v rest, τ.inp = v :: rest := by
      rcases h : τ.inp with _ | ⟨v, rest⟩
      · rw [h] at hn; simp at hn; omega
      · exact ⟨v, rest, rfl⟩
    have hvB : v < B := hinpB v (by rw [hinp]; exact List.mem_cons_self ..)
    refine ⟨_, Run.seq (Run.read hinp)
        (Run.seq (Run.write (v := v) (by simp [hvB]))
          (Run.assign (v := τ.vars "i" + 1) (by simp; omega))), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hinp] at hn ⊢; omega
    · simpa using hnB
    · intro u hu; exact hinpB u (by rw [hinp]; exact List.mem_cons_of_mem _ hu)
    · simp [hinp] at hout ⊢; simpa using hout
    · simp [hinp]
  obtain ⟨σ', hrun, ⟨hn, _, _, hout⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := cond) (c := body) (Inv B σ₀)
      (fun τ => τ.inp.length) 7
      (fun τ hτ => ⟨decide (τ.vars "i" < τ.vars "n"), by
        obtain ⟨hn, hnB, _, _⟩ := hτ; simp [cond]; omega⟩) hstep hI
  have hexit : ¬ σ'.vars "i" < σ'.vars "n" := by simp [cond] at hfalse; omega
  have hnil : σ'.inp = [] := by
    rcases h : σ'.inp with _ | ⟨u, rest⟩
    · rfl
    · rw [h] at hn; simp at hn; omega
  refine ⟨σ', hrun.mono (by simp [cond]), ?_⟩
  rw [hnil] at hout; simpa using hout

theorem solves : Solves layout com dom (fun x => x.tail)
    (fun x => x.sum + 2) (fun x => 11 * x.length + 7) where
  ok := com_ok
  inp := by
    rintro x ⟨xs, rfl⟩ v hv
    have : v ≤ (xs.length :: xs).sum := List.single_le_sum (by simp) v hv
    omega
  run := by
    rintro x ⟨xs, rfl⟩
    have hsum : (xs.length :: xs).sum = xs.length + xs.sum := by simp
    set B := (xs.length :: xs).sum + 2 with hB
    set σ₀ : Env := initEnv (fun _ => 0) (xs.length :: xs) with hσ₀
    obtain ⟨σ', hloop, hout⟩ :=
      loop_run (B := B) ({ σ₀.setVar "n" xs.length with inp := xs }.setVar "i" 0)
        ⟨by simp [hσ₀, initEnv], by simp; omega, by
          intro v hv
          have : v ≤ xs.sum := List.single_le_sum (by simp) v (by simpa using hv)
          simp; omega, by simp [hσ₀, initEnv]⟩
    refine ⟨fun _ => 0, σ', (Run.seq (Run.read (by simp [hσ₀, initEnv]))
      (Run.seq (Run.assign (x := "i") (v := 0) (by simp; omega)) hloop)).mono ?_, ?_⟩
    · simp; omega
    · rw [hout]; simp [hσ₀, initEnv]

/-- **Echo, end to end.** The compiled machine program copies a
length-prefixed input to the output within `110 * (|x| + 1)` steps, at
every word length at which the total of the input fits. -/
theorem prog_computesInTime {w : ℕ} (hw : ∀ x ∈ dom, x.sum + 7 ≤ 2 ^ w) :
    ComputesInTime w prog dom (fun x => x.tail) (fun x => 110 * (x.length + 1)) := by
  refine computesInTime_of_solves solves
    (fun x hx => fitsWords_of_max_le (by omega)
      (by have := hw x hx; simp [Layout.span, layout]; omega))
    (fun x _ => by rw [const_eq]; omega)

end Echo

/-! ### Sum: add up a length-prefixed input -/

namespace Sum

/-- `i < n`, the loop condition. -/
def cond : Cond := .lt (.var "i") (.var "n")

/-- Read the next number, add it to the running sum, count it. -/
def body : Com :=
  .seq (.read "v")
    (.seq (.assign "s" (.add (.var "s") (.var "v")))
      (.assign "i" (.add (.var "i") (.lit 1))))

/-- Read the count, then that many numbers, then write their sum. -/
def com : Com :=
  .seq (.read "n")
    (.seq (.assign "i" (.lit 0))
      (.seq (.assign "s" (.lit 0)) (.seq (.while cond body) (.write (.var "s")))))

/-- Four scalars, no arrays, two temporaries. -/
def layout : Layout := ⟨["n", "i", "s", "v"], [], 2⟩

/-- The machine program. -/
def prog : Program := compileProgram layout com

/-- Length-prefixed inputs. -/
def dom : Set (List ℕ) := {x : List ℕ | ∃ xs, x = xs.length :: xs}

theorem com_ok : Com.Ok layout com := by
  simp [com, body, cond, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem const_eq : layout.const = 10 := by
  simp [Layout.const]

/-- The loop invariant: the counter has the input still to be read left
to go, the sum of what was read is already in `s`, and nothing was
written. -/
def Inv (B : ℕ) (σ₀ τ : Env) : Prop :=
  τ.vars "n" = τ.vars "i" + τ.inp.length ∧ τ.vars "n" < B ∧
    τ.vars "s" + τ.inp.sum = σ₀.vars "s" + σ₀.inp.sum ∧ τ.out = σ₀.out

/-- The loop reads, counts and sums whatever the input still holds, at a
cost of at most 13 per number. The value bound is the one hypothesis the
unbounded version of this lemma does not have: the total that will be
accumulated has to fit. -/
theorem loop_run {B : ℕ} (σ₀ : Env) (hI : Inv B σ₀ σ₀)
    (hS : σ₀.vars "s" + σ₀.inp.sum < B) :
    ∃ σ', Run B (.while cond body) σ₀ σ' (13 * σ₀.inp.length + 4) ∧
      σ'.vars "s" = σ₀.vars "s" + σ₀.inp.sum ∧ σ'.out = σ₀.out := by
  have hstep : ∀ τ : Env, Inv B σ₀ τ → cond.evalB B τ = some true →
      ∃ τ', Run B body τ τ' 9 ∧ Inv B σ₀ τ' ∧ τ'.inp.length < τ.inp.length := by
    rintro τ ⟨hn, hnB, hs, hout⟩ hcond
    have hlt : τ.vars "i" < τ.vars "n" := by simp [cond] at hcond; omega
    obtain ⟨v, rest, hinp⟩ : ∃ v rest, τ.inp = v :: rest := by
      rcases h : τ.inp with _ | ⟨v, rest⟩
      · rw [h] at hn; simp at hn; omega
      · exact ⟨v, rest, rfl⟩
    have hsum : τ.vars "s" + v + rest.sum = σ₀.vars "s" + σ₀.inp.sum := by
      rw [hinp] at hs; simp at hs; omega
    refine ⟨_, Run.seq (Run.read hinp)
        (Run.seq (Run.assign (v := τ.vars "s" + v) (by simp; omega))
          (Run.assign (v := τ.vars "i" + 1) (by simp; omega))), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hinp] at hn ⊢; omega
    · simpa using hnB
    · simp; omega
    · simpa using hout
    · simp [hinp]
  obtain ⟨σ', hrun, ⟨hn, _, hs, hout⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := cond) (c := body) (Inv B σ₀)
      (fun τ => τ.inp.length) 9
      (fun τ hτ => ⟨decide (τ.vars "i" < τ.vars "n"), by
        obtain ⟨hn, hnB, _, _⟩ := hτ; simp [cond]; omega⟩) hstep hI
  have hexit : ¬ σ'.vars "i" < σ'.vars "n" := by simp [cond] at hfalse; omega
  have hnil : σ'.inp = [] := by
    rcases h : σ'.inp with _ | ⟨u, rest⟩
    · rfl
    · rw [h] at hn; simp at hn; omega
  refine ⟨σ', hrun.mono (by simp [cond]), ?_, hout⟩
  rw [hnil] at hs; simpa using hs

theorem solves : Solves layout com dom (fun x => [x.tail.sum])
    (fun x => x.sum + 2) (fun x => 13 * x.length + 11) where
  ok := com_ok
  inp := by
    rintro x ⟨xs, rfl⟩ v hv
    have : v ≤ (xs.length :: xs).sum := List.single_le_sum (by simp) v hv
    omega
  run := by
    rintro x ⟨xs, rfl⟩
    have hsum : (xs.length :: xs).sum = xs.length + xs.sum := by simp
    set B := (xs.length :: xs).sum + 2 with hB
    set σ₀ : Env := initEnv (fun _ => 0) (xs.length :: xs) with hσ₀
    obtain ⟨σ', hloop, hs, hout⟩ :=
      loop_run (B := B)
        (({ σ₀.setVar "n" xs.length with inp := xs }.setVar "i" 0).setVar "s" 0)
        ⟨by simp [hσ₀, initEnv], by simp [hB]; omega, by simp, by simp⟩
        (by simp [hB]; omega)
    refine ⟨fun _ => 0, _, (Run.seq (Run.read (by simp [hσ₀, initEnv]))
      (Run.seq (Run.assign (x := "i") (v := 0) (by simp [hB]))
        (Run.seq (Run.assign (x := "s") (v := 0) (by simp [hB]))
          (Run.seq hloop (Run.write (v := σ'.vars "s") (by
            simp [hs, hσ₀, initEnv, hB]; omega)))))).mono ?_, ?_⟩
    · simp; omega
    · show σ'.out ++ [σ'.vars "s"] = _
      rw [hout, hs]; simp [hσ₀, initEnv]

/-- **Sum, end to end.** The compiled machine program writes the sum of a
length-prefixed input within `130 * (|x| + 1)` steps, at every word
length at which the total of the input fits. -/
theorem prog_computesInTime {w : ℕ} (hw : ∀ x ∈ dom, x.sum + 8 ≤ 2 ^ w) :
    ComputesInTime w prog dom (fun x => [x.tail.sum]) (fun x => 130 * (x.length + 1)) := by
  refine computesInTime_of_solves solves
    (fun x hx => fitsWords_of_max_le (by omega)
      (by have := hw x hx; simp [Layout.span, layout]; omega))
    (fun x _ => by rw [const_eq]; omega)

end Sum

/-! ### Square: one product and one shift -/

namespace Square

/-- Read one number, write its square, write its double. -/
def com : Com :=
  .seq (.read "a")
    (.seq (.write (.mul (.var "a") (.var "a")))
      (.write (.shiftl (.var "a") (.lit 1))))

/-- One scalar, no arrays, two temporaries. -/
def layout : Layout := ⟨["a"], [], 2⟩

/-- The machine program. -/
def prog : Program := compileProgram layout com

/-- One number whose square and double fit under the bound. Here the
admissibility of the input is where the value bound is paid for, rather
than the word length alone: a product is the first construct of the
language whose result is not bounded by what was read. -/
def dom (b : ℕ) : Set (List ℕ) := {x : List ℕ | ∃ a, x = [a] ∧ a * a + a * 2 < b}

theorem com_ok : Com.Ok layout com := by
  simp [com, layout, Com.Ok, Expr.Ok]

theorem const_eq : layout.const = 10 := by
  simp [Layout.const]

theorem solves {b : ℕ} (hb : 1 < b) :
    Solves layout com (dom b) (fun x => [x.headI * x.headI, x.headI * 2])
      (fun _ => b) (fun _ => 9) where
  ok := com_ok
  inp := by
    rintro x ⟨a, rfl, hab⟩ v hv
    have : a ≤ a * 2 := by omega
    simp at hv
    omega
  run := by
    rintro x ⟨a, rfl, hab⟩
    have h2 : a ≤ a * 2 := by omega
    refine ⟨fun _ => 0, _, (Run.seq (Run.read (x := "a") (v := a) (rest := []) rfl)
      (Run.seq (Run.write (v := a * a) (by simp; omega))
        (Run.write (v := a * 2) (by simp; omega)))).mono (by simp), ?_⟩
    simp [initEnv]

/-- **Square, end to end.** The compiled machine program writes the
square and the double of its input within 90 steps, at every word length
at which the bound fits. -/
theorem prog_computesInTime {b w : ℕ} (hb : 1 < b) (hw : b + 5 ≤ 2 ^ w) :
    ComputesInTime w prog (dom b) (fun x => [x.headI * x.headI, x.headI * 2])
      (fun _ => 90) := by
  refine computesInTime_of_solves (solves hb)
    (fun x _ => fitsWords_of_max_le hb (by simp [Layout.span, layout]; omega))
    (fun x _ => by rw [const_eq])

end Square

end Lax759944Proofs.Legacy.Smoke
