-- Adapted 2026-09-15 from word-ram-v4-33 at 0aa87e1f6e6add4abe4f4e0aff8fe4a28950b2ea.
-- Namespace relocated for use as a proof-only intermediate; semantics unchanged.
import Lax759944Proofs.Legacy.RamComputes
import Lax759944Proofs.Legacy.Reasoning

/-!
The boundary: from an IMP+ run to a statement about the machine.

This is the one theorem an algorithm proof ends with, and the only
place where the word length appears. Everything below it — the value
bound, the compiler, the layout invariant, the machine — has been
discharged once and for all; what a user brings is a single predicate
about their own program.

`Solves L c D f B K` is that predicate: the command `c` compiles under
the layout `L`, every entry of an admissible input is below the bound,
and on every admissible input the command runs to an environment whose
output tape is the value of `f`, at a cost of at most `K`, every value
it produces staying below the bound. Nothing in it mentions `w`, the
machine, or the compiler.

The bound `B` and the cost `K` are functions of the input, and that is
what makes the word-length hypothesis of the conclusion sayable in the
style of the concept: an algorithm's values are bounded in terms of what
it read — `c * (n + 1)` for a graph on `n` vertices — so the hypothesis
that comes out is `∀ x ∈ D, L.span (B x) ≤ 2 ^ w`, an explicit
inequality against `2 ^ w` with the constant written in. A program whose
values are bounded outright uses a constant function and loses nothing.

The cost is separated from the conclusion's time bound by one
inequality, `L.const * K x ≤ T x`, so that a statement may be made at a
round constant instead of at whatever the cost model happens to add up
to; `Solves.computesInTime` is the version that takes the product as it
comes.
-/

namespace Lax759944Proofs.Legacy.Transfer

open Lax759944Proofs.Legacy.Ram Lax759944Proofs.Legacy.RamComputes Lax759944Proofs.Legacy.Imp Lax759944Proofs.Legacy.Compile
open Lax759944Proofs.Legacy.Simulation Lax759944Proofs.Legacy.Reasoning

/-- The obligation the pipeline asks of one program: `c` compiles under
`L`, admissible inputs have entries below `B`, and on an admissible
input `c` runs to output `f x` at cost at most `K x` with every value
below `B x`. This is stated entirely in IMP+; the word length, the
machine and the compiler do not occur. -/
structure Solves (L : Layout) (c : Com) (D : Set (List ℕ)) (f : List ℕ → List ℕ)
    (B K : List ℕ → ℕ) : Prop where
  /-- Every name the command mentions is in the layout. -/
  ok : Com.Ok L c
  /-- Admissible inputs fit under the bound. -/
  inp : ∀ x ∈ D, ∀ v ∈ x, v < B x
  /-- On an admissible input the command computes `f`, within the cost
  and under the bound. The declared array lengths are chosen per input:
  an algorithm sizes its arrays by what it reads, and the compiled
  program does not represent them at all. -/
  run : ∀ x ∈ D, ∃ (ext : String → ℕ) (σ' : Env),
    Run (B x) c (initEnv ext x) σ' (K x) ∧ σ'.out = f x

/-- **The transfer theorem.** A program that solves a problem in IMP+
within cost `K` and values below `B` compiles to a machine program that
computes the same function within `T`, at every word length at which the
layout and the bound fit — provided `L.const` machine steps per unit of
IMP+ cost stay within `T`. -/
theorem computesInTime_of_solves {L : Layout} {c : Com} {D : Set (List ℕ)}
    {f : List ℕ → List ℕ} {B K T : List ℕ → ℕ} {w : ℕ}
    (h : Solves L c D f B K) (hfit : ∀ x ∈ D, L.FitsWords (B x) w)
    (hT : ∀ x ∈ D, L.const * K x ≤ T x) :
    ComputesInTime w (compileProgram L c) D f T := by
  intro x hx
  obtain ⟨ext, σ', ⟨k, hk, hbs⟩, hout⟩ := h.run x hx
  obtain ⟨t, ht, hrun⟩ := compileProgram_runsTo (hfit x hx) h.ok (h.inp x hx) hbs
  exact ⟨t, ht.trans ((Nat.mul_le_mul_left _ hk).trans (hT x hx)), hout ▸ hrun⟩

/-- The transfer theorem with the time bound taken as it comes: the
IMP+ cost times the constant of the layout. -/
theorem Solves.computesInTime {L : Layout} {c : Com} {D : Set (List ℕ)}
    {f : List ℕ → List ℕ} {B K : List ℕ → ℕ} {w : ℕ}
    (h : Solves L c D f B K) (hfit : ∀ x ∈ D, L.FitsWords (B x) w) :
    ComputesInTime w (compileProgram L c) D f (fun x => L.const * K x) :=
  computesInTime_of_solves h hfit fun _ _ => le_rfl

/-- The word-length hypothesis as one inequality against `2 ^ w`. The
bound and the span of the layout at that bound both have to fit; a
layout with an array spans more than its bound and a layout without one
need not, so what has to fit is their maximum, and stating it that way
costs a downstream statement nothing. -/
theorem fitsWords_of_max_le {L : Layout} {B w : ℕ} (h1 : 1 < B)
    (h : max B (L.span B) ≤ 2 ^ w) : L.FitsWords B w :=
  ⟨h1, le_trans (le_max_left _ _) h, le_trans (le_max_right _ _) h⟩

end Lax759944Proofs.Legacy.Transfer
