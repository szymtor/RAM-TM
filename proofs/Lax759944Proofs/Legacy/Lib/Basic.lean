-- Adapted 2026-09-15 from word-ram-v4-33 at 0aa87e1f6e6add4abe4f4e0aff8fe4a28950b2ea.
-- Namespace relocated for use as a proof-only intermediate; semantics unchanged.
import Lax759944Proofs.Legacy.Tactic
import Lax759944Proofs.Legacy.Compile

/-!
The two pieces every module of the data-structure library needs, and
neither `Reasoning` nor `Spec` should carry.

`upd` is what a store does to a cell function: `arrOf n f` is the kit's
way of saying what is *at* each position of an array, a store changes
one position, so it changes `f` at one point. It is written as the very
`if` that `set_arrOf` produces, so that a store rewrites into it and no
`Function.update` cast has to be pushed around afterwards.

`runOut` is the driver the worked examples are checked with. Every `Lib`
module ships a small program built from its own operations, compiled and
run on the machine of the concept package, so that what its
specifications say is also *seen*; that is house discipline everywhere
else in this repo and there is no reason for the kit to be exempt.
-/

namespace Lax759944Proofs.Legacy.Reasoning.Lib

open Lax759944Proofs.Legacy.Imp

/-! ### Updating a cell function -/

/-- The cell function `f` with position `k` holding `v`. -/
def upd (f : ℕ → ℕ) (k v : ℕ) : ℕ → ℕ := fun i => if i = k then v else f i

theorem upd_apply (f : ℕ → ℕ) (k v i : ℕ) : upd f k v i = if i = k then v else f i := rfl

@[simp] theorem upd_self (f : ℕ → ℕ) (k v : ℕ) : upd f k v k = v := by simp [upd]

@[simp] theorem upd_of_ne {f : ℕ → ℕ} {k i : ℕ} (v : ℕ) (h : i ≠ k) : upd f k v i = f i := by
  simp [upd, h]

/-- A store into an `arrOf` array is an `upd` of its cell function. This
is `set_arrOf` with the anonymous function named, and it is the only
bridge an operation's specification needs between the list and the
function. -/
theorem set_arrOf_eq_upd {n : ℕ} (f : ℕ → ℕ) (k v : ℕ) :
    (arrOf n f).set k v = arrOf n (upd f k v) := set_arrOf f v

/-- `arrOf` at a position, in the `getElem` form `simp` normalizes a
`getD` into once it can see the length. `Reasoning`'s `getD_arrOf` is
stated on `getD`, so it stops firing exactly when `simp` has made most
progress; this is the companion that keeps going. -/
@[simp] theorem getElem_arrOf {n i : ℕ} (f : ℕ → ℕ) (h : i < (arrOf n f).length) :
    (arrOf n f)[i] = f i := by
  simp only [arrOf, List.getElem_map, List.getElem_range]

/-- An update stays within a pointwise bound. -/
theorem upd_le {f : ℕ → ℕ} {k v c i : ℕ} (hv : v ≤ c) (hf : f i ≤ c) : upd f k v i ≤ c := by
  rw [upd_apply]; split <;> assumption

/-! ### The worked-example driver -/

open Lax759944Proofs.Legacy.Ram in
/-- Run `p` at word length `w` from `s` until it halts, taking at most
`fuel` steps, and report the output tape together with the number of
steps taken. `none` means the fuel ran out. -/
def runOut (w : ℕ) : ℕ → Program → State → ℕ → Option (List ℕ × ℕ)
  | 0, _, _, _ => none
  | fuel + 1, p, s, k =>
      match step w p s with
      | none => some (s.out, k)
      | some s' => runOut w fuel p s' (k + 1)

/-! `runOut` is defined by `match`, so its equation lemmas and match
splitters are created on first use. These two statements ask for them
here, per the standing kit rule of `Frame.lean`: a downstream
`simp [runOut]` then finds them among its imports and creates nothing
named under `Lax759944Proofs.Legacy` in a consumer package. -/

@[simp] theorem runOut_zero (w : ℕ) (p : Lax759944Proofs.Legacy.Ram.Program) (s : Lax759944Proofs.Legacy.Ram.State) (k : ℕ) :
    runOut w 0 p s k = none := by simp [runOut]

theorem runOut_succ (w fuel : ℕ) (p : Lax759944Proofs.Legacy.Ram.Program) (s : Lax759944Proofs.Legacy.Ram.State) (k : ℕ) :
    runOut w (fuel + 1) p s k =
      match Lax759944Proofs.Legacy.Ram.step w p s with
      | none => some (s.out, k)
      | some s' => runOut w fuel p s' (k + 1) := by
  simp [runOut]

end Lax759944Proofs.Legacy.Reasoning.Lib
