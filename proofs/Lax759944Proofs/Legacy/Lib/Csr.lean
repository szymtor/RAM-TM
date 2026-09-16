-- Adapted 2026-09-15 from word-ram-v4-33 at 0aa87e1f6e6add4abe4f4e0aff8fe4a28950b2ea.
-- Namespace relocated for use as a proof-only intermediate; semantics unchanged.
import Lax759944Proofs.Legacy.Lib.Basic

/-!
A block structure in compressed-row form: an array of offsets and an
array of targets. Row `v` is the stretch of the target array between
`off v` and `off (v + 1)`.

This is the shape every adjacency list in the repo is stored in, and
its two scans are the most-copied loops here. The row scan — `j` from
`off v` to `off (v + 1)`, one slot per turn — is written from scratch
at `Phases.lean:462` (`rowLoop_run`), `Phases3.lean:1320`
(`rowScan3_run`) and `CCSearch.lean:301` (Lax11's `scan_run`, the body
of `expandBody`). The owner-advancing scan — all slots once, with a
second pointer walking the row that owns the current slot — is written
from scratch at `Phases.lean:1004` (`descendScan_run`) and
`VCScan.lean:59` (Lax11's `scan_run`), and the two do not even have the
same program shape: Lax11 tests `j < off[u+1]` in an `ite` and does one
thing per turn, Lax15 puts a whole inner `while off[u+1] < j+1` loop in
front of the slot's work. Both pay with the same two-term potential,
"so much per slot left, so much per row left", and both spend twenty
lines getting from that potential to `Run.while_potential`'s
obligation.

### The relation, and what is deliberately not in it

`Csr o t nv ns V off tgt σ` says: the array named `o` is the length-
`nv + 1` array of `off`, the array named `t` is the length-`ns` array
of `tgt`, the offsets are nondecreasing, `off nv = ns`, and every
target is smaller than `V`.

* **No graph, no `Fin n`.** The plan's placement decision: the kit does
  not acquire a graph dependency, so `Lib/Csr` is stated over two
  arrays of numbers and nothing else. `EncodesGraph`, `offset`,
  `target`, `adjn` stay in Lax11, and a consumer bridges by rewriting
  its `offset g` into this module's `off` — which is what `hO : ∀ i ≤
  n, O i = offset g i` already does at every site.
* **Monotonicity is stated stepwise**, `off i ≤ off (i + 1)`, because
  that is the form `offset_mono` is proved in downstream and the form
  `arrOf`-shaped invariants keep. `Csr.mono` derives the general one.
* **`off nv = ns` is the extent**, and it is what makes the owner
  pointer meaningful: a slot below `ns` is in some row, so the owner
  never runs off the end (`Csr.owner_lt`). Both owner-advancing scans
  hand-derive exactly this, by contradiction, from `offset_last`.
* **The target bound `V` rides in the relation**, as in `Stack`,
  `Queue` and `Ind`: a slot read owes `tgt p < B` and the relation is
  opaque to the walk's discharger, so the caller supplies `V ≤ B` once.
  Both consumers instantiate `V` with `n`.
* **The offsets need no separate bound**: `off i ≤ ns` follows from
  monotonicity and the extent, so `ns < B` is the only word obligation
  the offsets carry. Lax11's `hOB` and Lax15's `hOB` are that lemma,
  hand-written twice.
* **No scalar is named in the relation.** It is a statement about two
  arrays, so `Csr.setVar_iff` holds unconditionally — unlike `Stack`'s
  and `Queue`'s, which have to exclude their pointers.

### The two scans, and why they are one `Com`

`scan j e c` is `while j < e do c`. The row scan and the owner-
advancing scan are *the same command*: `rowLoop` is `while j < jend`
and `descendScan`'s loop is `while j < m2`, and the only difference is
what bounds the pointer and what pays for the turns. So the module
exports one command and two specifications over it, rather than two
definitions with the same body.

`rowScan_spec` is the flat one: the body moves `j` up by one at a cost
of at most `Kb`, and the loop costs `(Kb + 4)` per slot of the row. It
is `Spec.forRange` with the bounds taken from a row rather than from a
counter, and its step obligation is in `Run.while_potential`'s
existential-cost form rather than `forRange`'s `Spec` form — a body
that is itself a loop, or an `ite` whose branches cost differently,
cannot be handed over as a constant-cost `Spec`, and `Queue.drain_spec`
wants this loop as one of *its* steps, where the cost has to be free to
be the row's length.

`ownerScan_spec` is the amortized one. Its potential is
`(Kslot + 4) · (ns − j) + (Kown + 4) · (nv − u)`, and — this is the
point of the export — the caller never sees it. A turn declares how far
it moved each pointer and what it cost, in the form
`K' ≤ Kslot · Δj + Kown · Δu`, and the combinator does the arithmetic.
That covers both program shapes: Lax11's turn moves one pointer or the
other, Lax15's moves the owner several times and then the slot once,
and both are instances of "moved `Δj` and `Δu`, paid `Kslot` and `Kown`
apiece". The one thing a turn owes beyond its cost is *progress*, since
a turn that moved nothing would have to be paid for out of nothing.

### Deviations from the plan's P4 text, and what they cost

The plan's table names the operations "row scan, full owner-advancing
scan". Two straight-line operations ship with them, because every one
of the six sites opens with them: `loadRow`, which reads a row's two
bounds out of the offsets array, and `slot`, which reads the target at
the pointer. Both remove a read whose obligations a caller would
otherwise pre-load by hand.

**Neither scan combinator mentions the relation.** This is deliberate
and was forced by the acceptance test: `rowLoop_run` has no offsets
array in its hypotheses at all — it is handed `jend` already loaded —
so a row-scan combinator that demanded a `Csr` could not be
instantiated there without changing the statement. What the relation
supplies is the *inputs* to the combinators (`Csr.row_le`,
`Csr.off_lt`, `Csr.owner_lt`), stated separately, so that a caller who
has a relation pays one lemma and a caller who has only the numbers
pays nothing.

**`loadRow_spec` is written out rather than walked**, and it is the one
place in the kit where the tactic does not apply. Its second read reads
`v` *after* `j` has been assigned, so the index the walk states its
obligations at is `(σ.setVar j _).vars v`; collapsing that `if` needs
`v ≠ j`, and the discharger is `omega`-then-`simp` over the goal alone
and does not look at the local context. Shape note 5's pre-loading
cannot reach it, because a precondition is a statement about the
*initial* environment. The same shape is why the worked example's turn
hands `run_vcg` its slot step as one specification instead of two
commands: the moment a read of `j` follows a write of `w`, the block
has to enter as a unit. Anything reading a scalar that an earlier line
of the same block wrote is in this position, and the fix is always the
same — export the pair as one `Spec`.

`Csr.owner_unique` is `Lax15Proofs.Phases.owner_unique` with the graph
taken out; that copy is left in place, since removing it is a retrofit
and this phase is not one.
-/

namespace Lax759944Proofs.Legacy.Reasoning.Lib

open Lax759944Proofs.Legacy.Imp

variable {B nv ns V i k p u : ℕ} {o t v j b : String} {off tgt : ℕ → ℕ} {σ : Env}

/-! ### The relation -/

/-- `Csr o t nv ns V off tgt σ`: in `σ`, the array named `o` is the
length-`nv + 1` array of offsets `off`, the array named `t` is the
length-`ns` array of targets `tgt`, the offsets are nondecreasing, the
last one is the number of slots, and every target is smaller than
`V`. Row `v` is the stretch `off v … off (v + 1) − 1` of the target
array. -/
def Csr (o t : String) (nv ns V : ℕ) (off tgt : ℕ → ℕ) (σ : Env) : Prop :=
  σ.arrs o = arrOf (nv + 1) off ∧ σ.arrs t = arrOf ns tgt ∧
    (∀ i, i < nv → off i ≤ off (i + 1)) ∧ off nv = ns ∧ ∀ p, p < ns → tgt p < V

/-- The offsets array. -/
theorem Csr.offArr (hc : Csr o t nv ns V off tgt σ) : σ.arrs o = arrOf (nv + 1) off := hc.1

/-- The targets array. -/
theorem Csr.tgtArr (hc : Csr o t nv ns V off tgt σ) : σ.arrs t = arrOf ns tgt := hc.2.1

/-- The offsets do not decrease, one step at a time. -/
theorem Csr.off_le_succ (hc : Csr o t nv ns V off tgt σ) (hi : i < nv) : off i ≤ off (i + 1) :=
  hc.2.2.1 i hi

/-- The last offset is the number of slots. -/
theorem Csr.last (hc : Csr o t nv ns V off tgt σ) : off nv = ns := hc.2.2.2.1

/-- Every target is below the bound. -/
theorem Csr.target (hc : Csr o t nv ns V off tgt σ) (hp : p < ns) : tgt p < V :=
  hc.2.2.2.2 p hp

/-- **The offsets do not decrease.** The stepwise form of the relation,
turned into the one the scans use. -/
theorem Csr.mono (hc : Csr o t nv ns V off tgt σ) (hik : i ≤ k) (hk : k ≤ nv) :
    off i ≤ off k := by
  induction k with
  | zero => have : i = 0 := by omega
            subst this; exact le_rfl
  | succ k ih =>
      by_cases hik' : i ≤ k
      · exact le_trans (ih hik' (by omega)) (hc.off_le_succ (by omega))
      · have : i = k + 1 := by omega
        subst this; exact le_rfl

/-- **Every row ends inside the target array**, which is the bound the
row scan runs to. -/
theorem Csr.le_ns (hc : Csr o t nv ns V off tgt σ) (hi : i ≤ nv) : off i ≤ ns :=
  hc.last ▸ hc.mono hi le_rfl

/-- **A row ends inside the target array**, which is the bound its scan
runs to and the one hypothesis `rowScan_spec` asks of a caller who has a
relation. -/
theorem Csr.row_le (hc : Csr o t nv ns V off tgt σ) (hv : i < nv) : off (i + 1) ≤ ns :=
  hc.le_ns (by omega)

/-- The lengths, which is what a read's range condition asks for. -/
theorem Csr.length_off (hc : Csr o t nv ns V off tgt σ) : (σ.arrs o).length = nv + 1 := by
  rw [hc.offArr, length_arrOf]

theorem Csr.length_tgt (hc : Csr o t nv ns V off tgt σ) : (σ.arrs t).length = ns := by
  rw [hc.tgtArr, length_arrOf]

/-- Reading an offset. -/
theorem Csr.getD_off (hc : Csr o t nv ns V off tgt σ) (hi : i ≤ nv) :
    (σ.arrs o).getD i 0 = off i := by
  rw [hc.offArr, getD_arrOf off (by omega)]

/-- Reading a target. -/
theorem Csr.getD_tgt (hc : Csr o t nv ns V off tgt σ) (hp : p < ns) :
    (σ.arrs t).getD p 0 = tgt p := by
  rw [hc.tgtArr, getD_arrOf tgt hp]

/-- Reading an offset, in the `getElem?` form the walk's discharger
normalizes a `getD` into. -/
theorem Csr.off_getD (hc : Csr o t nv ns V off tgt σ) (hi : i ≤ nv) :
    (σ.arrs o)[i]?.getD 0 = off i := by
  rw [← List.getD_eq_getElem?_getD, hc.getD_off hi]

/-- And a target in the same form. -/
theorem Csr.tgt_getD (hc : Csr o t nv ns V off tgt σ) (hp : p < ns) :
    (σ.arrs t)[p]?.getD 0 = tgt p := by
  rw [← List.getD_eq_getElem?_getD, hc.getD_tgt hp]

/-- **Every target is a word as soon as `V` is**: the reason the bound
belongs in the relation rather than in every precondition, exactly as
`Ind.lt`, `Stack.lt` and `Queue.lt`. -/
theorem Csr.lt (hc : Csr o t nv ns V off tgt σ) (hVB : V ≤ B) (hp : p < ns) : tgt p < B :=
  lt_of_lt_of_le (hc.target hp) hVB

/-- **And every offset is a word as soon as the slot count is**, which
is why the offsets carry no bound of their own. -/
theorem Csr.off_lt (hc : Csr o t nv ns V off tgt σ) (hnsB : ns < B) (hi : i ≤ nv) :
    off i < B :=
  lt_of_le_of_lt (hc.le_ns hi) hnsB

/-- **A slot has an owner.** If the pointer is a slot and the owner is
at most the last row, then the owner is a row: the extent is what rules
out an owner that has walked off the end. Both owner-advancing scans
derive this by contradiction from `offset_last`; here it is once. -/
theorem Csr.owner_lt (hc : Csr o t nv ns V off tgt σ) (hu : u ≤ nv) (hlo : off u ≤ p)
    (hp : p < ns) : u < nv := by
  rcases Nat.lt_or_ge u nv with h | h
  · exact h
  · exfalso
    have hun : u = nv := by omega
    rw [hun, hc.last] at hlo
    omega

/-- **A slot has only one owner.** Two rows containing the same slot are
the same row, since the offsets do not decrease. This is Lax15's
`owner_unique`, which is about offsets and not about graphs. -/
theorem Csr.owner_unique (hc : Csr o t nv ns V off tgt σ) {u u' : ℕ}
    (hu : u ≤ nv) (hu' : u' ≤ nv) (h1 : off u ≤ p) (h2 : p < off (u + 1))
    (h3 : off u' ≤ p) (h4 : p < off (u' + 1)) : u = u' := by
  rcases lt_trichotomy u u' with h | h | h
  · have := hc.mono (show u + 1 ≤ u' by omega) hu'
    omega
  · exact h
  · have := hc.mono (show u' + 1 ≤ u by omega) hu
    omega

/-- **A scalar assignment leaves the structure alone**, with no side
condition: the relation names two arrays and no scalar at all. -/
@[simp] theorem Csr.setVar_iff (o t : String) (nv ns V : ℕ) (off tgt : ℕ → ℕ) (σ : Env)
    (y : String) (x : ℕ) :
    Csr o t nv ns V off tgt (σ.setVar y x) ↔ Csr o t nv ns V off tgt σ := by simp [Csr]

theorem Csr.setVar (hc : Csr o t nv ns V off tgt σ) (y : String) (x : ℕ) :
    Csr o t nv ns V off tgt (σ.setVar y x) :=
  (Csr.setVar_iff ..).2 hc

/-- **The transport lemma.** The relation is a statement about two
arrays, so any environment agreeing on those two satisfies it. This is
what carries the structure across a phase that writes marks, labels or
a queue — which is every phase at every one of the six sites. -/
theorem Csr.of_eq (hc : Csr o t nv ns V off tgt σ) {σ' : Env}
    (ho : σ'.arrs o = σ.arrs o) (ht : σ'.arrs t = σ.arrs t) :
    Csr o t nv ns V off tgt σ' :=
  ⟨by rw [ho, hc.offArr], by rw [ht, hc.tgtArr], hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2⟩

/-- A store into another array leaves the structure alone. -/
theorem Csr.setArr_of_ne (hc : Csr o t nv ns V off tgt σ) (hbo : b ≠ o) (hbt : b ≠ t)
    (k x : ℕ) : Csr o t nv ns V off tgt (σ.setArr b k x) :=
  hc.of_eq (by rw [arrs_setArr, if_neg (Ne.symm hbo)]) (by rw [arrs_setArr, if_neg (Ne.symm hbt)])

/-! Everything from here on is this module's own — its row view, its
operations, their specifications and its worked example — so it lives in
the module's namespace. -/

namespace Csr

/-! ### The row view

Derived, on top of the relation and never inside it: the length of a
row, and its slots as a list. -/

/-- The number of slots in row `i`. -/
def rowLen (off : ℕ → ℕ) (i : ℕ) : ℕ := off (i + 1) - off i

/-- The targets of row `i`, in slot order. -/
def row (off tgt : ℕ → ℕ) (i : ℕ) : List ℕ :=
  arrOf (rowLen off i) (fun k => tgt (off i + k))

@[simp] theorem length_row (off tgt : ℕ → ℕ) (i : ℕ) :
    (row off tgt i).length = rowLen off i := by simp [row]

/-- An empty row is an empty list. -/
theorem row_eq_nil (off tgt : ℕ → ℕ) (i : ℕ) (h : off (i + 1) ≤ off i) :
    row off tgt i = [] := by
  simp [row, rowLen, show off (i + 1) - off i = 0 by omega, arrOf]

/-- The rows tile the target array: the slots of the whole structure are
the slots of row `0`, then of row `1`, and so on. This is the sum every
amortized scan pays with, stated once. -/
theorem sum_rowLen (hc : Csr o t nv ns V off tgt σ) (k : ℕ) (hk : k ≤ nv) :
    ∑ i ∈ Finset.range k, rowLen off i = off k - off 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k ≤ nv := by omega
      rw [Finset.sum_range_succ, ih hk']
      have h₁ : off 0 ≤ off k := hc.mono (by omega) hk'
      have h₂ : off k ≤ off (k + 1) := hc.off_le_succ (by omega)
      simp only [rowLen]
      omega

/-! ### The operations

Two straight-line commands and one loop. Every name is a parameter —
the two arrays, the row number, the two pointers and the scalar a
target lands in — so that one specification serves `"off"`/`"tgt"` at
all six sites. -/

/-- Load the bounds of row `v` into `j` and `jend`: the four lines every
row scan opens with. -/
def loadRow (o v j jend : String) : Com :=
  .seq (.assign j (.get o (.var v))) (.assign jend (.get o (.add (.var v) (.lit 1))))

/-- Read the target at the slot pointer `j` into `w`. -/
def slot (t j w : String) : Com := .assign w (.get t (.var j))

/-- **The slot loop**: run `c` while the slot pointer `j` is below the
bound held in `e`. The row scan and the owner-advancing scan are this
one command — see this file's header — and differ only in what bounds
it and in what pays for its turns. -/
def scan (j e : String) (c : Com) : Com := .while (.lt (.var j) (.var e)) c

/-! The frame conditions of the two straight-line operations, as `simp`
lemmas: a call site's array names are bound variables, so `Spec.frame`'s
obligations are discharged there by `simp` and not by `decide`. The
loop's are the body's, so they are stated in terms of it. -/

@[simp] theorem wvars_loadRow (o v j jend : String) :
    (loadRow o v j jend).wvars = [j, jend] := by simp [loadRow, Com.wvars]

@[simp] theorem warrs_loadRow (o v j jend : String) : (loadRow o v j jend).warrs = [] := by
  simp [loadRow, Com.warrs]

@[simp] theorem not_reads_loadRow (o v j jend : String) : ¬ (loadRow o v j jend).reads := by
  simp [loadRow, Com.reads]

@[simp] theorem noWrite_loadRow (o v j jend : String) : (loadRow o v j jend).NoWrite := by
  simp [loadRow, Com.NoWrite]

@[simp] theorem wvars_slot (t j w : String) : (slot t j w).wvars = [w] := by
  simp [slot, Com.wvars]

@[simp] theorem warrs_slot (t j w : String) : (slot t j w).warrs = [] := by
  simp [slot, Com.warrs]

@[simp] theorem not_reads_slot (t j w : String) : ¬ (slot t j w).reads := by
  simp [slot, Com.reads]

@[simp] theorem noWrite_slot (t j w : String) : (slot t j w).NoWrite := by
  simp [slot, Com.NoWrite]

@[simp] theorem wvars_scan (j e : String) (c : Com) : (scan j e c).wvars = c.wvars := by
  simp [scan, Com.wvars]

@[simp] theorem warrs_scan (j e : String) (c : Com) : (scan j e c).warrs = c.warrs := by
  simp [scan, Com.warrs]

@[simp] theorem reads_scan_iff (j e : String) (c : Com) : (scan j e c).reads ↔ c.reads := by
  simp [scan, Com.reads]

@[simp] theorem noWrite_scan_iff (j e : String) (c : Com) :
    (scan j e c).NoWrite ↔ c.NoWrite := by simp [scan, Com.NoWrite]

/-! ### The specifications of the two reads -/

/-- What every operation needs: the relation, the target bound inside
the word bound, and a slot count that is a word — which covers every
offset, by `Csr.off_lt`. -/
abbrev Pre (o t : String) (nv ns V B : ℕ) (off tgt : ℕ → ℕ) (σ : Env) : Prop :=
  Csr o t nv ns V off tgt σ ∧ V ≤ B ∧ ns < B

/-- What `loadRow` needs on top of that: a row number that is a row, and
its successor a word — the arithmetic index of the second read. -/
abbrev RowPre (o t v : String) (nv ns V B : ℕ) (off tgt : ℕ → ℕ) (σ : Env) : Prop :=
  Pre o t nv ns V B off tgt σ ∧ σ.vars v < nv ∧ σ.vars v + 1 < B

/-- What `slot` needs on top of that: a pointer that is a slot. -/
abbrev SlotPre (o t j : String) (nv ns V B : ℕ) (off tgt : ℕ → ℕ) (σ : Env) : Prop :=
  Pre o t nv ns V B off tgt σ ∧ σ.vars j < ns

/-- What `loadRow` leaves: the two bounds of the row, and — since this
is a straight-line operation stepped over in the middle of a caller's
block — the state itself. A relation says what an operation *did*, which
is what a data structure's caller wants; a caller who has to go on
walking its own block wants the state back, because everything it reads
next is a projection of it and a frame condition per projection is what
it costs otherwise. `Spec.assign` names the state for the same reason. -/
abbrev LoadRowPost (o t v j jend : String) (nv ns V : ℕ) (off tgt : ℕ → ℕ)
    (σ σ' : Env) : Prop :=
  Csr o t nv ns V off tgt σ' ∧ σ'.vars j = off (σ.vars v) ∧
    σ'.vars jend = off (σ.vars v + 1) ∧
    σ' = (σ.setVar j (off (σ.vars v))).setVar jend (off (σ.vars v + 1))

/-- What `slot` leaves: the target at the pointer. -/
abbrev SlotPost (o t j w : String) (nv ns V : ℕ) (off tgt : ℕ → ℕ) (σ σ' : Env) : Prop :=
  Csr o t nv ns V off tgt σ' ∧ σ'.vars w = tgt (σ.vars j)

/-- **The obligations of the two offset reads**, in the forms the walk
states them: each index in range, and each cell a word both as a
`List.getD` and in the `getElem?` form the discharger's `simp`
normalizes into, together with the scalar bounds — including
`σ.vars v + 1 < B`, which is the arithmetic index shape note 5's
refinement was written for. `Queue.FrontRead` is the same package for a
read at a pointer. -/
abbrev RowRead (o t v : String) (nv ns V B : ℕ) (off tgt : ℕ → ℕ) (σ : Env) : Prop :=
  RowPre o t v nv ns V B off tgt σ ∧ σ.vars v < (σ.arrs o).length ∧
    σ.vars v + 1 < (σ.arrs o).length ∧
    (σ.arrs o).getD (σ.vars v) 0 < B ∧ (σ.arrs o)[σ.vars v]?.getD 0 < B ∧
    (σ.arrs o).getD (σ.vars v + 1) 0 < B ∧ (σ.arrs o)[σ.vars v + 1]?.getD 0 < B ∧
    σ.vars v < B

/-- All of them come off the relation. -/
theorem rowRead_of_pre (hσ : RowPre o t v nv ns V B off tgt σ) :
    RowRead o t v nv ns V B off tgt σ := by
  have hc := hσ.1.1
  have hnsB := hσ.1.2.2
  have h₁ : (σ.arrs o).getD (σ.vars v) 0 < B := by
    rw [hc.getD_off (by omega)]; exact hc.off_lt hnsB (by omega)
  have h₂ : (σ.arrs o).getD (σ.vars v + 1) 0 < B := by
    rw [hc.getD_off (by omega)]; exact hc.off_lt hnsB hσ.2.1
  exact ⟨hσ, by rw [hc.length_off]; omega, by rw [hc.length_off]; omega, h₁,
    by rwa [← List.getD_eq_getElem?_getD], h₂, by rwa [← List.getD_eq_getElem?_getD],
    by omega⟩

/-- The obligations of a target read, in the same two forms. -/
abbrev SlotRead (o t j : String) (nv ns V B : ℕ) (off tgt : ℕ → ℕ) (σ : Env) : Prop :=
  SlotPre o t j nv ns V B off tgt σ ∧ σ.vars j < (σ.arrs t).length ∧
    (σ.arrs t).getD (σ.vars j) 0 < B ∧ (σ.arrs t)[σ.vars j]?.getD 0 < B ∧ σ.vars j < B

theorem slotRead_of_pre (hσ : SlotPre o t j nv ns V B off tgt σ) :
    SlotRead o t j nv ns V B off tgt σ := by
  have hc := hσ.1.1
  have hval : (σ.arrs t).getD (σ.vars j) 0 < B := by
    rw [hc.getD_tgt hσ.2]; exact hc.lt hσ.1.2.1 hσ.2
  exact ⟨hσ, by rw [hc.length_tgt]; exact hσ.2, hval,
    by rwa [← List.getD_eq_getElem?_getD], by have := hσ.1.2.2; omega⟩

/-- **Loading a row's bounds.** Written out rather than walked, and
this is the one place in the kit where that is forced: the second read
is a read of `v` *after* `j` has been assigned, so the index the walk
states its obligations at is `(σ.setVar j _).vars v`, and collapsing
that `if` needs `v ≠ j`, which the discharger does not look at. Every
consumer wants exactly this pair of reads, so the disequality is the
specification's hypothesis and the two `Run`s are built here once. -/
theorem loadRow_spec (B nv ns V : ℕ) (o t v j jend : String) (off tgt : ℕ → ℕ)
    (hvj : v ≠ j) (hjje : j ≠ jend) :
    Spec B (RowPre o t v nv ns V B off tgt) (loadRow o v j jend)
      (LoadRowPost o t v j jend nv ns V off tgt) 8 := by
  refine Spec.of_exists (fun σ hσ => ?_)
  have hc := hσ.1.1
  have hnsB := hσ.1.2.2
  have hv := hσ.2.1
  have e₁ : (Expr.get o (.var v)).evalB B σ = some (off (σ.vars v)) :=
    evalB_get (evalB_var (by omega)) (by rw [hc.offArr, getElem?_arrOf off (by omega)])
      (hc.off_lt hnsB (by omega))
  have hvars : (σ.setVar j (off (σ.vars v))).vars v = σ.vars v := by simp [hvj]
  have ev : (Expr.var v).evalB B (σ.setVar j (off (σ.vars v))) = some (σ.vars v) := by
    have h := evalB_var (B := B) (x := v) (σ := σ.setVar j (off (σ.vars v)))
      (by rw [hvars]; omega)
    rwa [hvars] at h
  have e₂ : (Expr.get o (.add (.var v) (.lit 1))).evalB B (σ.setVar j (off (σ.vars v)))
      = some (off (σ.vars v + 1)) := by
    refine evalB_get (k := σ.vars v + 1) ?_ ?_ (hc.off_lt hnsB hv)
    · simp only [evalB_bin_iff]
      exact ⟨σ.vars v, 1, ev, by simp; omega, by simp [Bop.apply], by omega⟩
    · rw [arrs_setVar, hc.offArr, getElem?_arrOf off (by omega)]
  refine ⟨_, 8, ((Run.assign e₁).seq (Run.assign e₂)).mono (by simp), le_rfl, ?_, ?_, ?_, rfl⟩
  · simpa using hc
  · simp [hjje]
  · simp

/-- **Reading the target at the pointer.** -/
theorem slot_spec (B nv ns V : ℕ) (o t j w : String) (off tgt : ℕ → ℕ) :
    Spec B (SlotPre o t j nv ns V B off tgt) (slot t j w)
      (SlotPost o t j w nv ns V off tgt) 3 := by
  refine Spec.pre (P := SlotRead o t j nv ns V B off tgt) ?_ (fun _ hσ => slotRead_of_pre hσ)
  run_vcg
  have hc := ‹Csr o t nv ns V off tgt σ›
  exact ⟨by simpa using hc, by simp [hc.tgt_getD ‹σ.vars j < ns›]⟩

/-! ### The row scan

The loop is the caller's, body and all, exactly as `Queue.drain`'s is:
what a slot *does* is the algorithm, and the six sites do six different
things with it. What the combinator supplies is the loop condition —
whose definedness is the row bound's, not the caller's — the exit fact
`j = hi`, and the cost, `Kb + 4` per slot of the row.

The step obligation is `Run.while_potential`'s existential-cost form
rather than a body `Spec`: the body of `rowScan3` is an `ite` whose
branches cost differently, and `Queue.drain_spec` wants this whole loop
as one of *its* steps, where the cost has to be free to be the row's
length. -/

/-- **Scanning a row.** From any state satisfying an invariant that
pins the bound in `jend` and keeps the pointer inside the row, `while
j < jend do c` runs to the end of the row at a cost of `Kb + 4` per
slot plus one last test. -/
theorem rowScan_spec (B K hi Kb : ℕ) (j jend : String) (c : Com)
    {P : Env → Prop} (I : Env → Prop)
    (hhi : hi < B)
    (hIb : ∀ σ, I σ → σ.vars jend = hi ∧ σ.vars j ≤ hi)
    (hstep : ∀ σ, I σ → σ.vars j < hi →
      ∃ σ' K', Run B c σ σ' K' ∧ I σ' ∧ σ'.vars j = σ.vars j + 1 ∧ K' ≤ Kb)
    (hPI : ∀ σ, P σ → I σ) (hK : ∀ σ, P σ → (Kb + 4) * (hi - σ.vars j) + 4 ≤ K) :
    Spec B P (scan j jend c) (fun _ σ' => I σ' ∧ σ'.vars j = hi) K := by
  refine Spec.forRange j jend (c := c) I hi Kb K
    (fun σ hI => by have := hIb σ hI; omega) (fun σ hI => by have := (hIb σ hI).1; omega)
    (fun σ hI => (hIb σ hI).1) (fun σ hI => (hIb σ hI).2) ?_ hPI hK
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨σ', K', hrun, hI', hj', hK'⟩ := hstep σ hσ.1 hσ.2
  exact ⟨σ', K', hrun, hK', hI', hj'⟩

/-! ### The owner-advancing scan

One pass over the whole target array, with a second pointer walking the
row that owns the current slot. The potential is two terms, one per
pointer, and the combinator is what keeps it out of the caller's proof:
a turn says how far it moved each pointer and what it cost, and the
arithmetic that turns that into `Run.while_potential`'s obligation
happens here. Progress — one of the two pointers moved — is what a turn
owes beyond its cost. -/

/-- The arithmetic of the amortization, on its own: a turn that moves
the two pointers by `da` and `db` and costs at most `Kslot · da +
Kown · db` is paid for by charging `Kslot + 4` per slot and `Kown + 4`
per row, as long as it moved something. -/
theorem pay_le (Kslot Kown da db K' : ℕ) (hmove : 1 ≤ da + db)
    (hK : K' ≤ Kslot * da + Kown * db) :
    4 + K' ≤ (Kslot + 4) * da + (Kown + 4) * db := by
  have e₁ : (Kslot + 4) * da = Kslot * da + 4 * da := by ring
  have e₂ : (Kown + 4) * db = Kown * db + 4 * db := by ring
  rw [e₁, e₂]
  generalize Kslot * da = A at hK ⊢
  generalize Kown * db = C at hK ⊢
  omega

/-- **The owner-advancing scan.** From any state satisfying an
invariant that pins the slot count in `m` and keeps both pointers in
range, `while j < m do c` runs to the end of the target array. Each
turn declares how far it moved the slot pointer and the owner pointer
and what it cost; the potential — `Kslot + 4` per slot left and
`Kown + 4` per row left — is the combinator's, and the caller never
writes it down.

The body is entirely open, which is what lets the one combinator serve
both program shapes in the repo: a turn that either passes a slot or
advances the owner (Lax11's `scanBody`), and a turn that advances the
owner as often as it must and then passes a slot (Lax15's
`ownerAdvance; slotStep`). -/
theorem ownerScan_spec (B K nv ns Kslot Kown : ℕ) (j m u : String) (c : Com)
    {P : Env → Prop} (I : Env → Prop) (hnsB : ns < B)
    (hIb : ∀ σ, I σ → σ.vars m = ns ∧ σ.vars j ≤ ns ∧ σ.vars u ≤ nv)
    (hstep : ∀ σ, I σ → σ.vars j < ns →
      ∃ σ' K', Run B c σ σ' K' ∧ I σ' ∧
        σ.vars j ≤ σ'.vars j ∧ σ.vars u ≤ σ'.vars u ∧
        (σ.vars j < σ'.vars j ∨ σ.vars u < σ'.vars u) ∧
        K' ≤ Kslot * (σ'.vars j - σ.vars j) + Kown * (σ'.vars u - σ.vars u))
    (hPI : ∀ σ, P σ → I σ)
    (hK : ∀ σ, P σ →
      (Kslot + 4) * (ns - σ.vars j) + (Kown + 4) * (nv - σ.vars u) + 4 ≤ K) :
    Spec B P (scan j m c) (fun _ σ' => I σ' ∧ σ'.vars j = ns) K := by
  refine (Spec.while_potential (b := .lt (.var j) (.var m)) I
    (fun σ => (Kslot + 4) * (ns - σ.vars j) + (Kown + 4) * (nv - σ.vars u))
    (fun σ hI => by
      have h := hIb σ hI
      exact evalB_condLt_vars (by omega) (by omega))
    (fun σ hI hc => ?_) hPI (fun σ hσ => by have := hK σ hσ; simp; omega)).post ?_
  · have hlt : σ.vars j < ns := by
      have h := hIb σ hI
      have := lt_of_condLt_true hc
      omega
    obtain ⟨σ', K', hrun, hI', hj, hu, hmove, hcost⟩ := hstep σ hI hlt
    refine ⟨σ', K', hrun, hI', ?_⟩
    have h := hIb σ hI
    have h' := hIb σ' hI'
    -- the potential drops by exactly the two moves, since both pointers stay in range
    have e₁ : (Kslot + 4) * (ns - σ.vars j)
        = (Kslot + 4) * (ns - σ'.vars j) + (Kslot + 4) * (σ'.vars j - σ.vars j) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    have e₂ : (Kown + 4) * (nv - σ.vars u)
        = (Kown + 4) * (nv - σ'.vars u) + (Kown + 4) * (σ'.vars u - σ.vars u) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    have hpay := pay_le Kslot Kown (σ'.vars j - σ.vars j) (σ'.vars u - σ.vars u) K'
      (by omega) hcost
    simp only [size_condLt, size_var]
    omega
  · rintro σ σ' - ⟨hI', hfalse⟩
    have h₁ := le_of_condLt_false hfalse
    have h₂ := hIb σ' hI'
    exact ⟨hI', by omega⟩

/-- **The owner-advancing scan, as a step of a larger loop.** The same
statement with the cost bound read off the state the pass *starts* in
rather than announced as a constant — which is what a turn of an outer
amortized loop owes its own potential, since a turn's cost there is
existential and may not be bounded by any constant.

The credit form `K + Φ σ' ≤ Φ σ + 4` that `Queue.drain_run` exports is
deliberately not what this is. `drain`'s potential is its caller's
parameter, so handing back the drop exposes nothing; this pass's
potential is the combinator's own, and the point of the export is that
the caller never writes it down. A caller who needs the credit for the
rows the pass left unvisited is asking for the potential, and should say
so — then this becomes the primitive and `ownerScan_spec` derives from
it, the way `Queue`'s two forms do. -/
theorem ownerScan_run (B nv ns Kslot Kown : ℕ) (j m u : String) (c : Com)
    (I : Env → Prop) (hnsB : ns < B)
    (hIb : ∀ σ, I σ → σ.vars m = ns ∧ σ.vars j ≤ ns ∧ σ.vars u ≤ nv)
    (hstep : ∀ σ, I σ → σ.vars j < ns →
      ∃ σ' K', Run B c σ σ' K' ∧ I σ' ∧
        σ.vars j ≤ σ'.vars j ∧ σ.vars u ≤ σ'.vars u ∧
        (σ.vars j < σ'.vars j ∨ σ.vars u < σ'.vars u) ∧
        K' ≤ Kslot * (σ'.vars j - σ.vars j) + Kown * (σ'.vars u - σ.vars u))
    {σ : Env} (hI : I σ) :
    ∃ σ' K, Run B (scan j m c) σ σ' K ∧ I σ' ∧ σ'.vars j = ns ∧
      K ≤ (Kslot + 4) * (ns - σ.vars j) + (Kown + 4) * (nv - σ.vars u) + 4 := by
  obtain ⟨σ', hrun, hI', hj⟩ :=
    (ownerScan_spec B ((Kslot + 4) * (ns - σ.vars j) + (Kown + 4) * (nv - σ.vars u) + 4)
      nv ns Kslot Kown j m u c (P := fun τ => τ = σ) I hnsB hIb hstep
      (fun τ hτ => hτ ▸ hI) (fun τ hτ => by subst hτ; exact le_rfl)).run rfl
  exact ⟨σ', _, hrun, hI', hj, le_rfl⟩

/-! ### The worked example

A structure with three rows and four slots — row `0` holds two slots,
rows `1` and `2` one each — scanned twice: one row through
`rowScan_spec`, and the whole target array through `ownerScan_spec`,
with the owner pointer advancing at the row ends. The second is Lax11's
`scanBody` in miniature: the turn tests `j < off[u+1]` and either takes
the slot or moves the owner on, and neither its proof nor the pass's
mentions a potential. The compiled program builds the structure with
its own stores — the machine's memory starts zeroed — and writes each
slot's owner and target out, so the `#guard` sees the owner advance. -/

namespace Demo

/-- The offsets of the example: rows `0`, `1`, `2` start at `0`, `2`,
`3`, and the four slots end at `4`. -/
def offD : ℕ → ℕ := fun i => if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else 4

/-- The targets of the example. -/
def tgtD : ℕ → ℕ := fun p => if p = 0 then 1 else if p = 1 then 2 else if p = 2 then 0 else 1

#guard arrOf 4 offD = [0, 2, 3, 4]
#guard arrOf 4 tgtD = [1, 2, 0, 1]
#guard rowLen offD 0 = 2
#guard row offD tgtD 0 = [1, 2]
#guard row offD tgtD 1 = [0]
#guard row offD tgtD 2 = [1]

/-- The example's structure really is one: three rows, four slots, every
target below three. -/
theorem csrD {σ : Env} (ho : σ.arrs "off" = arrOf 4 offD) (ht : σ.arrs "tgt" = arrOf 4 tgtD) :
    Csr "off" "tgt" 3 4 3 offD tgtD σ :=
  ⟨ho, ht, by decide, by decide, by decide⟩

/-! #### One row -/

/-- One slot of a row scan: read the target, move on. -/
def slotStep (t j w : String) : Com :=
  .seq (slot t j w) (.assign j (.add (.var j) (.lit 1)))

@[simp] theorem wvars_slotStep (t j w : String) : (slotStep t j w).wvars = [w, j] := by
  simp [slotStep, slot, Com.wvars]

@[simp] theorem warrs_slotStep (t j w : String) : (slotStep t j w).warrs = [] := by
  simp [slotStep, slot, Com.warrs]

@[simp] theorem not_reads_slotStep (t j w : String) : ¬ (slotStep t j w).reads := by
  simp [slotStep, slot, Com.reads]

@[simp] theorem noWrite_slotStep (t j w : String) : (slotStep t j w).NoWrite := by
  simp [slotStep, slot, Com.NoWrite]

/-- Its specification, by `slot_spec` and the walk. -/
theorem slotStep_spec (B nv ns V : ℕ) (o t j w : String) (off tgt : ℕ → ℕ) (hjw : j ≠ w) :
    Spec B (fun σ => SlotPre o t j nv ns V B off tgt σ ∧ σ.vars j + 1 < B)
      (slotStep t j w)
      (fun σ σ' => Csr o t nv ns V off tgt σ' ∧ σ'.vars w = tgt (σ.vars j) ∧
        σ'.vars j = σ.vars j + 1) 8 := by
  run_vcg [(slot_spec B nv ns V o t j w off tgt).frame] <;>
    (try simp_all [Pre, SlotPost, Ne.symm hjw]); (try omega)

/-- **A row, scanned.** The invariant is the structure and the row
bounds; the body costs eight and the loop twelve a slot. -/
theorem rowDemo_spec (B nv ns V hi : ℕ) (o t j jend w : String) (off tgt : ℕ → ℕ)
    (hwj : w ≠ j) (hwje : w ≠ jend) (hjje : j ≠ jend) (hVB : V ≤ B) (hhi : hi ≤ ns)
    (hnsB : ns < B) :
    Spec B (fun σ => Csr o t nv ns V off tgt σ ∧ σ.vars jend = hi ∧ σ.vars j ≤ hi)
      (scan j jend (slotStep t j w))
      (fun _ σ' => Csr o t nv ns V off tgt σ' ∧ σ'.vars j = hi) (12 * ns + 4) := by
  refine (rowScan_spec B (12 * ns + 4) hi 8 j jend (slotStep t j w)
    (I := fun σ => Csr o t nv ns V off tgt σ ∧ σ.vars jend = hi ∧ σ.vars j ≤ hi)
    (by omega) (fun σ hI => ⟨hI.2.1, hI.2.2⟩) ?_ (fun σ hσ => hσ)
    (fun σ _ => by
      have h : hi - σ.vars j ≤ ns := by omega
      have : (8 + 4) * (hi - σ.vars j) ≤ 12 * ns := by
        exact Nat.mul_le_mul_left 12 h
      omega)).post (fun _ σ' _ hQ => ⟨hQ.1.1, hQ.2⟩)
  intro σ hI hlt
  obtain ⟨σ', hrun, hQ⟩ :=
    (slotStep_spec B nv ns V o t j w off tgt (Ne.symm hwj)).frame σ
      ⟨⟨⟨hI.1, hVB, hnsB⟩, by omega⟩, by omega⟩
  refine ⟨σ', 8, hrun, ⟨hQ.1.1, ?_, by omega⟩, hQ.1.2.2, le_rfl⟩
  rw [hQ.2.1 jend (by simp [Ne.symm hjje, Ne.symm hwje]), hI.2.1]

/-! #### The whole array, owner and all -/

/-- The body of the owner-advancing scan: inside the owner's row, take
the slot; at its end, move the owner on. This is Lax11's `scanBody`
with the slot's work replaced by a read. -/
def ownerStep (o t j w u : String) : Com :=
  .ite (.lt (.var j) (.get o (.add (.var u) (.lit 1))))
    (slotStep t j w)
    (.assign u (.add (.var u) (.lit 1)))

@[simp] theorem wvars_ownerStep (o t j w u : String) :
    (ownerStep o t j w u).wvars = [w, j, u] := by simp [ownerStep, Com.wvars]

@[simp] theorem warrs_ownerStep (o t j w u : String) : (ownerStep o t j w u).warrs = [] := by
  simp [ownerStep, Com.warrs]

@[simp] theorem not_reads_ownerStep (o t j w u : String) : ¬ (ownerStep o t j w u).reads := by
  simp [ownerStep, Com.reads]

@[simp] theorem noWrite_ownerStep (o t j w u : String) : (ownerStep o t j w u).NoWrite := by
  simp [ownerStep, Com.NoWrite]

/-- What a turn of the owner-advancing scan is run in. Beyond the
relation and the two pointers: the offset read at `u + 1` is pre-loaded
in both `getD` forms *and with its value*, so that the branch the walk
splits on arrives as a statement about `off`, not about a list. -/
abbrev OwnerRead (o t j u : String) (nv ns V B : ℕ) (off tgt : ℕ → ℕ) (σ : Env) : Prop :=
  Csr o t nv ns V off tgt σ ∧ V ≤ B ∧ ns < B ∧ nv + 1 < B ∧
    σ.vars j < ns ∧ σ.vars u ≤ nv ∧ off (σ.vars u) ≤ σ.vars j ∧
    σ.vars u + 1 < (σ.arrs o).length ∧
    (σ.arrs o).getD (σ.vars u + 1) 0 < B ∧ (σ.arrs o)[σ.vars u + 1]?.getD 0 < B ∧
    (σ.arrs o)[σ.vars u + 1]?.getD 0 = off (σ.vars u + 1) ∧
    (σ.arrs o).getD (σ.vars u + 1) 0 = off (σ.vars u + 1) ∧
    σ.vars j < (σ.arrs t).length ∧ (σ.arrs t).getD (σ.vars j) 0 < B ∧
    (σ.arrs t)[σ.vars j]?.getD 0 < B ∧
    σ.vars u + 1 < B ∧ σ.vars j + 1 < B

/-- The whole package comes off the relation, since the pointer is a
slot and so its owner is a row. -/
theorem ownerRead_of_pre (B nv ns V : ℕ) (o t j u : String) (off tgt : ℕ → ℕ) (σ : Env)
    (hc : Csr o t nv ns V off tgt σ) (hVB : V ≤ B) (hnsB : ns < B) (hnvB : nv + 1 < B)
    (hj : σ.vars j < ns) (hu : σ.vars u ≤ nv) (hlo : off (σ.vars u) ≤ σ.vars j) :
    OwnerRead o t j u nv ns V B off tgt σ := by
  have hult : σ.vars u < nv := hc.owner_lt hu hlo hj
  have hval : (σ.arrs o).getD (σ.vars u + 1) 0 = off (σ.vars u + 1) :=
    hc.getD_off (by omega)
  have htv : (σ.arrs t).getD (σ.vars j) 0 < B := by
    rw [hc.getD_tgt hj]; exact hc.lt hVB hj
  exact ⟨hc, hVB, hnsB, hnvB, hj, hu, hlo, by rw [hc.length_off]; omega,
    by rw [hval]; exact hc.off_lt hnsB (by omega),
    by rw [← List.getD_eq_getElem?_getD, hval]; exact hc.off_lt hnsB (by omega),
    by rw [← List.getD_eq_getElem?_getD, hval], hval,
    by rw [hc.length_tgt]; exact hj, htv, by rwa [← List.getD_eq_getElem?_getD],
    by omega, by omega⟩

/-- **A turn.** It either passes a slot or moves the owner on, and at
the end of the owner's row the second is what happens — which is the
fact the invariant needs to keep `off u ≤ j`. -/
theorem ownerStep_spec (B nv ns V : ℕ) (o t j w u : String) (off tgt : ℕ → ℕ)
    (hjw : j ≠ w) (hwu : w ≠ u) (hju : j ≠ u) :
    Spec B (OwnerRead o t j u nv ns V B off tgt) (ownerStep o t j w u)
      (fun σ σ' => Csr o t nv ns V off tgt σ' ∧
        ((σ'.vars j = σ.vars j + 1 ∧ σ'.vars u = σ.vars u) ∨
          (σ'.vars j = σ.vars j ∧ σ'.vars u = σ.vars u + 1 ∧
            off (σ.vars u + 1) ≤ σ.vars j))) 15 := by
  run_vcg [(slotStep_spec B nv ns V o t j w off tgt hjw).frame] <;>
    (try simp_all [Ne.symm hwu, Ne.symm hju]);
    (try exact ⟨⟨by assumption, by assumption, by assumption⟩, by assumption⟩)

/-- **The whole array, scanned.** The turn costs fifteen either way, so
the pass costs nineteen per slot and nineteen per row, plus the last
test. Nothing in this proof mentions a potential: the two moves and the
turn's cost are all `ownerScan_spec` asks for. -/
theorem scanDemo_spec (B nv ns V : ℕ) (o t j m w u : String) (off tgt : ℕ → ℕ)
    (hwj : w ≠ j) (hwu : w ≠ u) (hju : j ≠ u) (hwm : w ≠ m) (hjm : j ≠ m) (hum : u ≠ m)
    (hVB : V ≤ B) (hnsB : ns < B) (hnvB : nv + 1 < B) (hoff0 : off 0 = 0) :
    Spec B (fun σ => Csr o t nv ns V off tgt σ ∧ σ.vars m = ns ∧ σ.vars j = 0 ∧
        σ.vars u = 0)
      (scan j m (ownerStep o t j w u))
      (fun _ σ' => Csr o t nv ns V off tgt σ' ∧ σ'.vars j = ns)
      (19 * ns + 19 * nv + 4) := by
  refine (ownerScan_spec B (19 * ns + 19 * nv + 4) nv ns 15 15 j m u (ownerStep o t j w u)
    (I := fun σ => Csr o t nv ns V off tgt σ ∧ σ.vars m = ns ∧ σ.vars j ≤ ns ∧
      σ.vars u ≤ nv ∧ off (σ.vars u) ≤ σ.vars j)
    hnsB (fun σ hI => ⟨hI.2.1, hI.2.2.1, hI.2.2.2.1⟩) ?_
    (fun σ hσ => ⟨hσ.1, hσ.2.1, by omega, by omega, by rw [hσ.2.2.1, hσ.2.2.2, hoff0]⟩)
    (fun σ hσ => by
      have h₁ : (15 + 4) * (ns - σ.vars j) ≤ 19 * ns := Nat.mul_le_mul_left 19 (by omega)
      have h₂ : (15 + 4) * (nv - σ.vars u) ≤ 19 * nv := Nat.mul_le_mul_left 19 (by omega)
      omega)).post (fun _ σ' _ hQ => ⟨hQ.1.1, hQ.2⟩)
  intro σ hI hlt
  obtain ⟨σ', hrun, hQ⟩ :=
    (ownerStep_spec B nv ns V o t j w u off tgt (Ne.symm hwj) hwu hju).frame σ
    (ownerRead_of_pre B nv ns V o t j u off tgt σ hI.1 hVB hnsB hnvB hlt hI.2.2.2.1
      hI.2.2.2.2)
  have hm : σ'.vars m = σ.vars m := hQ.2.1 m (by simp [Ne.symm hjm, Ne.symm hwm, Ne.symm hum])
  refine ⟨σ', 15, hrun, ⟨hQ.1.1, by rw [hm]; exact hI.2.1, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rcases hQ.1.2 with ⟨h₁, h₂⟩ | ⟨h₁, -, -⟩ <;> omega
  · rcases hQ.1.2 with ⟨h₁, h₂⟩ | ⟨-, h₂, -⟩
    · omega
    · have := hI.1.owner_lt hI.2.2.2.1 hI.2.2.2.2 hlt
      omega
  · rcases hQ.1.2 with ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩
    · rw [h₁, h₂]; exact le_trans hI.2.2.2.2 (by omega)
    · rw [h₁, h₂]; exact h₃
  · rcases hQ.1.2 with ⟨h₁, -⟩ | ⟨h₁, -, -⟩ <;> omega
  · rcases hQ.1.2 with ⟨-, h₂⟩ | ⟨-, h₂, -⟩ <;> omega
  · rcases hQ.1.2 with ⟨h₁, -⟩ | ⟨-, h₂, -⟩
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases hQ.1.2 with ⟨h₁, h₂⟩ | ⟨h₁, h₂, -⟩ <;> rw [h₁, h₂] <;> omega

/-! #### Through the compiler and the machine

The block above with the offsets and the targets stored first, the two
readings written out at each slot, and the whole thing compiled and
run. The machine's memory starts zeroed, so the structure has to be
built by the program itself. -/

/-- Build the example's structure: four offsets, four targets. -/
def setup (o t : String) : Com :=
  .seq (.store o (.lit 0) (.lit 0))
    (.seq (.store o (.lit 1) (.lit 2))
      (.seq (.store o (.lit 2) (.lit 3))
        (.seq (.store o (.lit 3) (.lit 4))
          (.seq (.store t (.lit 0) (.lit 1))
            (.seq (.store t (.lit 1) (.lit 2))
              (.seq (.store t (.lit 2) (.lit 0))
                (.store t (.lit 3) (.lit 1))))))))

/-- The turn of the scan, with the owner and the target written out. -/
def ownerStepWatched (o t j w u : String) : Com :=
  .ite (.lt (.var j) (.get o (.add (.var u) (.lit 1))))
    (.seq (slot t j w)
      (.seq (.write (.var u))
        (.seq (.write (.var w)) (.assign j (.add (.var j) (.lit 1))))))
    (.assign u (.add (.var u) (.lit 1)))

/-- The whole example: build the structure, then scan it. -/
def demoWatched (o t j m w u : String) : Com :=
  .seq (setup o t)
    (.seq (.assign m (.lit 4))
      (scan j m (ownerStepWatched o t j w u)))

/-- Four scalars, two arrays, four temporaries. -/
def layout : Lax759944Proofs.Legacy.Compile.Layout := ⟨["j", "m", "w", "u"], ["off", "tgt"], 4⟩

/-- The machine program. -/
def prog : Lax759944Proofs.Legacy.Ram.Program :=
  Lax759944Proofs.Legacy.Compile.compileProgram layout (demoWatched "off" "tgt" "j" "m" "w" "u")

/-- The layout covers the block, so the compilation is the one the
simulation theorem is about and not an accident. -/
theorem demoWatched_ok :
    Lax759944Proofs.Legacy.Compile.Com.Ok layout (demoWatched "off" "tgt" "j" "m" "w" "u") := by
  simp [demoWatched, setup, ownerStepWatched, slot, scan, layout,
    Lax759944Proofs.Legacy.Compile.Com.Ok, Lax759944Proofs.Legacy.Compile.Cond.Ok, Lax759944Proofs.Legacy.Compile.condExpr,
    Lax759944Proofs.Legacy.Compile.Expr.Ok]

/-- Run it. The four slots come out paired with their owners: the first
two slots belong to row `0`, the third to row `1`, the fourth to row
`2`, and the owner pointer advances between them without any slot being
read twice. -/
def demoRun : Option (List ℕ × ℕ) := runOut 16 4000 prog (Lax759944Proofs.Legacy.Ram.initState []) 0

#guard demoRun = some ([0, 1, 0, 2, 1, 0, 2, 1], 310)

end Demo

end Csr

end Lax759944Proofs.Legacy.Reasoning.Lib
