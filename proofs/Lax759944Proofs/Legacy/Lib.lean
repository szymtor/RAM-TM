-- Adapted 2026-09-15 from word-ram-v4-33 at 0aa87e1f6e6add4abe4f4e0aff8fe4a28950b2ea.
-- Namespace relocated for use as a proof-only intermediate; semantics unchanged.
import Lax759944Proofs.Legacy.Lib.Basic
import Lax759944Proofs.Legacy.Lib.Ind
import Lax759944Proofs.Legacy.Lib.Stack
import Lax759944Proofs.Legacy.Lib.Trail
import Lax759944Proofs.Legacy.Lib.Queue
import Lax759944Proofs.Legacy.Lib.Csr
import Lax759944Proofs.Legacy.Lib.Fill

/-!
The data-structure library: one module per structure, each an
abstraction relation and its operations exported as `Spec`s with cost.

`Lib/Basic.lean` holds what they share — the pointwise cell update, and
the driver their worked examples are checked with. `Lib/Ind.lean` is the
indicator array, and its header states the shape the remaining modules
follow. `Lib/Stack.lean` is the search stack of both drivers, and
`Lib/Trail.lean` the undo trail of Lax15's two rungs, whose `unwind`
loop is the first loop the kit exports as a `Spec`. `Lib/Queue.lean` is
the breadth-first queue of the two search drivers; its `drain` is the
first loop the kit exports with the *body* left to the caller, since in
both consumers the body is the algorithm. `Lib/Csr.lean` is the
offsets-and-targets block structure every adjacency list in the repo is
stored in, and its two scans — one row, and the whole array with the
owner pointer advancing — are the most-copied loops here; both are
combinators with the body open, and the second is where the amortized
potential of an owner-advancing pass stops being the caller's problem.
`Lib/Fill.lean` is the array a counter fills cell by cell — what a flat
pass over an array leaves behind — and the one module whose export is a
whole phase: `Fill.loop_spec` is `Spec.forRangeZero` and the module's
one operation put together, so that clearing an array is one line at a
call site.
-/
