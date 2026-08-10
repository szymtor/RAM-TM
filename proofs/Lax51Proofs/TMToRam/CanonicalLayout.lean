import Lax51Proofs.TMToRam.NativeMachine

namespace Lax51Proofs.TMToRam

open Lax13Proofs.Imp Lax13Proofs.Compile

def exprScalarNames : Expr → List String
  | .lit _ => []
  | .var x => [x]
  | .get _ i => exprScalarNames i
  | .bin _ e f => exprScalarNames e ++ exprScalarNames f

def exprArrayNames : Expr → List String
  | .lit _ | .var _ => []
  | .get a i => a :: exprArrayNames i
  | .bin _ e f => exprArrayNames e ++ exprArrayNames f

def exprTempNeed : Expr → ℕ
  | .lit _ | .var _ => 0
  | .get _ i => max (exprTempNeed i) 1
  | .bin _ e f => max (exprTempNeed f) (exprTempNeed e + 1)

def condScalarNames (b : Cond) : List String := exprScalarNames (condExpr b)
def condArrayNames (b : Cond) : List String := exprArrayNames (condExpr b)
def condTempNeed (b : Cond) : ℕ := exprTempNeed (condExpr b)

def comScalarNames : Com → List String
  | .skip => []
  | .assign x e => x :: exprScalarNames e
  | .store _ i e => exprScalarNames i ++ exprScalarNames e
  | .seq c d => comScalarNames c ++ comScalarNames d
  | .ite b c d => condScalarNames b ++ comScalarNames c ++ comScalarNames d
  | .while b c => condScalarNames b ++ comScalarNames c
  | .read x => [x]
  | .write e => exprScalarNames e

def comArrayNames : Com → List String
  | .skip => []
  | .assign _ e => exprArrayNames e
  | .store a i e => a :: (exprArrayNames i ++ exprArrayNames e)
  | .seq c d => comArrayNames c ++ comArrayNames d
  | .ite b c d => condArrayNames b ++ comArrayNames c ++ comArrayNames d
  | .while b c => condArrayNames b ++ comArrayNames c
  | .read _ => []
  | .write e => exprArrayNames e

def comTempNeed : Com → ℕ
  | .skip | .read _ => 0
  | .assign _ e => exprTempNeed e
  | .store _ i e => max 1 (max (exprTempNeed i) (exprTempNeed e + 1))
  | .seq c d => max (comTempNeed c) (comTempNeed d)
  | .ite b c d => max (condTempNeed b) (max (comTempNeed c) (comTempNeed d))
  | .while b c => max (condTempNeed b) (comTempNeed c)
  | .write e => max 1 (exprTempNeed e)

def comCanonicalLayout (c : Com) : Layout where
  scalars := comScalarNames c
  arrays := comArrayNames c
  temps := comTempNeed c + 1

theorem exprOkOfNames (e : Expr) (L : Layout) (d : ℕ)
    (hscalars : ∀ x ∈ exprScalarNames e, x ∈ L.scalars)
    (harrays : ∀ a ∈ exprArrayNames e, a ∈ L.arrays)
    (htemp : d + exprTempNeed e < L.temps) : Expr.Ok L e d := by
  induction e generalizing d with
  | lit n => trivial
  | var x => exact hscalars x (by simp [exprScalarNames])
  | get a i ih =>
      refine ⟨harrays a (by simp [exprArrayNames]), ?_, ?_⟩
      · apply ih
        · intro x hx
          exact hscalars x (by simpa [exprScalarNames] using hx)
        · intro b hb
          exact harrays b (by simp [exprArrayNames, hb])
        · simp [exprTempNeed] at htemp
          omega
      · simp [exprTempNeed] at htemp
        omega
  | bin op e f ihe ihf =>
      refine ⟨?_, ?_, ?_⟩
      · apply ihf
        · intro x hx
          exact hscalars x (by simp [exprScalarNames, hx])
        · intro a ha
          exact harrays a (by simp [exprArrayNames, ha])
        · simp [exprTempNeed] at htemp
          omega
      · apply ihe
        · intro x hx
          exact hscalars x (by simp [exprScalarNames, hx])
        · intro a ha
          exact harrays a (by simp [exprArrayNames, ha])
        · simp [exprTempNeed] at htemp
          omega
      · simp [exprTempNeed] at htemp
        omega

theorem condOkOfNames (b : Cond) (L : Layout) (d : ℕ)
    (hscalars : ∀ x ∈ condScalarNames b, x ∈ L.scalars)
    (harrays : ∀ a ∈ condArrayNames b, a ∈ L.arrays)
    (htemp : d + condTempNeed b < L.temps) : Cond.Ok L b d := by
  exact exprOkOfNames (condExpr b) L d hscalars harrays htemp

theorem comOkOfNames (c : Com) (L : Layout)
    (hscalars : ∀ x ∈ comScalarNames c, x ∈ L.scalars)
    (harrays : ∀ a ∈ comArrayNames c, a ∈ L.arrays)
    (htemp : comTempNeed c < L.temps) : Com.Ok L c := by
  induction c with
  | skip => trivial
  | assign x e =>
      refine ⟨hscalars x (by simp [comScalarNames]), ?_⟩
      apply exprOkOfNames e L 0
      · intro y hy; exact hscalars y (by simp [comScalarNames, hy])
      · intro a ha; exact harrays a (by simpa [comArrayNames] using ha)
      · simpa [comTempNeed] using htemp
  | store a i e =>
      refine ⟨harrays a (by simp [comArrayNames]), ?_, ?_, ?_⟩
      · apply exprOkOfNames i L 0
        · intro x hx; exact hscalars x (by simp [comScalarNames, hx])
        · intro b hb; exact harrays b (by simp [comArrayNames, hb])
        · simp [comTempNeed] at htemp; omega
      · apply exprOkOfNames e L 1
        · intro x hx; exact hscalars x (by simp [comScalarNames, hx])
        · intro b hb; exact harrays b (by simp [comArrayNames, hb])
        · simp [comTempNeed] at htemp; omega
      · simp [comTempNeed] at htemp; omega
  | seq c d ihc ihd =>
      constructor
      · apply ihc
        · intro x hx; exact hscalars x (by simp [comScalarNames, hx])
        · intro a ha; exact harrays a (by simp [comArrayNames, ha])
        · simp [comTempNeed] at htemp; omega
      · apply ihd
        · intro x hx; exact hscalars x (by simp [comScalarNames, hx])
        · intro a ha; exact harrays a (by simp [comArrayNames, ha])
        · simp [comTempNeed] at htemp; omega
  | ite b c d ihc ihd =>
      refine ⟨?_, ?_, ?_⟩
      · apply condOkOfNames b L 0
        · intro x hx
          exact hscalars x (by
            simp only [comScalarNames, List.mem_append]
            exact Or.inl (Or.inl hx))
        · intro a ha
          exact harrays a (by
            simp only [comArrayNames, List.mem_append]
            exact Or.inl (Or.inl ha))
        · simp [comTempNeed] at htemp; omega
      · apply ihc
        · intro x hx; exact hscalars x (by simp [comScalarNames, hx])
        · intro a ha; exact harrays a (by simp [comArrayNames, ha])
        · simp [comTempNeed] at htemp; omega
      · apply ihd
        · intro x hx; exact hscalars x (by simp [comScalarNames, hx])
        · intro a ha; exact harrays a (by simp [comArrayNames, ha])
        · simp [comTempNeed] at htemp; omega
  | «while» b c ih =>
      constructor
      · apply condOkOfNames b L 0
        · intro x hx
          change x ∈ exprScalarNames (condExpr b) at hx
          exact hscalars x (by
            simp only [comScalarNames, List.mem_append]
            exact Or.inl hx)
        · intro a ha
          change a ∈ exprArrayNames (condExpr b) at ha
          exact harrays a (by
            simp only [comArrayNames, List.mem_append]
            exact Or.inl ha)
        · simp [comTempNeed] at htemp; omega
      · apply ih
        · intro x hx; exact hscalars x (by simp [comScalarNames, hx])
        · intro a ha; exact harrays a (by simp [comArrayNames, ha])
        · simp [comTempNeed] at htemp; omega
  | read x => exact hscalars x (by simp [comScalarNames])
  | write e =>
      constructor
      · apply exprOkOfNames e L 0
        · intro x hx; exact hscalars x (by simpa [comScalarNames] using hx)
        · intro a ha; exact harrays a (by simpa [comArrayNames] using ha)
        · simp [comTempNeed] at htemp; omega
      · simp [comTempNeed] at htemp; omega

theorem comCanonicalLayoutOk (c : Com) : Com.Ok (comCanonicalLayout c) c := by
  apply comOkOfNames
  · intro x hx; exact hx
  · intro a ha; exact ha
  · simp [comCanonicalLayout]

end Lax51Proofs.TMToRam
