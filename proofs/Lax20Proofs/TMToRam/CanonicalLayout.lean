import Lax20Proofs.TMToRam.NativeMachine

namespace Lax13Proofs.Imp

open Lax13Proofs.Compile

def Expr.scalarNames : Expr → List String
  | .lit _ => []
  | .var x => [x]
  | .get _ i => i.scalarNames
  | .bin _ e f => e.scalarNames ++ f.scalarNames

def Expr.arrayNames : Expr → List String
  | .lit _ | .var _ => []
  | .get a i => a :: i.arrayNames
  | .bin _ e f => e.arrayNames ++ f.arrayNames

def Expr.tempNeed : Expr → ℕ
  | .lit _ | .var _ => 0
  | .get _ i => max i.tempNeed 1
  | .bin _ e f => max f.tempNeed (e.tempNeed + 1)

def Cond.scalarNames (b : Cond) : List String := (condExpr b).scalarNames
def Cond.arrayNames (b : Cond) : List String := (condExpr b).arrayNames
def Cond.tempNeed (b : Cond) : ℕ := (condExpr b).tempNeed

def Com.scalarNames : Com → List String
  | .skip => []
  | .assign x e => x :: e.scalarNames
  | .store _ i e => i.scalarNames ++ e.scalarNames
  | .seq c d => c.scalarNames ++ d.scalarNames
  | .ite b c d => b.scalarNames ++ c.scalarNames ++ d.scalarNames
  | .while b c => b.scalarNames ++ c.scalarNames
  | .read x => [x]
  | .write e => e.scalarNames

def Com.arrayNames : Com → List String
  | .skip => []
  | .assign _ e => e.arrayNames
  | .store a i e => a :: (i.arrayNames ++ e.arrayNames)
  | .seq c d => c.arrayNames ++ d.arrayNames
  | .ite b c d => b.arrayNames ++ c.arrayNames ++ d.arrayNames
  | .while b c => b.arrayNames ++ c.arrayNames
  | .read _ => []
  | .write e => e.arrayNames

def Com.tempNeed : Com → ℕ
  | .skip | .read _ => 0
  | .assign _ e => e.tempNeed
  | .store _ i e => max 1 (max i.tempNeed (e.tempNeed + 1))
  | .seq c d => max c.tempNeed d.tempNeed
  | .ite b c d => max b.tempNeed (max c.tempNeed d.tempNeed)
  | .while b c => max b.tempNeed c.tempNeed
  | .write e => max 1 e.tempNeed

def Com.canonicalLayout (c : Com) : Layout where
  scalars := c.scalarNames
  arrays := c.arrayNames
  temps := c.tempNeed + 1

theorem Expr.ok_of_names (e : Expr) (L : Layout) (d : ℕ)
    (hscalars : ∀ x ∈ e.scalarNames, x ∈ L.scalars)
    (harrays : ∀ a ∈ e.arrayNames, a ∈ L.arrays)
    (htemp : d + e.tempNeed < L.temps) : Expr.Ok L e d := by
  induction e generalizing d with
  | lit n => trivial
  | var x => exact hscalars x (by simp [Expr.scalarNames])
  | get a i ih =>
      refine ⟨harrays a (by simp [Expr.arrayNames]), ?_, ?_⟩
      · apply ih
        · intro x hx
          exact hscalars x (by simpa [Expr.scalarNames] using hx)
        · intro b hb
          exact harrays b (by simp [Expr.arrayNames, hb])
        · simp [Expr.tempNeed] at htemp
          omega
      · simp [Expr.tempNeed] at htemp
        omega
  | bin op e f ihe ihf =>
      refine ⟨?_, ?_, ?_⟩
      · apply ihf
        · intro x hx
          exact hscalars x (by simp [Expr.scalarNames, hx])
        · intro a ha
          exact harrays a (by simp [Expr.arrayNames, ha])
        · simp [Expr.tempNeed] at htemp
          omega
      · apply ihe
        · intro x hx
          exact hscalars x (by simp [Expr.scalarNames, hx])
        · intro a ha
          exact harrays a (by simp [Expr.arrayNames, ha])
        · simp [Expr.tempNeed] at htemp
          omega
      · simp [Expr.tempNeed] at htemp
        omega

theorem Cond.ok_of_names (b : Cond) (L : Layout) (d : ℕ)
    (hscalars : ∀ x ∈ b.scalarNames, x ∈ L.scalars)
    (harrays : ∀ a ∈ b.arrayNames, a ∈ L.arrays)
    (htemp : d + b.tempNeed < L.temps) : Cond.Ok L b d := by
  exact Expr.ok_of_names (condExpr b) L d hscalars harrays htemp

theorem Com.ok_of_names (c : Com) (L : Layout)
    (hscalars : ∀ x ∈ c.scalarNames, x ∈ L.scalars)
    (harrays : ∀ a ∈ c.arrayNames, a ∈ L.arrays)
    (htemp : c.tempNeed < L.temps) : Com.Ok L c := by
  induction c with
  | skip => trivial
  | assign x e =>
      refine ⟨hscalars x (by simp [Com.scalarNames]), ?_⟩
      apply Expr.ok_of_names e L 0
      · intro y hy; exact hscalars y (by simp [Com.scalarNames, hy])
      · intro a ha; exact harrays a (by simpa [Com.arrayNames] using ha)
      · simpa [Com.tempNeed] using htemp
  | store a i e =>
      refine ⟨harrays a (by simp [Com.arrayNames]), ?_, ?_, ?_⟩
      · apply Expr.ok_of_names i L 0
        · intro x hx; exact hscalars x (by simp [Com.scalarNames, hx])
        · intro b hb; exact harrays b (by simp [Com.arrayNames, hb])
        · simp [Com.tempNeed] at htemp; omega
      · apply Expr.ok_of_names e L 1
        · intro x hx; exact hscalars x (by simp [Com.scalarNames, hx])
        · intro b hb; exact harrays b (by simp [Com.arrayNames, hb])
        · simp [Com.tempNeed] at htemp; omega
      · simp [Com.tempNeed] at htemp; omega
  | seq c d ihc ihd =>
      constructor
      · apply ihc
        · intro x hx; exact hscalars x (by simp [Com.scalarNames, hx])
        · intro a ha; exact harrays a (by simp [Com.arrayNames, ha])
        · simp [Com.tempNeed] at htemp; omega
      · apply ihd
        · intro x hx; exact hscalars x (by simp [Com.scalarNames, hx])
        · intro a ha; exact harrays a (by simp [Com.arrayNames, ha])
        · simp [Com.tempNeed] at htemp; omega
  | ite b c d ihc ihd =>
      refine ⟨?_, ?_, ?_⟩
      · apply Cond.ok_of_names b L 0
        · intro x hx
          exact hscalars x (by
            simp only [Com.scalarNames, List.mem_append]
            exact Or.inl (Or.inl hx))
        · intro a ha
          exact harrays a (by
            simp only [Com.arrayNames, List.mem_append]
            exact Or.inl (Or.inl ha))
        · simp [Com.tempNeed] at htemp; omega
      · apply ihc
        · intro x hx; exact hscalars x (by simp [Com.scalarNames, hx])
        · intro a ha; exact harrays a (by simp [Com.arrayNames, ha])
        · simp [Com.tempNeed] at htemp; omega
      · apply ihd
        · intro x hx; exact hscalars x (by simp [Com.scalarNames, hx])
        · intro a ha; exact harrays a (by simp [Com.arrayNames, ha])
        · simp [Com.tempNeed] at htemp; omega
  | «while» b c ih =>
      constructor
      · apply Cond.ok_of_names b L 0
        · intro x hx
          change x ∈ (condExpr b).scalarNames at hx
          exact hscalars x (by
            simp only [Com.scalarNames, List.mem_append]
            exact Or.inl hx)
        · intro a ha
          change a ∈ (condExpr b).arrayNames at ha
          exact harrays a (by
            simp only [Com.arrayNames, List.mem_append]
            exact Or.inl ha)
        · simp [Com.tempNeed] at htemp; omega
      · apply ih
        · intro x hx; exact hscalars x (by simp [Com.scalarNames, hx])
        · intro a ha; exact harrays a (by simp [Com.arrayNames, ha])
        · simp [Com.tempNeed] at htemp; omega
  | read x => exact hscalars x (by simp [Com.scalarNames])
  | write e =>
      constructor
      · apply Expr.ok_of_names e L 0
        · intro x hx; exact hscalars x (by simpa [Com.scalarNames] using hx)
        · intro a ha; exact harrays a (by simpa [Com.arrayNames] using ha)
        · simp [Com.tempNeed] at htemp; omega
      · simp [Com.tempNeed] at htemp; omega

theorem Com.canonicalLayout_ok (c : Com) : Com.Ok c.canonicalLayout c := by
  apply Com.ok_of_names
  · intro x hx; exact hx
  · intro a ha; exact ha
  · simp [Com.canonicalLayout]

end Lax13Proofs.Imp
