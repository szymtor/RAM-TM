import Lax20Proofs.RamToTM.UnaryMultiplyMacro

namespace Lax20Proofs.RamToTM

open Turing TM2

inductive UnaryPowerLabel : Nat → Type
  | done : UnaryPowerLabel 0
  | mul {d : Nat} (label : UnaryMulLabel) : UnaryPowerLabel (d + 1)
  | move {d : Nat} : UnaryPowerLabel (d + 1)
  | next {d : Nat} (label : UnaryPowerLabel d) : UnaryPowerLabel (d + 1)

deriving instance DecidableEq for UnaryPowerLabel

def unaryPowerLabelSuccEquiv (d : Nat) :
    UnaryPowerLabel (d + 1) ≃ Option (UnaryMulLabel ⊕ UnaryPowerLabel d) where
  toFun
    | .mul l => some (.inl l)
    | .move => none
    | .next l => some (.inr l)
  invFun
    | some (.inl l) => .mul l
    | none => .move
    | some (.inr l) => .next l
  left_inv := by intro l; cases l <;> rfl
  right_inv := by
    intro l
    cases l with
    | none => rfl
    | some l => cases l <;> rfl

instance unaryPowerLabelFintype : (d : Nat) → Fintype (UnaryPowerLabel d)
  | 0 => Fintype.ofEquiv Unit
      { toFun := fun _ => .done
        invFun := fun _ => ()
        left_inv := by intro x; cases x; rfl
        right_inv := by intro x; cases x; rfl }
  | d + 1 => by
      letI := unaryPowerLabelFintype d
      exact Fintype.ofEquiv (Option (UnaryMulLabel ⊕ UnaryPowerLabel d))
        (unaryPowerLabelSuccEquiv d).symm

def unaryPowerStart : (d : Nat) → UnaryPowerLabel d
  | 0 => .done
  | _ + 1 => .mul .outer

def unaryPowerFinish : (d : Nat) → UnaryPowerLabel d
  | 0 => .done
  | d + 1 => .next (unaryPowerFinish d)

def unaryPowerProgram : (d : Nat) → UnaryPowerLabel d →
    TM2.Stmt (fun _ : UnaryMulStack => SparseSymbol)
      (UnaryPowerLabel d) SymbolMoveControl
  | 0, .done => .halt
  | d + 1, .mul .done => .goto fun _ => .move
  | d + 1, .mul label => mapLabelStmt .mul (unaryMulProgram label)
  | d + 1, .move =>
      .pop .destination (fun _ a => ⟨a⟩) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .next (unaryPowerStart d))
        (.push .source (fun s => s.held.getD default) <|
          .load (fun _ => default) <| .goto fun _ => .move)
  | d + 1, .next label => mapLabelStmt .next (unaryPowerProgram d label)

def unaryPowerCfg {d : Nat} (label : UnaryPowerLabel d)
    (source multiplier destination backup : List SparseSymbol) :
    TM2.Cfg (fun _ : UnaryMulStack => SparseSymbol)
      (UnaryPowerLabel d) SymbolMoveControl :=
  ⟨some label, default, unaryMulStacks source multiplier destination backup⟩

def unaryPowerCost (a b : Nat) : Nat → Nat
  | 0 => 0
  | d + 1 =>
      a * (2 * b + 3) + 2 + a * b + 1 + unaryPowerCost (a * b) b d

theorem unaryPower_mul_phase {d a b : Nat} :
    ((fun o => o.bind (TM2.step (unaryPowerProgram (d + 1))))^[
        a * (2 * b + 3) + 2])
      (some (unaryPowerCfg (.mul .outer)
        (unaryMarkers a) (unaryMarkers b) [] [])) =
    some (unaryPowerCfg (.move : UnaryPowerLabel (d + 1)) []
      (unaryMarkers b) (unaryMarkers (a * b)) []) := by
  have h := unaryMul_correct a b
  have hm :
      ((fun o => o.bind (TM2.step (unaryPowerProgram (d + 1))))^[
          a * (2 * b + 3) + 1])
        (some (unaryPowerCfg (.mul .outer)
          (unaryMarkers a) (unaryMarkers b) [] [])) =
      some (unaryPowerCfg (.mul .done)
        [] (unaryMarkers b) (unaryMarkers (a * b)) []) := by
    have hembed := iterate_mapLabelProgram_until_exit unaryMulProgram
      (unaryPowerProgram (d + 1)) UnaryPowerLabel.mul
      (fun l hl => by
        cases l with
        | done => exact (hl rfl).elim
        | outer | copy | restore => rfl) h
      (by simp [unaryMulCfg])
    simpa [mapLabelCfg, unaryMulCfg, unaryPowerCfg] using hembed
  have hnext :
      ((fun o => o.bind (TM2.step (unaryPowerProgram (d + 1))))^[1])
        (some (unaryPowerCfg (.mul .done) [] (unaryMarkers b)
          (unaryMarkers (a * b)) [])) =
      some (unaryPowerCfg (.move : UnaryPowerLabel (d + 1)) []
        (unaryMarkers b) (unaryMarkers (a * b)) []) := by
    simp [unaryPowerProgram, unaryPowerCfg, TM2.step]
  simpa using chain_iterations _ hm hnext

theorem unaryPower_move_phase_aux {d a b : Nat} (acc : List SparseSymbol) :
    ((fun o => o.bind (TM2.step (unaryPowerProgram (d + 1))))^[a + 1])
      (some (unaryPowerCfg (.move : UnaryPowerLabel (d + 1)) acc
        (unaryMarkers b) (unaryMarkers a) [])) =
    some (unaryPowerCfg (.next (unaryPowerStart d))
      (unaryMarkers a ++ acc) (unaryMarkers b) [] []) := by
  induction a generalizing acc with
  | zero =>
      simp [unaryMarkers, unaryPowerProgram, unaryPowerCfg, unaryMulStacks,
        TM2.step]
  | succ a ih =>
      have hs : unaryMarkers (a + 1) = .wordEnd :: unaryMarkers a := by
        rw [show a + 1 = Nat.succ a by omega]
        rfl
      rw [hs]
      have hstep :
          ((fun o => o.bind (TM2.step (unaryPowerProgram (d + 1))))^[1])
            (some (unaryPowerCfg (.move : UnaryPowerLabel (d + 1)) acc
              (unaryMarkers b) (.wordEnd :: unaryMarkers a) [])) =
          some (unaryPowerCfg (.move : UnaryPowerLabel (d + 1))
            (.wordEnd :: acc) (unaryMarkers b) (unaryMarkers a) []) := by
        simp [unaryPowerProgram, unaryPowerCfg, unaryMulStacks, TM2.step,
          Function.update]
        congr 2
        funext k
        cases k <;> rfl
      have hrest := ih (.wordEnd :: acc)
      have h := chain_iterations _ hstep hrest
      rw [show a + 1 + 1 = 1 + (a + 1) by omega]
      have hout : unaryMarkers a ++ (.wordEnd :: acc) =
          .wordEnd :: (unaryMarkers a ++ acc) := by
        change List.replicate a .wordEnd ++
            (List.replicate 1 .wordEnd ++ acc) =
          List.replicate 1 .wordEnd ++
            (List.replicate a .wordEnd ++ acc)
        rw [← List.append_assoc, ← List.replicate_add,
          ← List.append_assoc, ← List.replicate_add, Nat.add_comm a 1]
      simpa only [List.cons_append, hout] using h

theorem unaryPower_move_phase {d a b : Nat} :
    ((fun o => o.bind (TM2.step (unaryPowerProgram (d + 1))))^[a + 1])
      (some (unaryPowerCfg (.move : UnaryPowerLabel (d + 1)) []
        (unaryMarkers b) (unaryMarkers a) [])) =
    some (unaryPowerCfg (.next (unaryPowerStart d))
      (unaryMarkers a) (unaryMarkers b) [] []) := by
  simpa using unaryPower_move_phase_aux (d := d) (a := a) (b := b) []

theorem unaryPower_correct (d a b : Nat) :
    ((fun o => o.bind (TM2.step (unaryPowerProgram d)))^[
        unaryPowerCost a b d])
      (some (unaryPowerCfg (unaryPowerStart d)
        (unaryMarkers a) (unaryMarkers b) [] [])) =
    some (unaryPowerCfg (unaryPowerFinish d)
      (unaryMarkers (a * b ^ d)) (unaryMarkers b) [] []) := by
  induction d generalizing a with
  | zero => simp [unaryPowerCost, unaryPowerStart, unaryPowerFinish]
  | succ d ih =>
      rw [unaryPowerCost]
      have hmul := unaryPower_mul_phase (d := d) (a := a) (b := b)
      have hmove := unaryPower_move_phase (d := d) (a := a * b) (b := b)
      have htail := ih (a * b)
      have htail' :
          ((fun o => o.bind (TM2.step (unaryPowerProgram (d + 1))))^[
              unaryPowerCost (a * b) b d])
            (some (unaryPowerCfg (.next (unaryPowerStart d))
              (unaryMarkers (a * b)) (unaryMarkers b) [] [])) =
          some (unaryPowerCfg (.next (unaryPowerFinish d))
            (unaryMarkers ((a * b) * b ^ d)) (unaryMarkers b) [] []) := by
        have hembed := iterate_mapLabelProgram (unaryPowerProgram d)
          (unaryPowerProgram (d + 1)) UnaryPowerLabel.next
          (fun l => by simp [unaryPowerProgram])
          (unaryPowerCost (a * b) b d)
          (unaryPowerCfg (unaryPowerStart d) (unaryMarkers (a * b))
            (unaryMarkers b) [] [])
        rw [htail] at hembed
        simpa [mapLabelCfg, unaryPowerCfg] using hembed
      have h := chain_iterations _ (chain_iterations _ hmul hmove) htail'
      have hp : a * (b * b ^ d) = a * (b ^ d * b) := by ring
      rw [pow_succ]
      rw [← hp]
      simpa [unaryPowerStart, unaryPowerFinish, mul_assoc,
        Nat.add_assoc] using h

theorem unaryPowerProgram_finish_halt (d : Nat) :
    unaryPowerProgram d (unaryPowerFinish d) = .halt := by
  induction d with
  | zero => rfl
  | succ d ih => rw [unaryPowerFinish, unaryPowerProgram, ih]; rfl

noncomputable def unaryPowerCostPolynomial
    (accumulator multiplier : Polynomial Nat) : Nat → Polynomial Nat
  | 0 => 0
  | d + 1 =>
      accumulator * (2 * multiplier + 3) + 2 + accumulator * multiplier + 1 +
        unaryPowerCostPolynomial (accumulator * multiplier) multiplier d

@[simp] theorem unaryPowerCostPolynomial_eval
    (accumulator multiplier : Polynomial Nat) (d n : Nat) :
    (unaryPowerCostPolynomial accumulator multiplier d).eval n =
      unaryPowerCost (accumulator.eval n) (multiplier.eval n) d := by
  induction d generalizing accumulator with
  | zero => simp [unaryPowerCostPolynomial, unaryPowerCost]
  | succ d ih =>
      simp [unaryPowerCostPolynomial, unaryPowerCost, ih]

/-- Exact running-time polynomial for evaluation of the simple majorant
`C * (n + 1)^d`. -/
noncomputable def simpleMajorantEvalCostPolynomial
    (p : Polynomial Nat) : Polynomial Nat :=
  unaryPowerCostPolynomial (Polynomial.C (polyCoeffSum p))
    (Polynomial.X + 1) p.natDegree

@[simp] theorem simpleMajorantEvalCostPolynomial_eval
    (p : Polynomial Nat) (n : Nat) :
    (simpleMajorantEvalCostPolynomial p).eval n =
      unaryPowerCost (polyCoeffSum p) (n + 1) p.natDegree := by
  simp [simpleMajorantEvalCostPolynomial]

theorem unaryPower_simpleMajorant_correct (p : Polynomial Nat) (n : Nat) :
    ((fun o => o.bind (TM2.step (unaryPowerProgram p.natDegree)))^[
        (simpleMajorantEvalCostPolynomial p).eval n])
      (some (unaryPowerCfg (unaryPowerStart p.natDegree)
        (unaryMarkers (polyCoeffSum p)) (unaryMarkers (n + 1)) [] [])) =
    some (unaryPowerCfg (unaryPowerFinish p.natDegree)
      (unaryMarkers ((polynomialSimpleMajorant p).eval n))
      (unaryMarkers (n + 1)) [] []) := by
  simpa [polynomialSimpleMajorant_eval] using
    unaryPower_correct p.natDegree (polyCoeffSum p) (n + 1)

theorem unaryPower_core_simpleMajorant_correct {N : Nat} {R : Type}
    (p : Polynomial Nat) (n : Nat) (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum (UnaryPowerLabel p.natDegree) R) (FullInterpreterState N))
    (ambientState : FullInterpreterState N)
    (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (lensSpliceProgram unaryMulCoreRenaming
      FullInterpreterState.moveLens (unaryPowerProgram p.natDegree)
      (unaryPowerFinish p.natDegree) returnLabel right)))^[
        (simpleMajorantEvalCostPolynomial p).eval n + 1])
      (some (lensRenamedCfg unaryMulCoreRenaming
        FullInterpreterState.moveLens
        (unaryPowerCfg (unaryPowerStart p.natDegree)
          (unaryMarkers (polyCoeffSum p)) (unaryMarkers (n + 1)) [] [])
        ambientState ambientStacks)) =
    some (lensReturnCfg unaryMulCoreRenaming FullInterpreterState.moveLens
      returnLabel
      (unaryPowerCfg (unaryPowerFinish p.natDegree)
        (unaryMarkers ((polynomialSimpleMajorant p).eval n))
        (unaryMarkers (n + 1)) [] [])
      ambientState ambientStacks) := by
  apply transport_lensHaltingMacro_and_return unaryMulCoreRenaming
    FullInterpreterState.moveLens (unaryPowerProgram p.natDegree)
    (unaryPowerFinish p.natDegree) (unaryPowerProgram_finish_halt _) returnLabel right
    (unaryPower_simpleMajorant_correct p n) rfl ambientState ambientStacks

end Lax20Proofs.RamToTM
