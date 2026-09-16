import Lax759944Proofs.GenericTimeSimulation
import Lax759944Proofs.TuringRamEquivalence
import Lax759944Proofs.TuringRamPolytimeEquivalence
import Lax759944Proofs.TapeRamNativeLowering

-- Audit the actual public endpoints and the all-instruction lowerer together.
-- In particular these declarations must not use a concept axiom as a premise.
#print axioms Lax759944Proofs.TuringRamEquivalence.ramComputable_iff_computable
#print axioms Lax759944Proofs.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime
#print axioms Lax759944Proofs.TapeRamNativeLowering.runsTo
#print axioms Lax759944Proofs.TapeRamBufferedSimulation.runsTo_compile
#print axioms Lax759944Proofs.GenericTimeSimulation.ramInTime_to_turingInPolynomialOverhead
#print axioms Lax759944Proofs.GenericTimeSimulation.turingWithInputTime_to_ramInPolynomialOverhead

example (f : List Nat → List Nat) :
    Lax759944.TuringRamEquivalence.RamComputable f ↔ Computable f :=
  Lax759944Proofs.TuringRamEquivalence.ramComputable_iff_computable f

example (f : List Nat → List Nat) :
    Lax759944.RamPolytime.RamPolytime f ↔ Lax759944.TuringPolytime.TuringPolytime f :=
  Lax759944Proofs.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime f

-- The generic-time endpoint must match the full public proposition exactly.
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let expected ← getConstInfo
    `Lax759944.RamToTuringGenericTime.ramInTime_to_turingInPolynomialOverhead
  let actual ← getConstInfo
    `Lax759944Proofs.GenericTimeSimulation.ramInTime_to_turingInPolynomialOverhead
  unless ← isDefEq actual.type expected.type do
    throwError "RAM-to-Turing generic-time proof differs from its public statement"
