import Lax51Proofs.TMToRam.InterpreterTame

namespace Lax51Proofs.TMToRam

open Lax13Proofs.Imp
open Lax13Proofs.Compile Lax13Proofs.Simulation Lax13.Ram

/-- The complete native interpreter has a bounded IMP+ execution at an
explicit bit exponent: input bit-size plus its fixed syntactic growth
constant times the already-established execution-cost bound. -/
theorem FinTM2.compileNativeMachine_outputsInTime_bounded (tm : Turing.FinTM2)
    (inputAlphabet : tm.Γ tm.k₀ ≃ Lax51.BinaryWordEncoding.Symbol)
    (outputAlphabet : tm.Γ tm.k₁ ≃ Lax51.BinaryWordEncoding.Symbol)
    (x y : List ℕ) (bound : ℕ)
    (hrun : Turing.TM2OutputsInTime tm
      (List.map inputAlphabet.invFun (Lax51.BinaryWordEncoding.encode x))
      (some (List.map outputAlphabet.invFun
        (Lax51.BinaryWordEncoding.encode y))) bound) :
    let inputStack := @finCode tm.K tm.kFin tm.kDecidableEq tm.k₀
    let outputStack := @finCode tm.K tm.kFin tm.kDecidableEq tm.k₁
    let separatorIn := FinTM2.inputSymbolCode tm inputAlphabet .separator
    let zeroIn := FinTM2.inputSymbolCode tm inputAlphabet .zero
    let oneIn := FinTM2.inputSymbolCode tm inputAlphabet .one
    let separatorOut := FinTM2.outputSymbolCode tm outputAlphabet .separator
    let zeroOut := FinTM2.outputSymbolCode tm outputAlphabet .zero
    let oneOut := FinTM2.outputSymbolCode tm outputAlphabet .one
    let initialStateCode := @finCode tm.σ tm.σFin (Classical.decEq tm.σ) tm.initialState
    let mainLabelCode := @finCode tm.Λ tm.ΛFin (Classical.decEq tm.Λ) tm.main
    let growth := FinTM2.nativeBitGrowth tm inputStack outputStack separatorIn zeroIn oneIn
      separatorOut zeroOut oneOut initialStateCode mainLabelCode
    let costBound :=
      (encodeInputLoopCost x + 19 * Lax51.BinaryWordEncoding.bitSize x + 18) +
      (initializeTablesCost (FinTM2.compileDispatcher tm 0).tables +
        (1 + Cond.size (.lt (.lit 0) (.var labelVar)) +
          maxCost (FinTM2.compileDispatcher tm 0).com) * bound +
        (1 + Cond.size (.lt (.lit 0) (.var labelVar)))) +
      (29 * Lax51.BinaryWordEncoding.bitSize y + 19) + 1
    ∃ ext σ' cost,
      BigStepB (2 ^ (Lax51.BinaryWordEncoding.bitSize x + 1 + costBound * growth))
        (FinTM2.compileNativeMachine tm inputStack outputStack separatorIn zeroIn oneIn
          separatorOut zeroOut oneOut initialStateCode mainLabelCode)
        (initEnv ext (x.length :: x)) σ' cost ∧
      cost ≤ costBound ∧ σ'.out = y := by
  dsimp only
  obtain ⟨ext, σ', cost, hbig, hcost, hout⟩ :=
    FinTM2.compileNativeMachine_outputsInTime tm inputAlphabet outputAlphabet x y bound hrun
  let growth := FinTM2.nativeBitGrowth tm
    (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₀)
    (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₁)
    (FinTM2.inputSymbolCode tm inputAlphabet .separator)
    (FinTM2.inputSymbolCode tm inputAlphabet .zero)
    (FinTM2.inputSymbolCode tm inputAlphabet .one)
    (FinTM2.outputSymbolCode tm outputAlphabet .separator)
    (FinTM2.outputSymbolCode tm outputAlphabet .zero)
    (FinTM2.outputSymbolCode tm outputAlphabet .one)
    (@finCode tm.σ tm.σFin (Classical.decEq tm.σ) tm.initialState)
    (@finCode tm.Λ tm.ΛFin (Classical.decEq tm.Λ) tm.main)
  have hgrowth := FinTM2.compileNativeMachine_bitGrowth tm
    (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₀)
    (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₁)
    (FinTM2.inputSymbolCode tm inputAlphabet .separator)
    (FinTM2.inputSymbolCode tm inputAlphabet .zero)
    (FinTM2.inputSymbolCode tm inputAlphabet .one)
    (FinTM2.outputSymbolCode tm outputAlphabet .separator)
    (FinTM2.outputSymbolCode tm outputAlphabet .zero)
    (FinTM2.outputSymbolCode tm outputAlphabet .one)
    (@finCode tm.σ tm.σFin (Classical.decEq tm.σ) tm.initialState)
    (@finCode tm.Λ tm.ΛFin (Classical.decEq tm.Λ) tm.main)
  obtain ⟨hbounded, _⟩ := bigStepBigStepBOfBitGrowth hbig
    (initEnv_bitBounded ext x) hgrowth le_rfl
  refine ⟨ext, σ', cost, ?_, hcost, hout⟩
  refine bigStepBMono ?_ hbounded
  apply pow_mono_exponent
  apply Nat.add_le_add_left
  exact Nat.mul_le_mul_right growth hcost

/-- End-to-end low-level RAM execution of the compiled Turing interpreter.
The sufficient word length is the explicit value exponent plus a fixed
layout constant, and the RAM time is the IMP cost times a fixed compiler
constant. -/
theorem FinTM2.compiledRam_outputsInTime (tm : Turing.FinTM2)
    (inputAlphabet : tm.Γ tm.k₀ ≃ Lax51.BinaryWordEncoding.Symbol)
    (outputAlphabet : tm.Γ tm.k₁ ≃ Lax51.BinaryWordEncoding.Symbol)
    (x y : List ℕ) (bound w : ℕ)
    (hrun : Turing.TM2OutputsInTime tm
      (List.map inputAlphabet.invFun (Lax51.BinaryWordEncoding.encode x))
      (some (List.map outputAlphabet.invFun
        (Lax51.BinaryWordEncoding.encode y))) bound) :
    let inputStack := @finCode tm.K tm.kFin tm.kDecidableEq tm.k₀
    let outputStack := @finCode tm.K tm.kFin tm.kDecidableEq tm.k₁
    let separatorIn := FinTM2.inputSymbolCode tm inputAlphabet .separator
    let zeroIn := FinTM2.inputSymbolCode tm inputAlphabet .zero
    let oneIn := FinTM2.inputSymbolCode tm inputAlphabet .one
    let separatorOut := FinTM2.outputSymbolCode tm outputAlphabet .separator
    let zeroOut := FinTM2.outputSymbolCode tm outputAlphabet .zero
    let oneOut := FinTM2.outputSymbolCode tm outputAlphabet .one
    let initialStateCode := @finCode tm.σ tm.σFin (Classical.decEq tm.σ) tm.initialState
    let mainLabelCode := @finCode tm.Λ tm.ΛFin (Classical.decEq tm.Λ) tm.main
    let cmd := FinTM2.compileNativeMachine tm inputStack outputStack separatorIn zeroIn oneIn
      separatorOut zeroOut oneOut initialStateCode mainLabelCode
    let layout := comCanonicalLayout cmd
    let growth := FinTM2.nativeBitGrowth tm inputStack outputStack separatorIn zeroIn oneIn
      separatorOut zeroOut oneOut initialStateCode mainLabelCode
    let costBound :=
      (encodeInputLoopCost x + 19 * Lax51.BinaryWordEncoding.bitSize x + 18) +
      (initializeTablesCost (FinTM2.compileDispatcher tm 0).tables +
        (1 + Cond.size (.lt (.lit 0) (.var labelVar)) +
          maxCost (FinTM2.compileDispatcher tm 0).com) * bound +
        (1 + Cond.size (.lt (.lit 0) (.var labelVar)))) +
      (29 * Lax51.BinaryWordEncoding.bitSize y + 19) + 1
    let exponent := Lax51.BinaryWordEncoding.bitSize x + 1 + costBound * growth
    exponent + layoutBitOverhead layout ≤ w →
      ∃ t ≤ layout.const * costBound,
        RunsTo w (compileProgram layout cmd) (x.length :: x) y t := by
  dsimp only
  intro hw
  obtain ⟨ext, σ', cost, hbs, hcost, hout⟩ :=
    FinTM2.compileNativeMachine_outputsInTime_bounded tm inputAlphabet outputAlphabet
      x y bound hrun
  let cmd := FinTM2.compileNativeMachine tm
    (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₀)
    (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₁)
    (FinTM2.inputSymbolCode tm inputAlphabet .separator)
    (FinTM2.inputSymbolCode tm inputAlphabet .zero)
    (FinTM2.inputSymbolCode tm inputAlphabet .one)
    (FinTM2.outputSymbolCode tm outputAlphabet .separator)
    (FinTM2.outputSymbolCode tm outputAlphabet .zero)
    (FinTM2.outputSymbolCode tm outputAlphabet .one)
    (@finCode tm.σ tm.σFin (Classical.decEq tm.σ) tm.initialState)
    (@finCode tm.Λ tm.ΛFin (Classical.decEq tm.Λ) tm.main)
  let layout := comCanonicalLayout cmd
  let growth := FinTM2.nativeBitGrowth tm
    (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₀)
    (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₁)
    (FinTM2.inputSymbolCode tm inputAlphabet .separator)
    (FinTM2.inputSymbolCode tm inputAlphabet .zero)
    (FinTM2.inputSymbolCode tm inputAlphabet .one)
    (FinTM2.outputSymbolCode tm outputAlphabet .separator)
    (FinTM2.outputSymbolCode tm outputAlphabet .zero)
    (FinTM2.outputSymbolCode tm outputAlphabet .one)
    (@finCode tm.σ tm.σFin (Classical.decEq tm.σ) tm.initialState)
    (@finCode tm.Λ tm.ΛFin (Classical.decEq tm.Λ) tm.main)
  let exponent := Lax51.BinaryWordEncoding.bitSize x + 1 +
    ((encodeInputLoopCost x + 19 * Lax51.BinaryWordEncoding.bitSize x + 18) +
      (initializeTablesCost (FinTM2.compileDispatcher tm 0).tables +
        (1 + Cond.size (.lt (.lit 0) (.var labelVar)) +
          maxCost (FinTM2.compileDispatcher tm 0).com) * bound +
        (1 + Cond.size (.lt (.lit 0) (.var labelVar)))) +
      (29 * Lax51.BinaryWordEncoding.bitSize y + 19) + 1) * growth
  have hfit : layout.FitsWords (2 ^ exponent) w :=
    layoutFitsWordsTwoPow layout (by dsimp [exponent]; omega) hw
  have hx : ∀ v ∈ x.length :: x, v < 2 ^ exponent := by
    intro v hv
    have hsmall := (initEnv_bitBounded ext x).inp v hv
    exact hsmall.trans_le (pow_mono_exponent (by dsimp [exponent]; omega))
  obtain ⟨t, ht, htRun⟩ := compileProgram_runsTo hfit
    (by simpa [layout] using comCanonicalLayoutOk cmd) hx hbs
  refine ⟨t, ht.trans ?_, ?_⟩
  · exact Nat.mul_le_mul_left layout.const hcost
  · simpa [cmd, layout, hout] using htRun

end Lax51Proofs.TMToRam
