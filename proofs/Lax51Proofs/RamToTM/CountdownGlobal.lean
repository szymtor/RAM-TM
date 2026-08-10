import Lax51Proofs.RamToTM.MultiExitPhase
import Lax51Proofs.RamToTM.FullInterpreterState

namespace Lax51Proofs.RamToTM

open Turing TM2

def sparseCountdownProgram : CountdownLabel ->
    TM2.Stmt (fun _ : CountdownStack => SparseSymbol)
      CountdownLabel CountdownControl :=
  mapAlphabetProgram sparseBitEncode sparseBitDecode countdownMachine.m

def sparseCountdownCfg (label : CountdownLabel) (state : CountdownControl)
    (count temp : List Bool) :
    TM2.Cfg (fun _ : CountdownStack => SparseSymbol)
      CountdownLabel CountdownControl :=
  mapAlphabetCfg sparseBitEncode (countdownCfg label state count temp)

theorem sparseCountdown_zero_correct (w : Nat) :
    ((fun x => x.bind (TM2.step sparseCountdownProgram))^[w + 1])
      (some (sparseCountdownCfg .scan default (fixedBits w 0) [])) =
    some (sparseCountdownCfg .zero
      { held := none, borrow := true, positiveSeen := false }
      [] (List.replicate w true)) := by
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode countdownMachine.m
    (countdownMachine_zero_correct w)

theorem sparseCountdown_positive_correct (w d : Nat)
    (hd0 : 0 < d) (hd : d < 2 ^ w) :
    ∃ finalState,
      ((fun x => x.bind (TM2.step sparseCountdownProgram))^[2 * w + 2])
        (some (sparseCountdownCfg .scan default (fixedBits w d) [])) =
      some (sparseCountdownCfg .positive finalState
        (fixedBits w (d - 1)) []) := by
  rcases countdownMachine_positive_correct w d hd0 hd with
    ⟨finalState, hrun⟩
  refine ⟨finalState, ?_⟩
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode countdownMachine.m hrun

def countdownCoreEncode : CountdownStack -> CoreStack
  | .count => .work3
  | .temp => .work4

def countdownCoreDecode : CoreStack -> Option CountdownStack
  | .work3 => some .count
  | .work4 => some .temp
  | _ => none

def countdownCoreRenaming : StackRenaming CountdownStack CoreStack where
  encode := countdownCoreEncode
  decode := countdownCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;>
      simp [countdownCoreDecode, countdownCoreEncode] at h ⊢

def countdownExit {R : Type} (zeroLabel positiveLabel : R) :
    CountdownLabel -> Option R
  | .zero => some zeroLabel
  | .positive => some positiveLabel
  | .scan | .restore => none

def countdownOnExit {N : Nat} (_ : CountdownLabel)
    (state : FullInterpreterState N) : FullInterpreterState N := state

def countdownMultiLeft {N : Nat} {R : Type}
    (zeroLabel positiveLabel : R) :
    CountdownLabel -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (Sum CountdownLabel R)
      (FullInterpreterState N) :=
  lensMultiPhaseLeft countdownCoreRenaming FullInterpreterState.countdownLens
    sparseCountdownProgram (countdownExit zeroLabel positiveLabel)
    countdownOnExit

theorem countdownExit_halt {R : Type} (zeroLabel positiveLabel : R)
    (label : CountdownLabel)
    (h : (countdownExit zeroLabel positiveLabel label).isSome) :
    sparseCountdownProgram label = .halt := by
  cases label <;> simp [countdownExit] at h ⊢ <;> rfl

theorem globalCountdown_zero_correct {N : Nat} {R : Type}
    (zeroLabel positiveLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w : Nat) (state : FullInterpreterState N)
    (base : CoreStack -> List SparseSymbol) :
    ((fun x => x.bind (TM2.step
      (liftRightProgram (countdownMultiLeft zeroLabel positiveLabel) right)))^[
        w + 2])
      (some (lensRenamedCfg countdownCoreRenaming
        FullInterpreterState.countdownLens
        (sparseCountdownCfg .scan default (fixedBits w 0) [])
        state base)) =
    some (mapLabelCfg Sum.inr
      (multiPhaseReturnCfg countdownCoreRenaming
        FullInterpreterState.countdownLens zeroLabel id
        (sparseCountdownCfg .zero
          { held := none, borrow := true, positiveSeen := false }
          [] (List.replicate w true)) state base)) := by
  have h := run_lensMultiPhase_to_right countdownCoreRenaming
    FullInterpreterState.countdownLens sparseCountdownProgram
    (countdownExit zeroLabel positiveLabel) countdownOnExit
    (countdownExit_halt zeroLabel positiveLabel) right
    (sparseCountdown_zero_correct w) rfl (by rfl) state base
  simpa [countdownMultiLeft, countdownOnExit] using h

theorem globalCountdown_positive_correct {N : Nat} {R : Type}
    (zeroLabel positiveLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w d : Nat) (hd0 : 0 < d) (hd : d < 2 ^ w)
    (state : FullInterpreterState N)
    (base : CoreStack -> List SparseSymbol) :
    ∃ localFinal,
      ((fun x => x.bind (TM2.step
        (liftRightProgram (countdownMultiLeft zeroLabel positiveLabel) right)))^[
          2 * w + 3])
        (some (lensRenamedCfg countdownCoreRenaming
          FullInterpreterState.countdownLens
          (sparseCountdownCfg .scan default (fixedBits w d) [])
          state base)) =
      some (mapLabelCfg Sum.inr
        (multiPhaseReturnCfg countdownCoreRenaming
          FullInterpreterState.countdownLens positiveLabel id
          (sparseCountdownCfg .positive localFinal
            (fixedBits w (d - 1)) []) state base)) := by
  rcases sparseCountdown_positive_correct w d hd0 hd with
    ⟨localFinal, hrun⟩
  refine ⟨localFinal, ?_⟩
  have h := run_lensMultiPhase_to_right countdownCoreRenaming
    FullInterpreterState.countdownLens sparseCountdownProgram
    (countdownExit zeroLabel positiveLabel) countdownOnExit
    (countdownExit_halt zeroLabel positiveLabel) right hrun rfl (by rfl)
    state base
  simpa [countdownMultiLeft, countdownOnExit] using h

end Lax51Proofs.RamToTM
