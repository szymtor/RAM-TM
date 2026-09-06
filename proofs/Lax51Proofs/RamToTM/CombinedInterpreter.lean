import Lax51Proofs.RamToTM.FullInputPreprocessor
import Lax51Proofs.RamToTM.OutputAdapter
import Lax51Proofs.RamToTM.StackGrowthBounds

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax51Proofs.Microcode
open Lax51.BinaryWordEncoding Lax51.RamPolytime

noncomputable section

abbrev MiddleLabel (p : Program) (N : Nat) :=
  Sum (FiniteInterpreterLabel p N) OutputAdapterLabel

def middleProgram (p : Program) (N : Nat)
    (hbound : programArgumentBound p <= N) : MiddleLabel p N →
    TM2.Stmt WrapperAlphabet (MiddleLabel p N) (WrapperState N)
  | .inl (.control .stopped) => .goto fun _ => .inr .initialize
  | .inl label => liftCoreStmt (finiteInterpreterProgram p N hbound label)
  | .inr label => outputAdapterProgram label

abbrev CombinedLabel (p : Program) (N : Nat)
    (wordBound : Polynomial Nat) :=
  Sum (FullInputLabel wordBound) (MiddleLabel p N)

def combinedProgram (p : Program) (N : Nat)
    (hbound : programArgumentBound p <= N) (wordBound : Polynomial Nat) :
    CombinedLabel p N wordBound →
      TM2.Stmt WrapperAlphabet (CombinedLabel p N wordBound) (WrapperState N)
  | .inl (.inr (.inr (.inr (.inr (.inr (.inr terminal)))))) =>
      .goto fun _ => .inr (.inl (.fetch (boundPC p 0)))
  | .inl label => mapLabelStmt Sum.inl (fullInputProgram wordBound label)
  | .inr label => mapLabelStmt Sum.inr (middleProgram p N hbound label)

def embedInputCombined {p : Program} {N : Nat} {wordBound : Polynomial Nat} :
    FullInputLabel wordBound → CombinedLabel p N wordBound := Sum.inl

def embedMiddleCombined {p : Program} {N : Nat} {wordBound : Polynomial Nat} :
    MiddleLabel p N → CombinedLabel p N wordBound := Sum.inr

def embedCoreMiddle {p : Program} {N : Nat} :
    FiniteInterpreterLabel p N → MiddleLabel p N := Sum.inl

def embedOutputMiddle {p : Program} {N : Nat} :
    Sum Empty OutputAdapterLabel → MiddleLabel p N
  | .inl impossible => nomatch impossible
  | .inr label => .inr label

abbrev fullInputTerminal {wordBound : Polynomial Nat} :
    FullInputLabel wordBound :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))))

theorem combined_lift_input {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (wordBound : Polynomial Nat)
    {steps : Nat}
    {c d : TM2.Cfg WrapperAlphabet (FullInputLabel wordBound) (WrapperState N)}
    (hrun : ((fun o => o.bind (TM2.step (fullInputProgram wordBound)))^[steps])
      (some c) = some d) (hd : d.l.isSome) :
    ((fun o => o.bind (TM2.step (combinedProgram p N hbound wordBound)))^[steps])
      (some (mapLabelCfg embedInputCombined c)) =
    some (mapLabelCfg embedInputCombined d) := by
  apply iterate_mapLabelProgram_until_exit
    (fullInputProgram wordBound) (combinedProgram p N hbound wordBound)
    embedInputCombined ?_ hrun hd
  intro label hnonhalt
  rcases label with width | rest
  · simp [combinedProgram, embedInputCombined, fullInputProgram, mapLabelStmt]
  · rcases rest with length | rest
    · simp [combinedProgram, embedInputCombined, fullInputProgram, mapLabelStmt]
    · rcases rest with raw | rest
      · simp [combinedProgram, embedInputCombined, fullInputProgram, mapLabelStmt]
      · rcases rest with padding | rest
        · simp [combinedProgram, embedInputCombined, fullInputProgram, mapLabelStmt]
        · rcases rest with finalize | rest
          · simp [combinedProgram, embedInputCombined, fullInputProgram, mapLabelStmt]
          · rcases rest with core | unit
            · cases core <;>
                simp [combinedProgram, embedInputCombined, fullInputProgram,
                  mapLabelStmt] at hnonhalt ⊢
            · cases unit
              simp [fullInputProgram] at hnonhalt

theorem middle_lift_core {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) {steps : Nat}
    {c d : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (FiniteInterpreterLabel p N) (FullInterpreterState N)}
    (ambient : WrapperState N) (externalInput externalOutput : List Symbol)
    (hrun : ((fun o => o.bind
      (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
      (some c) = some d) (hd : d.l.isSome) :
    ((fun o => o.bind (TM2.step (middleProgram p N hbound)))^[steps])
      (some (liftCoreCfg (X := OutputAdapterLabel) c ambient
        externalInput externalOutput)) =
    some (liftCoreCfg (X := OutputAdapterLabel) d ambient
      externalInput externalOutput) := by
  let lifted := liftCoreProgram (finiteInterpreterProgram p N hbound)
    (outputAdapterProgram (N := N) (L := FiniteInterpreterLabel p N))
  have hlift := iterate_liftCoreProgram
    (finiteInterpreterProgram p N hbound)
    (outputAdapterProgram (N := N) (L := FiniteInterpreterLabel p N))
    c d ambient externalInput externalOutput hrun
  have hmapped := iterate_mapLabelProgram_until_exit lifted
    (middleProgram p N hbound) id (by
      intro label hnonhalt
      cases label with
      | inl label =>
          cases label <;>
            simp [lifted, liftCoreProgram, middleProgram] at hnonhalt ⊢ <;>
            (rename_i control; cases control <;>
              simp [lifted, liftCoreProgram, middleProgram,
                finiteInterpreterProgram, finiteControlStmt,
                controlDispatchMachine, lensRenameStmt, liftCoreStmt,
                mapLabelStmt] at hnonhalt ⊢)
      | inr label => simp [lifted, liftCoreProgram, middleProgram]) hlift (by
        simpa [liftCoreCfg] using hd)
  simpa using hmapped

theorem middle_lift_output {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (steps : Nat)
    (c : TM2.Cfg WrapperAlphabet (Sum Empty OutputAdapterLabel)
      (WrapperState N)) :
    ((fun o => o.bind (TM2.step (middleProgram p N hbound)))^[steps])
        (some (mapLabelCfg embedOutputMiddle c)) =
      (((fun o => o.bind (TM2.step
        (liftCoreProgram (fun _ : Empty => .halt)
          (outputAdapterProgram (N := N) (L := Empty)))))^[steps])
          (some c)).map (mapLabelCfg embedOutputMiddle) := by
  apply iterate_mapLabelProgram
  intro label
  rcases label with impossible | output
  · exact nomatch impossible
  · cases output <;> simp [middleProgram, embedOutputMiddle, liftCoreProgram,
      outputAdapterProgram, mapLabelStmt_comp, Function.comp_def,
      mapLabelStmt] <;> try (congr 1 <;> funext x <;> rfl)
    split <;> simp_all [mapLabelStmt] <;> congr 1 <;> funext x <;> rfl

theorem combined_lift_middle {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (wordBound : Polynomial Nat)
    (steps : Nat)
    (c : TM2.Cfg WrapperAlphabet (MiddleLabel p N) (WrapperState N)) :
    ((fun o => o.bind
      (TM2.step (combinedProgram p N hbound wordBound)))^[steps])
        (some (mapLabelCfg embedMiddleCombined c)) =
      (((fun o => o.bind (TM2.step (middleProgram p N hbound)))^[steps])
          (some c)).map (mapLabelCfg embedMiddleCombined) := by
  apply iterate_mapLabelProgram
  intro label
  simp [combinedProgram, embedMiddleCombined]

theorem combined_input_bridge {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (wordBound : Polynomial Nat)
    (state : WrapperState N)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    TM2.step (combinedProgram p N hbound wordBound)
      (mapLabelCfg embedInputCombined
        (fullInputCfg
          fullInputTerminal state tapes)) =
    some ⟨some (.inr (.inl (.fetch (boundPC p 0)))), state, tapes⟩ := by
  rfl

theorem combined_input_finish {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (wordBound : Polynomial Nat)
    (state : WrapperState N)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    ((fun o : Option (TM2.Cfg WrapperAlphabet (CombinedLabel p N wordBound)
      (WrapperState N)) => o.bind (TM2.step
        (combinedProgram p N hbound wordBound)))^[1])
      (some (mapLabelCfg embedInputCombined
        (fullInputCfg
          (.inr (.inr (.inr (.inr (.inr (.inl .done)))))) state tapes))) =
    some (mapLabelCfg embedInputCombined
      (fullInputCfg fullInputTerminal state tapes)) := by
  rfl

theorem middle_stopped_bridge {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N)
    (state : WrapperState N)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    TM2.step (middleProgram p N hbound)
      ⟨some (.inl (.control .stopped)), state, tapes⟩ =
    some ⟨some (.inr .initialize), state, tapes⟩ := by
  simp [middleProgram, TM2.step]

set_option maxHeartbeats 2000000 in
theorem middle_ram_to_output {p : Program} {w t : Nat}
    (hw : 0 < w) {input output : List Nat}
    (hram : RunsTo w p input output t) :
    ∃ ss coreSteps stopSteps finalState finalTapes,
      ss.out = output ∧ sparseStep w p ss = none ∧
      ss.mem.Normalized w ∧ ss.mem.length ≤ t ∧ ss.out.length ≤ t ∧
      coreSteps ≤ t * finiteRunUnitBound w 0 t ∧
      stopSteps ≤ operandEvalBound w ss.mem + 4 ∧
      finalTapes .output = (coreStacks w ss) .output ∧
      ((fun o => o.bind (TM2.step
        (middleProgram p (programArgumentBound p) le_rfl)))^[
          coreSteps + stopSteps + 1])
        (some (liftCoreCfg (X := OutputAdapterLabel)
          (finiteInterpreterCfg (.fetch (boundPC p 0)) default
            (coreStacks w (sparseInitState input))) default [] [])) =
      some ⟨some (.inr .initialize),
        WrapperState.coreLens.put default finalState,
        wrapperCoreStacks finalTapes [] []⟩ := by
  rcases ramRunsTo_coreSimulation hw hram with
    ⟨ss, coreSteps, hout, hstop, hm, hmem, houtLength, hcoreBound,
      coreState, hdispatch, hcore⟩
  rcases finite_sparseHalt_to_stopped le_rfl ss hm hstop coreState with
    ⟨stopSteps, hstopBound, finalState, finalTapes, houtTapes, hterminal⟩
  have hcoreLift := middle_lift_core le_rfl default [] [] hcore rfl
  have hterminalLift := middle_lift_core le_rfl default [] [] hterminal rfl
  have hbeforeBridge := chain_iterations
    (fun o : Option (TM2.Cfg WrapperAlphabet
      (MiddleLabel p (programArgumentBound p))
      (WrapperState (programArgumentBound p))) =>
      o.bind (TM2.step (middleProgram p (programArgumentBound p) le_rfl)))
    hcoreLift hterminalLift
  have hbridgeStep := middle_stopped_bridge (p := p) le_rfl
    (WrapperState.coreLens.put default finalState)
    (wrapperCoreStacks finalTapes [] [])
  have hbridge : ((fun o : Option (TM2.Cfg WrapperAlphabet
      (MiddleLabel p (programArgumentBound p))
      (WrapperState (programArgumentBound p))) =>
      o.bind (TM2.step (middleProgram p (programArgumentBound p) le_rfl)))^[1])
      (some (liftCoreCfg (X := OutputAdapterLabel)
        (finiteInterpreterCfg (.control .stopped) finalState finalTapes)
        default [] [])) =
      some ⟨some (.inr .initialize),
        WrapperState.coreLens.put default finalState,
        wrapperCoreStacks finalTapes [] []⟩ := by
    simpa [liftCoreCfg, finiteInterpreterCfg, mapLabelCfg] using hbridgeStep
  have hall := chain_iterations _ hbeforeBridge hbridge
  refine ⟨ss, coreSteps, stopSteps, finalState, finalTapes,
    hout, hstop, hm, hmem, houtLength,
    hcoreBound, hstopBound, houtTapes, ?_⟩
  simpa [liftCoreCfg, finiteInterpreterCfg, mapLabelCfg,
    WrapperState.coreLens, Nat.add_assoc] using hall

theorem middle_output_complete {p : Program} {N w : Nat}
    (hbound : programArgumentBound p <= N) (state : WrapperState N)
    (tapes : CoreStack → List SparseSymbol) (output : List Nat)
    (hout : tapes .output = encodeOutputStack w output)
    (hfit : ∀ n ∈ output, n < 2 ^ w) :
    let base := wrapperCoreStacks tapes [] []
    let decoded := outputAdapterStacks [] (encode output) base
    let steps := 4 + output.length * (3 * w + 3) +
      (cleanupTotalCost decoded + 1)
    ((fun o => o.bind (TM2.step (middleProgram p N hbound)))^[steps])
      (some ⟨some (.inr .initialize), state, base⟩) =
    some ⟨none, default, cleanedStacks decoded⟩ := by
  dsimp only
  let base := wrapperCoreStacks tapes [] []
  have hbase : outputAdapterStacks (encodeOutputStack w output) [] base = base := by
    funext k
    cases k with
    | input => simp [outputAdapterStacks, base, wrapperCoreStacks]
    | output => simp [outputAdapterStacks, base, wrapperCoreStacks]
    | core k =>
        cases k <;> simp [outputAdapterStacks, base, wrapperCoreStacks, hout]
  rcases output_decode_run state output hfit base with
    ⟨decodedState, hdecode⟩
  rw [hbase] at hdecode
  let decoded := outputAdapterStacks [] (encode output) base
  have hcleanup := output_cleanup_run decodedState decoded
  have hdecodeLift := middle_lift_output (p := p) hbound
    (4 + output.length * (3 * w + 3))
    (outputAdapterCfg (L := Empty) .initialize state base)
  rw [hdecode] at hdecodeLift
  have hcleanupLift := middle_lift_output (p := p) hbound
    (cleanupTotalCost decoded + 1)
    (outputAdapterCfg (L := Empty) (.cleanupPeek .input) decodedState decoded)
  rw [hcleanup] at hcleanupLift
  have hall := chain_iterations
    (fun o : Option (TM2.Cfg WrapperAlphabet (MiddleLabel p N)
      (WrapperState N)) => o.bind (TM2.step (middleProgram p N hbound)))
    hdecodeLift hcleanupLift
  simpa [outputAdapterCfg, embedOutputMiddle, mapLabelCfg, decoded,
    Nat.add_assoc] using hall

set_option maxHeartbeats 2000000 in
theorem middle_cleanupCost_le {p : Program} {N w steps : Nat}
    (hbound : programArgumentBound p <= N) (input : List Nat)
    (finalState : FullInterpreterState N)
    (finalTapes : CoreStack → List SparseSymbol)
    (hrun : ((fun o => o.bind (TM2.step (middleProgram p N hbound)))^[steps])
      (some (liftCoreCfg (X := OutputAdapterLabel)
        (finiteInterpreterCfg (.fetch (boundPC p 0)) default
          (coreStacks w (sparseInitState input))) default [] [])) =
      some ⟨some (.inr .initialize),
        WrapperState.coreLens.put default finalState,
        wrapperCoreStacks finalTapes [] []⟩)
    (output : List Nat) :
    cleanupTotalCost
        (outputAdapterStacks [] (encode output)
          (wrapperCoreStacks finalTapes [] [])) ≤
      2 * (13 * (coreSize w (sparseInitState input) +
        steps * programPushBound (middleProgram p N hbound))) + 13 := by
  let startCfg : TM2.Cfg WrapperAlphabet (MiddleLabel p N) (WrapperState N) :=
    liftCoreCfg (X := OutputAdapterLabel)
    (finiteInterpreterCfg (.fetch (boundPC p 0)) default
      (coreStacks w (sparseInitState input))) default [] []
  let finalCfg : TM2.Cfg WrapperAlphabet (MiddleLabel p N) (WrapperState N) :=
    ⟨some (.inr .initialize), WrapperState.coreLens.put default finalState,
      wrapperCoreStacks finalTapes [] []⟩
  have hb (k : CoreStack) := iterate_stack_length_le
    (middleProgram p N hbound) steps startCfg finalCfg hrun (.core k)
  have hinitial (k : CoreStack) :
      (startCfg.stk (.core k)).length ≤ coreSize w (sparseInitState input) := by
    dsimp only [startCfg, liftCoreCfg, finiteInterpreterCfg,
      wrapperCoreStacks, coreSize]
    cases k with
    | accumulator =>
        exact Nat.le_add_right_of_le (Nat.le_add_right_of_le
          (Nat.le_add_right _ _))
    | memory =>
        exact Nat.le_add_right_of_le (Nat.le_add_right_of_le
          (Nat.le_add_left _ _))
    | input =>
        exact Nat.le_add_right_of_le (Nat.le_add_left _ _)
    | output => exact Nat.le_add_left _ _
    | work0 | work1 | work2 | work3 | work4 | work5 | work6 | work7 =>
        exact Nat.zero_le _
  have hfinal (k : CoreStack) : (finalTapes k).length ≤
      coreSize w (sparseInitState input) +
        steps * programPushBound (middleProgram p N hbound) := by
    have hk := hb k
    dsimp [startCfg, finalCfg, liftCoreCfg, finiteInterpreterCfg,
      wrapperCoreStacks] at hk
    apply hk.trans
    exact Nat.add_le_add_right (hinitial k) _
  have hacc := hfinal .accumulator
  have hmem := hfinal .memory
  have hinp := hfinal .input
  have hw0 := hfinal .work0
  have hw1 := hfinal .work1
  have hw2 := hfinal .work2
  have hw3 := hfinal .work3
  have hw4 := hfinal .work4
  have hw5 := hfinal .work5
  have hw6 := hfinal .work6
  have hw7 := hfinal .work7
  let actualCost := cleanupTotalCost
    (outputAdapterStacks [] (encode output)
      (wrapperCoreStacks finalTapes [] []))
  have hcost : cleanupTotalCost
      (outputAdapterStacks [] (encode output)
        (wrapperCoreStacks finalTapes [] [])) = actualCost := by
    rfl
  rw [hcost]
  let decodedTapes := outputAdapterStacks [] (encode output)
    (wrapperCoreStacks finalTapes [] [])
  let bound := coreSize w (sparseInitState input) +
    steps * programPushBound (middleProgram p N hbound)
  have hdecodedInput : (decodedTapes .input).length ≤ bound := by
    dsimp [decodedTapes, outputAdapterStacks, wrapperCoreStacks]
    exact Nat.zero_le _
  have hdecodedCore (k : CoreStack) : (decodedTapes (.core k)).length ≤ bound := by
    cases k with
    | accumulator => simpa [decodedTapes, outputAdapterStacks, wrapperCoreStacks, bound] using hacc
    | memory => simpa [decodedTapes, outputAdapterStacks, wrapperCoreStacks, bound] using hmem
    | input => simpa [decodedTapes, outputAdapterStacks, wrapperCoreStacks, bound] using hinp
    | output =>
        dsimp [decodedTapes, outputAdapterStacks, wrapperCoreStacks]
        exact Nat.zero_le _
    | work0 => simpa [decodedTapes, outputAdapterStacks, wrapperCoreStacks, bound] using hw0
    | work1 => simpa [decodedTapes, outputAdapterStacks, wrapperCoreStacks, bound] using hw1
    | work2 => simpa [decodedTapes, outputAdapterStacks, wrapperCoreStacks, bound] using hw2
    | work3 => simpa [decodedTapes, outputAdapterStacks, wrapperCoreStacks, bound] using hw3
    | work4 => simpa [decodedTapes, outputAdapterStacks, wrapperCoreStacks, bound] using hw4
    | work5 => simpa [decodedTapes, outputAdapterStacks, wrapperCoreStacks, bound] using hw5
    | work6 => simpa [decodedTapes, outputAdapterStacks, wrapperCoreStacks, bound] using hw6
    | work7 => simpa [decodedTapes, outputAdapterStacks, wrapperCoreStacks, bound] using hw7
  dsimp only [actualCost]
  change 2 * (decodedTapes .input).length + 1 +
    2 * (decodedTapes (.core .accumulator)).length + 1 +
    2 * (decodedTapes (.core .memory)).length + 1 +
    2 * (decodedTapes (.core .input)).length + 1 +
    2 * (decodedTapes (.core .output)).length + 1 +
    2 * (decodedTapes (.core .work0)).length + 1 +
    2 * (decodedTapes (.core .work1)).length + 1 +
    2 * (decodedTapes (.core .work2)).length + 1 +
    2 * (decodedTapes (.core .work3)).length + 1 +
    2 * (decodedTapes (.core .work4)).length + 1 +
    2 * (decodedTapes (.core .work5)).length + 1 +
    2 * (decodedTapes (.core .work6)).length + 1 +
    2 * (decodedTapes (.core .work7)).length + 1 ≤
      2 * (13 * bound) + 13
  have ha := hdecodedCore .accumulator
  have hm := hdecodedCore .memory
  have hi := hdecodedCore .input
  have ho := hdecodedCore .output
  have h0 := hdecodedCore .work0
  have h1 := hdecodedCore .work1
  have h2 := hdecodedCore .work2
  have h3 := hdecodedCore .work3
  have h4 := hdecodedCore .work4
  have h5 := hdecodedCore .work5
  have h6 := hdecodedCore .work6
  have h7 := hdecodedCore .work7
  omega

set_option maxHeartbeats 3000000 in
theorem combined_runsTo_complete (p : Program) (wordBound : Polynomial Nat)
    (x output : List Nat) (t : Nat)
    (hfits : Lax51.RamPolytime.FitsInWords
      (wordBound.eval (bitSize x)) ((x.length :: x) ++ output))
    (hram : RunsTo (simulationWordWidth wordBound x) p
      (x.length :: x) output t) :
    ∃ ss : SparseState, ∃ coreSteps stopSteps : Nat,
      ∃ finalState : FullInterpreterState (programArgumentBound p),
      ∃ finalTapes : CoreStack → List SparseSymbol,
      let w := simulationWordWidth wordBound x
      let base := wrapperCoreStacks finalTapes [] []
      let decoded := outputAdapterStacks [] (encode output) base
      let totalSteps := fullInputCost wordBound x + 2 +
        (coreSteps + stopSteps + 1) +
        (4 + output.length * (3 * w + 3) +
          (cleanupTotalCost decoded + 1))
      ss.mem.length ≤ t ∧ output.length ≤ t ∧
      coreSteps ≤ t * finiteRunUnitBound w 0 t ∧
      stopSteps ≤ operandEvalBound w ss.mem + 4 ∧
      cleanupTotalCost decoded ≤
        2 * (13 * (coreSize w (sparseInitState (x.length :: x)) +
          (coreSteps + stopSteps + 1) *
            programPushBound (middleProgram p (programArgumentBound p) le_rfl))) + 13 ∧
      ((fun o => o.bind (TM2.step
        (combinedProgram p (programArgumentBound p) le_rfl wordBound)))^[
          totalSteps])
        (some (mapLabelCfg embedInputCombined
          (fullInputCfg (.inl (.inl .scan))
            (default : WrapperState (programArgumentBound p))
            (inputWidthInitialStacks (encode x))))) =
      some ⟨none, default, cleanedStacks decoded⟩ := by
  let w := simulationWordWidth wordBound x
  have hw : 0 < w := by simp [w, simulationWordWidth]
  have hwidth : wordBound.eval (bitSize x) ≤ w :=
    (polynomial_eval_le_simpleMajorant wordBound (bitSize x)).trans
      (by simp [w, simulationWordWidth])
  have hpow : 2 ^ wordBound.eval (bitSize x) ≤ 2 ^ w :=
    Nat.pow_le_pow_right (by omega) hwidth
  have hlen : x.length < 2 ^ w :=
    (hfits x.length (by simp)).trans_le hpow
  have hxfit : ∀ n ∈ x, n < 2 ^ w := by
    intro n hn
    exact (hfits n (by simp [hn])).trans_le hpow
  have houtfit : ∀ n ∈ output, n < 2 ^ w := by
    intro n hn
    exact (hfits n (by simp [hn])).trans_le hpow
  have hinput := fullInput_complete
    (N := programArgumentBound p) wordBound x default hlen hxfit
  have hinputLift := combined_lift_input (p := p) le_rfl wordBound
    hinput (by rfl)
  rw [fullInputCoreFinal_eq_canonical] at hinputLift
  have hinputFinish := combined_input_finish (p := p) le_rfl wordBound
    (default : WrapperState (programArgumentBound p))
    (wrapperCoreStacks
      (coreStacks w (sparseInitState (x.length :: x))) [] [])
  have hpreFinish := chain_iterations
    (fun o : Option (TM2.Cfg WrapperAlphabet
      (CombinedLabel p (programArgumentBound p) wordBound)
      (WrapperState (programArgumentBound p))) =>
      o.bind (TM2.step
        (combinedProgram p (programArgumentBound p) le_rfl wordBound)))
    hinputLift hinputFinish
  have hinputBridgeStep := combined_input_bridge (p := p) le_rfl wordBound
    (default : WrapperState (programArgumentBound p))
    (wrapperCoreStacks
      (coreStacks w (sparseInitState (x.length :: x))) [] [])
  have hinputBridge : ((fun o : Option (TM2.Cfg WrapperAlphabet
      (CombinedLabel p (programArgumentBound p) wordBound)
      (WrapperState (programArgumentBound p))) =>
      o.bind (TM2.step
        (combinedProgram p (programArgumentBound p) le_rfl wordBound)))^[1])
      (some (mapLabelCfg embedInputCombined
        (fullInputCfg
          fullInputTerminal default
          (wrapperCoreStacks
            (coreStacks w (sparseInitState (x.length :: x))) [] [])))) =
      some ⟨some (.inr (.inl (.fetch (boundPC p 0)))), default,
        wrapperCoreStacks
          (coreStacks w (sparseInitState (x.length :: x))) [] []⟩ := by
    simpa using hinputBridgeStep
  have hpre := chain_iterations _ hpreFinish hinputBridge
  rcases middle_ram_to_output hw hram with
    ⟨ss, coreSteps, stopSteps, finalState, finalTapes,
      hout, hstop, hm, hmem, houtLength,
      hcoreBound, hstopBound, houtTapes, hmiddle⟩
  have houtEncoded : finalTapes .output = encodeOutputStack w output := by
    rw [houtTapes]
    simp [coreStacks, hout]
  have houtput := middle_output_complete le_rfl
    (WrapperState.coreLens.put default finalState) finalTapes output
    houtEncoded houtfit
  have hcleanupBound := middle_cleanupCost_le le_rfl
    (x.length :: x) finalState finalTapes hmiddle output
  have hmiddleAll := chain_iterations
    (fun o : Option (TM2.Cfg WrapperAlphabet
      (MiddleLabel p (programArgumentBound p))
      (WrapperState (programArgumentBound p))) =>
      o.bind (TM2.step (middleProgram p (programArgumentBound p) le_rfl)))
    hmiddle houtput
  let middleStart : TM2.Cfg WrapperAlphabet
      (MiddleLabel p (programArgumentBound p))
      (WrapperState (programArgumentBound p)) :=
    liftCoreCfg (X := OutputAdapterLabel)
      (finiteInterpreterCfg (.fetch (boundPC p 0)) default
        (coreStacks w (sparseInitState (x.length :: x)))) default [] []
  have hmiddleLift := combined_lift_middle (p := p) le_rfl wordBound
    ((coreSteps + stopSteps + 1) +
      (4 + output.length * (3 * w + 3) +
        (cleanupTotalCost
          (outputAdapterStacks [] (encode output)
            (wrapperCoreStacks finalTapes [] [])) + 1))) middleStart
  rw [hmiddleAll] at hmiddleLift
  have hall := chain_iterations _ hpre hmiddleLift
  refine ⟨ss, coreSteps, stopSteps, finalState, finalTapes, ?_⟩
  dsimp only
  refine ⟨hmem, by simpa [hout] using houtLength,
    hcoreBound, hstopBound, hcleanupBound, ?_⟩
  simpa [w, middleStart, liftCoreCfg, finiteInterpreterCfg, mapLabelCfg,
    embedMiddleCombined, Nat.add_assoc] using hall

end

end Lax51Proofs.RamToTM
