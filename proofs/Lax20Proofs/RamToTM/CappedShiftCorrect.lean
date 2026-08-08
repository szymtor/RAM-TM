import Lax20Proofs.RamToTM.CappedShiftController

namespace Lax20Proofs.RamToTM

open Turing TM2

def cappedCountdownSource {N : Nat} (rightShift : Bool) :
    Sum CountdownLabel CappedShiftLabel -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol)
      (Sum CountdownLabel CappedShiftLabel) (FullInterpreterState N) :=
  liftRightProgram (countdownMultiLeft .cleanupFuel .fuel)
    (cappedShiftProgram rightShift)

theorem cappedCountdownSource_embeds {N : Nat} (rightShift : Bool)
    (label : Sum CountdownLabel CappedShiftLabel)
    (hn : cappedCountdownSource (N := N) rightShift label ≠ .halt) :
    cappedShiftProgram (N := N) rightShift
        (embedCountdownController label) =
      mapLabelStmt embedCountdownController
        (cappedCountdownSource (N := N) rightShift label) := by
  cases label with
  | inl label => rfl
  | inr label =>
      simp only [cappedCountdownSource, liftRightProgram]
      rw [mapLabelStmt_comp]
      change cappedShiftProgram (N := N) rightShift label =
        mapLabelStmt id (cappedShiftProgram (N := N) rightShift label)
      exact (mapLabelStmt_id _).symm

theorem cappedCountdown_zero_correct {N : Nat} (rightShift : Bool)
    (w : Nat) (state : FullInterpreterState N)
    (base : CoreStack -> List SparseSymbol) :
    ((fun x => x.bind (TM2.step (cappedShiftProgram rightShift)))^[w + 2])
      (some (mapLabelCfg embedCountdownController
        (lensRenamedCfg countdownCoreRenaming
          FullInterpreterState.countdownLens
          (sparseCountdownCfg .scan default (fixedBits w 0) [])
          state base))) =
    some (mapLabelCfg embedCountdownController
      (mapLabelCfg Sum.inr
        (multiPhaseReturnCfg countdownCoreRenaming
          FullInterpreterState.countdownLens CappedShiftLabel.cleanupFuel id
          (sparseCountdownCfg .zero
            { held := none, borrow := true, positiveSeen := false }
            [] (List.replicate w true)) state base))) := by
  have hrun := globalCountdown_zero_correct
    CappedShiftLabel.cleanupFuel CappedShiftLabel.fuel
    (cappedShiftProgram rightShift) w state base
  apply iterate_mapLabelProgram_until_exit
    (cappedCountdownSource rightShift) (cappedShiftProgram rightShift)
    embedCountdownController (cappedCountdownSource_embeds rightShift)
    hrun
  rfl

theorem cappedCountdown_positive_correct {N : Nat} (rightShift : Bool)
    (w d : Nat) (hd0 : 0 < d) (hd : d < 2 ^ w)
    (state : FullInterpreterState N)
    (base : CoreStack -> List SparseSymbol) :
    ∃ localFinal,
      ((fun x => x.bind (TM2.step (cappedShiftProgram rightShift)))^[
          2 * w + 3])
        (some (mapLabelCfg embedCountdownController
          (lensRenamedCfg countdownCoreRenaming
            FullInterpreterState.countdownLens
            (sparseCountdownCfg .scan default (fixedBits w d) [])
            state base))) =
      some (mapLabelCfg embedCountdownController
        (mapLabelCfg Sum.inr
          (multiPhaseReturnCfg countdownCoreRenaming
            FullInterpreterState.countdownLens CappedShiftLabel.fuel id
            (sparseCountdownCfg .positive localFinal
              (fixedBits w (d - 1)) []) state base))) := by
  rcases globalCountdown_positive_correct
      CappedShiftLabel.cleanupFuel CappedShiftLabel.fuel
      (cappedShiftProgram rightShift) w d hd0 hd state base with
    ⟨localFinal, hrun⟩
  refine ⟨localFinal, ?_⟩
  apply iterate_mapLabelProgram_until_exit
    (cappedCountdownSource rightShift) (cappedShiftProgram rightShift)
    embedCountdownController (cappedCountdownSource_embeds rightShift)
    hrun
  rfl

def embedLeftController : ShiftLeftRoundLabel Unit -> CappedShiftLabel :=
  CappedShiftLabel.left

theorem cappedLeftSource_embeds {N : Nat}
    (label : ShiftLeftRoundLabel Unit)
    (hn : shiftLeftRoundProgram (N := N) () (fun _ => .halt) label ≠ .halt) :
    cappedShiftProgram (N := N) false (embedLeftController label) =
      mapLabelStmt embedLeftController
        (shiftLeftRoundProgram () (fun _ => .halt) label) := by
  rcases label with label | tail
  · rfl
  rcases tail with label | tail
  · rfl
  rcases tail with label | tail
  · rfl
  cases tail
  exact False.elim (hn rfl)

theorem cappedLeftRound_correct {N : Nat}
    (w word count : Nat) (hw : 0 < w)
    (fuel : List SparseSymbol) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N)
    (hmove : FullInterpreterState.moveLens.get state = default) :
    ∃ finalState,
      ((fun x => x.bind (TM2.step (cappedShiftProgram false)))^[4 * w + 8])
        (some (mapLabelCfg embedLeftController
          (lensRenamedCfg shiftRoundRenaming FullInterpreterState.shiftLens
            (sparseShiftLeftLocalCfg .first (fixedBits w word) [] [])
            state (shiftRoundBase w word count fuel m base)))) =
      some (mapLabelCfg embedLeftController
        (mapLabelCfg (fun l : ShiftLeftRoundTailLabel Unit => Sum.inr l)
          (mapLabelCfg (fun l : ShiftRoundFinalLabel Unit => Sum.inr l)
            (mapLabelCfg (fun l : Unit => Sum.inr l)
              (cleanReturnCfg () finalState
                (shiftRoundBase w (2 * word) count fuel m base)))))) := by
  rcases shiftLeftRound_correct () (fun _ => .halt) w word count hw fuel m
      base state hmove with ⟨finalState, hrun⟩
  refine ⟨finalState, ?_⟩
  apply iterate_mapLabelProgram_until_exit
    (shiftLeftRoundProgram () (fun _ => .halt))
    (cappedShiftProgram false) embedLeftController cappedLeftSource_embeds hrun
  rfl

def embedRightController : ShiftRightRoundLabel Unit -> CappedShiftLabel :=
  CappedShiftLabel.right

theorem cappedRightSource_embeds {N : Nat}
    (label : ShiftRightRoundLabel Unit)
    (hn : shiftRightRoundProgram (N := N) () (fun _ => .halt) label ≠ .halt) :
    cappedShiftProgram (N := N) true (embedRightController label) =
      mapLabelStmt embedRightController
        (shiftRightRoundProgram () (fun _ => .halt) label) := by
  rcases label with label | tail
  · rfl
  rcases tail with label | tail
  · rfl
  rcases tail with label | tail
  · rfl
  cases tail
  exact False.elim (hn rfl)

theorem cappedRightRound_correct {N : Nat}
    (w word count : Nat) (hw : 0 < w) (hword : word < 2 ^ w)
    (fuel : List SparseSymbol) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N)
    (hmove : FullInterpreterState.moveLens.get state = default) :
    ∃ finalState,
      ((fun x => x.bind (TM2.step (cappedShiftProgram true)))^[4 * w + 7])
        (some (mapLabelCfg embedRightController
          (lensRenamedCfg shiftRoundRenaming FullInterpreterState.shiftLens
            (sparseShiftRightLocalCfg .discard (fixedBits w word) [] [])
            state (shiftRoundBase w word count fuel m base)))) =
      some (mapLabelCfg embedRightController
        (mapLabelCfg (fun l : ShiftLeftRoundTailLabel Unit => Sum.inr l)
          (mapLabelCfg (fun l : ShiftRoundFinalLabel Unit => Sum.inr l)
            (mapLabelCfg (fun l : Unit => Sum.inr l)
              (cleanReturnCfg () finalState
                (shiftRoundBase w (word / 2) count fuel m base)))))) := by
  rcases shiftRightRound_correct () (fun _ => .halt) w word count hw hword
      fuel m base state hmove with ⟨finalState, hrun⟩
  refine ⟨finalState, ?_⟩
  apply iterate_mapLabelProgram_until_exit
    (shiftRightRoundProgram () (fun _ => .halt))
    (cappedShiftProgram true) embedRightController cappedRightSource_embeds hrun
  rfl

theorem cappedShift_fuel_left_step {N : Nat}
    (w word count : Nat) (symbol : SparseSymbol)
    (fuel : List SparseSymbol) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    TM2.step (cappedShiftProgram false)
      (cappedShiftCfg .fuel state w word count (symbol :: fuel) m base) =
    some (cappedShiftCfg (.left (Sum.inl .first))
      (resetShiftControls state) w word count fuel m base) := by
  simp [cappedShiftProgram, cappedShiftCfg, cappedShiftStacks,
    cleanReturnCfg, shiftRoundBase, TM2.step, TM2.stepAux,
    resetShiftControls, FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]
  congr 2
  funext k
  cases k <;> simp [shiftRoundBase, Function.update]

theorem cappedShift_fuel_right_step {N : Nat}
    (w word count : Nat) (symbol : SparseSymbol)
    (fuel : List SparseSymbol) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    TM2.step (cappedShiftProgram true)
      (cappedShiftCfg .fuel state w word count (symbol :: fuel) m base) =
    some (cappedShiftCfg (.right (Sum.inl .discard))
      (resetShiftControls state) w word count fuel m base) := by
  simp [cappedShiftProgram, cappedShiftCfg, cappedShiftStacks,
    cleanReturnCfg, shiftRoundBase, TM2.step, TM2.stepAux,
    resetShiftControls, FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]
  congr 2
  funext k
  cases k <;> simp [shiftRoundBase, Function.update]

theorem cappedShift_fuel_empty_step {N : Nat} (rightShift : Bool)
    (w word count : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    TM2.step (cappedShiftProgram rightShift)
      (cappedShiftCfg .fuel state w word count [] m base) =
    some (cappedShiftCfg .cleanupFuel
      (FullInterpreterState.moveLens.put state ⟨none⟩)
      w word count [] m base) := by
  simp [cappedShiftProgram, cappedShiftCfg, cappedShiftStacks,
    cleanReturnCfg, shiftRoundBase, TM2.step, TM2.stepAux,
    FullInterpreterState.moveLens.get_put]

def controllerCfg {N : Nat} (label : CappedShiftLabel)
    (state : FullInterpreterState N)
    (tapes : CoreStack -> List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol) CappedShiftLabel
      (FullInterpreterState N) :=
  cleanReturnCfg label state tapes

theorem cappedShift_cleanup_cons_step {N : Nat} (rightShift : Bool)
    (stack : CoreStack) (again next : CappedShiftLabel)
    (hprogram : cappedShiftProgram (N := N) rightShift again =
      cappedShiftCleanupStmt stack again next)
    (symbol : SparseSymbol) (rest : List SparseSymbol)
    (state : FullInterpreterState N)
    (tapes : CoreStack -> List SparseSymbol)
    (hstack : tapes stack = symbol :: rest) :
    TM2.step (cappedShiftProgram rightShift)
      (controllerCfg again state tapes) =
    some (controllerCfg again
      (FullInterpreterState.moveLens.put state default)
      (Function.update tapes stack rest)) := by
  simp [controllerCfg, cleanReturnCfg, TM2.step, hprogram,
    cappedShiftCleanupStmt, TM2.stepAux, hstack,
    FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]

theorem cappedShift_cleanup_nil_step {N : Nat} (rightShift : Bool)
    (stack : CoreStack) (again next : CappedShiftLabel)
    (hprogram : cappedShiftProgram (N := N) rightShift again =
      cappedShiftCleanupStmt stack again next)
    (state : FullInterpreterState N)
    (tapes : CoreStack -> List SparseSymbol)
    (hstack : tapes stack = []) :
    TM2.step (cappedShiftProgram rightShift)
      (controllerCfg again state tapes) =
    some (controllerCfg next
      (FullInterpreterState.moveLens.put state ⟨none⟩)
      (Function.update tapes stack [])) := by
  simp [controllerCfg, cleanReturnCfg, TM2.step, hprogram,
    cappedShiftCleanupStmt, TM2.stepAux, hstack,
    FullInterpreterState.moveLens.get_put]

theorem cappedShift_cleanup_drain {N : Nat} (rightShift : Bool)
    (stack : CoreStack) (again next : CappedShiftLabel)
    (hprogram : cappedShiftProgram (N := N) rightShift again =
      cappedShiftCleanupStmt stack again next)
    (data : List SparseSymbol) (state : FullInterpreterState N)
    (tapes : CoreStack -> List SparseSymbol)
    (hstack : tapes stack = data) :
    ∃ finalState,
      ((fun x => x.bind (TM2.step (cappedShiftProgram rightShift)))^[
          data.length + 1])
        (some (controllerCfg again state tapes)) =
      some (controllerCfg next finalState
        (Function.update tapes stack [])) := by
  induction data generalizing state tapes with
  | nil =>
      refine ⟨FullInterpreterState.moveLens.put state ⟨none⟩, ?_⟩
      simpa using cappedShift_cleanup_nil_step rightShift stack again next
        hprogram state tapes hstack
  | cons symbol rest ih =>
      have hfirst := cappedShift_cleanup_cons_step rightShift stack again next
        hprogram symbol rest state tapes hstack
      let tapes' := Function.update tapes stack rest
      have hstack' : tapes' stack = rest := by
        simp [tapes']
      rcases ih (FullInterpreterState.moveLens.put state default)
          tapes' hstack' with ⟨finalState, hrest⟩
      refine ⟨finalState, ?_⟩
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, hfirst]
      simpa [tapes', Function.update_idem] using hrest

theorem cappedShift_cleanup_all {N : Nat} (rightShift : Bool)
    (fuel count temp : List SparseSymbol)
    (state : FullInterpreterState N)
    (tapes : CoreStack -> List SparseSymbol)
    (hfuel : tapes .work1 = fuel) (hcount : tapes .work3 = count)
    (htemp : tapes .work4 = temp) :
    ∃ finalState,
      ((fun x => x.bind (TM2.step (cappedShiftProgram rightShift)))^[
          fuel.length + count.length + temp.length + 3])
        (some (controllerCfg .cleanupFuel state tapes)) =
      some (controllerCfg .done finalState
        (Function.update
          (Function.update (Function.update tapes .work1 []) .work3 [])
          .work4 [])) := by
  rcases cappedShift_cleanup_drain rightShift .work1 .cleanupFuel
      .cleanupCount (by rfl) fuel state tapes hfuel with
    ⟨state₁, h₁⟩
  let tapes₁ := Function.update tapes CoreStack.work1 []
  have hcount₁ : tapes₁ .work3 = count := by
    simp [tapes₁, hcount]
  rcases cappedShift_cleanup_drain rightShift .work3 .cleanupCount
      .cleanupTemp (by rfl) count state₁ tapes₁ hcount₁ with
    ⟨state₂, h₂⟩
  let tapes₂ := Function.update tapes₁ CoreStack.work3 []
  have htemp₂ : tapes₂ .work4 = temp := by
    simp [tapes₂, tapes₁, htemp]
  rcases cappedShift_cleanup_drain rightShift .work4 .cleanupTemp
      .done (by rfl) temp state₂ tapes₂ htemp₂ with
    ⟨state₃, h₃⟩
  refine ⟨state₃, ?_⟩
  let stepO := fun x : Option (TM2.Cfg
      (fun _ : CoreStack => SparseSymbol) CappedShiftLabel
      (FullInterpreterState N)) =>
    x.bind (TM2.step (cappedShiftProgram rightShift))
  have h₁₂ := chain_iterations stepO h₁ h₂
  have h₁₂₃ := chain_iterations stepO h₁₂ h₃
  simpa [stepO, tapes₂, tapes₁,
    show (fuel.length + 1) + (count.length + 1) + (temp.length + 1) =
      fuel.length + count.length + temp.length + 3 by omega] using h₁₂₃

theorem cappedCountdown_start_bridge {N : Nat}
    (w word count : Nat) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    mapLabelCfg embedCountdownController
      (lensRenamedCfg countdownCoreRenaming
        FullInterpreterState.countdownLens
        (sparseCountdownCfg .scan default (fixedBits w count) [])
        state (shiftRoundBase w word count fuel m base)) =
    cappedShiftCfg (.countdown .scan)
      (FullInterpreterState.countdownLens.put state default)
      w word count fuel m base := by
  simp [mapLabelCfg, lensRenamedCfg, sparseCountdownCfg, countdownCfg,
    mapAlphabetCfg, mapAlphabetStacks, sparseBitEncode,
    cappedShiftCfg, cappedShiftStacks, cleanReturnCfg, shiftRoundBase,
    renamedStacks, countdownCoreRenaming, countdownCoreDecode]
  constructor
  · exact ⟨.scan, rfl, rfl⟩
  · funext k
    cases k <;> simp [shiftRoundBase, renamedStacks, countdownCoreRenaming,
      countdownCoreDecode, countdownCfg, countdownStacks,
      mapAlphabetCfg, mapAlphabetStacks, sparseBitEncode]

theorem cappedCountdown_positive_bridge {N : Nat}
    (localFinal : CountdownControl) (w word oldCount count : Nat)
    (fuel : List SparseSymbol) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    mapLabelCfg embedCountdownController
      (mapLabelCfg Sum.inr
        (multiPhaseReturnCfg countdownCoreRenaming
          FullInterpreterState.countdownLens CappedShiftLabel.fuel id
          (sparseCountdownCfg .positive localFinal
            (fixedBits w count) []) state
          (shiftRoundBase w word oldCount fuel m base))) =
    cappedShiftCfg .fuel
      (FullInterpreterState.countdownLens.put state localFinal)
      w word count fuel m base := by
  simp [mapLabelCfg, multiPhaseReturnCfg, sparseCountdownCfg, countdownCfg,
    mapAlphabetCfg, mapAlphabetStacks, sparseBitEncode,
    cappedShiftCfg, cappedShiftStacks, cleanReturnCfg, shiftRoundBase,
    renamedStacks, countdownCoreRenaming, countdownCoreDecode]
  constructor
  · rfl
  · funext k
    cases k <;> simp [shiftRoundBase, renamedStacks, countdownCoreRenaming,
      countdownCoreDecode, countdownCfg, countdownStacks,
      mapAlphabetCfg, mapAlphabetStacks, sparseBitEncode]

theorem cappedLeft_start_bridge {N : Nat}
    (w word count : Nat) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    mapLabelCfg embedLeftController
      (lensRenamedCfg shiftRoundRenaming FullInterpreterState.shiftLens
        (sparseShiftLeftLocalCfg .first (fixedBits w word) [] [])
        state (shiftRoundBase w word count fuel m base)) =
    cappedShiftCfg (.left (Sum.inl .first))
      (FullInterpreterState.shiftLens.put state default)
      w word count fuel m base := by
  simp [mapLabelCfg, lensRenamedCfg, sparseShiftLeftLocalCfg,
    mapAlphabetCfg, mapAlphabetStacks, sparseBitEncode, shiftCfg, shiftStacks,
    cappedShiftCfg, cappedShiftStacks, cleanReturnCfg, shiftRoundBase,
    renamedStacks, shiftRoundRenaming, shiftRoundDecode]
  constructor
  · exact ⟨.first, rfl, rfl⟩
  · constructor
    · rfl
    · funext k
      cases k <;> simp [shiftRoundBase, renamedStacks, shiftRoundRenaming,
        shiftRoundDecode, sparseShiftLeftLocalCfg, mapAlphabetCfg,
        mapAlphabetStacks, sparseBitEncode, shiftCfg, shiftStacks]

theorem cappedRight_start_bridge {N : Nat}
    (w word count : Nat) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    mapLabelCfg embedRightController
      (lensRenamedCfg shiftRoundRenaming FullInterpreterState.shiftLens
        (sparseShiftRightLocalCfg .discard (fixedBits w word) [] [])
        state (shiftRoundBase w word count fuel m base)) =
    cappedShiftCfg (.right (Sum.inl .discard))
      (FullInterpreterState.shiftLens.put state default)
      w word count fuel m base := by
  simp [mapLabelCfg, lensRenamedCfg, sparseShiftRightLocalCfg,
    mapAlphabetCfg, mapAlphabetStacks, sparseBitEncode,
    shiftRightCfg, shiftStacks, cappedShiftCfg, cappedShiftStacks,
    cleanReturnCfg, shiftRoundBase, renamedStacks, shiftRoundRenaming,
    shiftRoundDecode]
  constructor
  · exact ⟨.discard, rfl, rfl⟩
  · constructor
    · rfl
    · funext k
      cases k <;> simp [shiftRoundBase, renamedStacks, shiftRoundRenaming,
        shiftRoundDecode, sparseShiftRightLocalCfg, mapAlphabetCfg,
        mapAlphabetStacks, sparseBitEncode, shiftRightCfg, shiftStacks]

theorem cappedLeft_return_bridge {N : Nat}
    (w word count : Nat) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    mapLabelCfg embedLeftController
      (mapLabelCfg (fun l : ShiftLeftRoundTailLabel Unit => Sum.inr l)
        (mapLabelCfg (fun l : ShiftRoundFinalLabel Unit => Sum.inr l)
          (mapLabelCfg (fun l : Unit => Sum.inr l)
            (cleanReturnCfg () state
              (shiftRoundBase w word count fuel m base))))) =
    cappedShiftCfg (.left (Sum.inr (Sum.inr (Sum.inr ()))))
      state w word count fuel m base := by
  rfl

theorem cappedRight_return_bridge {N : Nat}
    (w word count : Nat) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    mapLabelCfg embedRightController
      (mapLabelCfg (fun l : ShiftLeftRoundTailLabel Unit => Sum.inr l)
        (mapLabelCfg (fun l : ShiftRoundFinalLabel Unit => Sum.inr l)
          (mapLabelCfg (fun l : Unit => Sum.inr l)
            (cleanReturnCfg () state
              (shiftRoundBase w word count fuel m base))))) =
    cappedShiftCfg (.right (Sum.inr (Sum.inr (Sum.inr ()))))
      state w word count fuel m base := by
  rfl

theorem cappedShift_left_return_step {N : Nat}
    (w word count : Nat) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    TM2.step (cappedShiftProgram false)
      (cappedShiftCfg (.left (Sum.inr (Sum.inr (Sum.inr ()))))
        state w word count fuel m base) =
    some (cappedShiftCfg (.countdown .scan)
      (FullInterpreterState.countdownLens.put state default)
      w word count fuel m base) := by
  rfl

theorem cappedShift_right_return_step {N : Nat}
    (w word count : Nat) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    TM2.step (cappedShiftProgram true)
      (cappedShiftCfg (.right (Sum.inr (Sum.inr (Sum.inr ()))))
        state w word count fuel m base) =
    some (cappedShiftCfg (.countdown .scan)
      (FullInterpreterState.countdownLens.put state default)
      w word count fuel m base) := by
  rfl

theorem shiftRoundBase_word_mod (w word count : Nat)
    (fuel : List SparseSymbol) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) :
    shiftRoundBase w word count fuel m base =
      shiftRoundBase w (word % 2 ^ w) count fuel m base := by
  funext k
  cases k <;> simp [shiftRoundBase, fixedBits_mod_word]

theorem cappedShiftCfg_word_mod {N : Nat} (label : CappedShiftLabel)
    (state : FullInterpreterState N) (w word count : Nat)
    (fuel : List SparseSymbol) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) :
    cappedShiftCfg label state w word count fuel m base =
      cappedShiftCfg label state w (word % 2 ^ w) count fuel m base := by
  simp only [cappedShiftCfg, cappedShiftStacks]
  rw [shiftRoundBase_word_mod]

theorem cappedLeft_cycle_correct {N : Nat}
    (w word count : Nat) (hw : 0 < w)
    (hcount0 : 0 < count) (hcount : count < 2 ^ w)
    (symbol : SparseSymbol) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N)
    (hcountdown : FullInterpreterState.countdownLens.get state = default) :
    ∃ finalState,
      FullInterpreterState.countdownLens.get finalState = default ∧
      ((fun x => x.bind (TM2.step (cappedShiftProgram false)))^[6 * w + 13])
        (some (cappedShiftCfg (.countdown .scan)
          state w word count (symbol :: fuel) m base)) =
      some (cappedShiftCfg (.countdown .scan) finalState w
        ((2 * word) % 2 ^ w) (count - 1) fuel m base) := by
  rcases cappedCountdown_positive_correct false w count hcount0 hcount state
      (shiftRoundBase w word count (symbol :: fuel) m base) with
    ⟨countState, hcountRun⟩
  rw [cappedCountdown_start_bridge w word count (symbol :: fuel) m base state]
    at hcountRun
  rw [cappedCountdown_positive_bridge countState w word count (count - 1)
      (symbol :: fuel) m base state] at hcountRun
  have hstate : FullInterpreterState.countdownLens.put state default = state := by
    rw [← hcountdown]
    exact FullInterpreterState.countdownLens.put_get state
  rw [hstate] at hcountRun
  let afterCount := FullInterpreterState.countdownLens.put state countState
  have hfuel := cappedShift_fuel_left_step w word (count - 1) symbol fuel m
    base afterCount
  let roundState := resetShiftControls afterCount
  rcases cappedLeftRound_correct w word (count - 1) hw fuel m base roundState
      (resetShiftControls_move afterCount) with ⟨afterRound, hround⟩
  rw [cappedLeft_start_bridge w word (count - 1) fuel m base roundState]
    at hround
  rw [show FullInterpreterState.shiftLens.put roundState default = roundState by
      rw [← resetShiftControls_shift afterCount]
      exact FullInterpreterState.shiftLens.put_get roundState] at hround
  rw [cappedLeft_return_bridge w (2 * word) (count - 1) fuel m base afterRound]
    at hround
  have hreturn := cappedShift_left_return_step w (2 * word) (count - 1)
    fuel m base afterRound
  let cycleState := FullInterpreterState.countdownLens.put afterRound default
  let stepO := fun x : Option (TM2.Cfg
      (fun _ : CoreStack => SparseSymbol) CappedShiftLabel
      (FullInterpreterState N)) =>
    x.bind (TM2.step (cappedShiftProgram false))
  have hfuel' : (stepO^[1])
      (some (cappedShiftCfg .fuel afterCount w word (count - 1)
        (symbol :: fuel) m base)) =
      some (cappedShiftCfg (.left (Sum.inl .first)) roundState
        w word (count - 1) fuel m base) := by
    simpa [stepO, roundState] using hfuel
  have hreturn' : (stepO^[1])
      (some (cappedShiftCfg (.left (Sum.inr (Sum.inr (Sum.inr ()))))
        afterRound w (2 * word) (count - 1) fuel m base)) =
      some (cappedShiftCfg (.countdown .scan) cycleState
        w (2 * word) (count - 1) fuel m base) := by
    simpa [stepO, cycleState] using hreturn
  have h₁ := chain_iterations stepO hcountRun hfuel'
  have h₂ := chain_iterations stepO h₁ hround
  have h₃ := chain_iterations stepO h₂ hreturn'
  rw [cappedShiftCfg_word_mod (.countdown .scan) cycleState w (2 * word)
    (count - 1) fuel m base] at h₃
  refine ⟨cycleState, FullInterpreterState.countdownLens.get_put _ _, ?_⟩
  simpa [stepO, afterCount, roundState,
    show (2 * w + 3) + 1 + (4 * w + 8) + 1 = 6 * w + 13 by omega]
    using h₃

theorem cappedRight_cycle_correct {N : Nat}
    (w word count : Nat) (hw : 0 < w) (hword : word < 2 ^ w)
    (hcount0 : 0 < count) (hcount : count < 2 ^ w)
    (symbol : SparseSymbol) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N)
    (hcountdown : FullInterpreterState.countdownLens.get state = default) :
    ∃ finalState,
      FullInterpreterState.countdownLens.get finalState = default ∧
      ((fun x => x.bind (TM2.step (cappedShiftProgram true)))^[6 * w + 12])
        (some (cappedShiftCfg (.countdown .scan)
          state w word count (symbol :: fuel) m base)) =
      some (cappedShiftCfg (.countdown .scan) finalState w
        (word / 2) (count - 1) fuel m base) := by
  rcases cappedCountdown_positive_correct true w count hcount0 hcount state
      (shiftRoundBase w word count (symbol :: fuel) m base) with
    ⟨countState, hcountRun⟩
  rw [cappedCountdown_start_bridge w word count (symbol :: fuel) m base state]
    at hcountRun
  rw [cappedCountdown_positive_bridge countState w word count (count - 1)
      (symbol :: fuel) m base state] at hcountRun
  have hstate : FullInterpreterState.countdownLens.put state default = state := by
    rw [← hcountdown]
    exact FullInterpreterState.countdownLens.put_get state
  rw [hstate] at hcountRun
  let afterCount := FullInterpreterState.countdownLens.put state countState
  have hfuel := cappedShift_fuel_right_step w word (count - 1) symbol fuel m
    base afterCount
  let roundState := resetShiftControls afterCount
  rcases cappedRightRound_correct w word (count - 1) hw hword fuel m base
      roundState (resetShiftControls_move afterCount) with
    ⟨afterRound, hround⟩
  rw [cappedRight_start_bridge w word (count - 1) fuel m base roundState]
    at hround
  rw [show FullInterpreterState.shiftLens.put roundState default = roundState by
      rw [← resetShiftControls_shift afterCount]
      exact FullInterpreterState.shiftLens.put_get roundState] at hround
  rw [cappedRight_return_bridge w (word / 2) (count - 1) fuel m base
    afterRound] at hround
  have hreturn := cappedShift_right_return_step w (word / 2) (count - 1)
    fuel m base afterRound
  let cycleState := FullInterpreterState.countdownLens.put afterRound default
  let stepO := fun x : Option (TM2.Cfg
      (fun _ : CoreStack => SparseSymbol) CappedShiftLabel
      (FullInterpreterState N)) =>
    x.bind (TM2.step (cappedShiftProgram true))
  have hfuel' : (stepO^[1])
      (some (cappedShiftCfg .fuel afterCount w word (count - 1)
        (symbol :: fuel) m base)) =
      some (cappedShiftCfg (.right (Sum.inl .discard)) roundState
        w word (count - 1) fuel m base) := by
    simpa [stepO, roundState] using hfuel
  have hreturn' : (stepO^[1])
      (some (cappedShiftCfg (.right (Sum.inr (Sum.inr (Sum.inr ()))))
        afterRound w (word / 2) (count - 1) fuel m base)) =
      some (cappedShiftCfg (.countdown .scan) cycleState
        w (word / 2) (count - 1) fuel m base) := by
    simpa [stepO, cycleState] using hreturn
  have h₁ := chain_iterations stepO hcountRun hfuel'
  have h₂ := chain_iterations stepO h₁ hround
  have h₃ := chain_iterations stepO h₂ hreturn'
  refine ⟨cycleState, FullInterpreterState.countdownLens.get_put _ _, ?_⟩
  simpa [stepO, afterCount, roundState,
    show (2 * w + 3) + 1 + (4 * w + 7) + 1 = 6 * w + 12 by omega]
    using h₃

theorem cappedShift_cleanup_roundBase {N : Nat} (rightShift : Bool)
    (w word count : Nat) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ finalState,
      ((fun x => x.bind (TM2.step (cappedShiftProgram rightShift)))^[
          fuel.length + w + 3])
        (some (cappedShiftCfg .cleanupFuel state
          w word count fuel m base)) =
      some (controllerCfg .done finalState
        (operandBoundaryBase w word m base)) := by
  rcases cappedShift_cleanup_all rightShift fuel
      ((fixedBits w count).map SparseSymbol.bit) [] state
      (shiftRoundBase w word count fuel m base)
      (by rfl) (by rfl) (by rfl) with ⟨finalState, hrun⟩
  refine ⟨finalState, ?_⟩
  have htapes :
      Function.update
        (Function.update
          (Function.update (shiftRoundBase w word count fuel m base)
            .work1 []) .work3 []) .work4 [] =
      operandBoundaryBase w word m base := by
    funext k
    cases k <;> simp [shiftRoundBase, operandBoundaryBase, Function.update]
  simpa [cappedShiftCfg, cappedShiftStacks, List.length_map,
    fixedBits_length, htapes] using hrun

def zeroShiftCleanupBase (w word : Nat) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w word).map SparseSymbol.bit
  | .work1 => fuel
  | .work4 => List.replicate w (.bit true)
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work0 | .work2 | .work3 | .work5 | .work6 | .work7 => []
  | k => base k

theorem cappedCountdown_zero_bridge {N : Nat}
    (w word : Nat) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    mapLabelCfg embedCountdownController
      (mapLabelCfg Sum.inr
        (multiPhaseReturnCfg countdownCoreRenaming
          FullInterpreterState.countdownLens CappedShiftLabel.cleanupFuel id
          (sparseCountdownCfg .zero
            { held := none, borrow := true, positiveSeen := false }
            [] (List.replicate w true)) state
          (shiftRoundBase w word 0 fuel m base))) =
    controllerCfg .cleanupFuel
      (FullInterpreterState.countdownLens.put state
        { held := none, borrow := true, positiveSeen := false })
      (zeroShiftCleanupBase w word fuel m base) := by
  simp [mapLabelCfg, multiPhaseReturnCfg, sparseCountdownCfg, countdownCfg,
    mapAlphabetCfg, mapAlphabetStacks, sparseBitEncode, controllerCfg,
    cleanReturnCfg, zeroShiftCleanupBase, shiftRoundBase, renamedStacks,
    countdownCoreRenaming, countdownCoreDecode]
  constructor
  · rfl
  · funext k
    cases k <;> simp [zeroShiftCleanupBase, shiftRoundBase, renamedStacks,
      countdownCoreRenaming, countdownCoreDecode, countdownCfg,
      countdownStacks, mapAlphabetCfg, mapAlphabetStacks, sparseBitEncode]

theorem cappedShift_zero_finish {N : Nat} (rightShift : Bool)
    (w word : Nat) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N)
    (hcountdown : FullInterpreterState.countdownLens.get state = default) :
    ∃ finalState,
      ((fun x => x.bind (TM2.step (cappedShiftProgram rightShift)))^[
          fuel.length + 2 * w + 5])
        (some (cappedShiftCfg (.countdown .scan)
          state w word 0 fuel m base)) =
      some (controllerCfg .done finalState
        (operandBoundaryBase w word m base)) := by
  have hzero := cappedCountdown_zero_correct rightShift w state
    (shiftRoundBase w word 0 fuel m base)
  rw [cappedCountdown_start_bridge w word 0 fuel m base state] at hzero
  rw [cappedCountdown_zero_bridge w word fuel m base state] at hzero
  have hstate : FullInterpreterState.countdownLens.put state default = state := by
    rw [← hcountdown]
    exact FullInterpreterState.countdownLens.put_get state
  rw [hstate] at hzero
  let zeroState := FullInterpreterState.countdownLens.put state
    { held := none, borrow := true, positiveSeen := false }
  rcases cappedShift_cleanup_all rightShift fuel []
      (List.replicate w (.bit true)) zeroState
      (zeroShiftCleanupBase w word fuel m base)
      (by rfl) (by rfl) (by rfl) with ⟨finalState, hclean⟩
  have htapes :
      Function.update
        (Function.update
          (Function.update (zeroShiftCleanupBase w word fuel m base)
            .work1 []) .work3 []) .work4 [] =
      operandBoundaryBase w word m base := by
    funext k
    cases k <;> simp [zeroShiftCleanupBase, operandBoundaryBase,
      Function.update]
  let stepO := fun x : Option (TM2.Cfg
      (fun _ : CoreStack => SparseSymbol) CappedShiftLabel
      (FullInterpreterState N)) =>
    x.bind (TM2.step (cappedShiftProgram rightShift))
  rw [htapes] at hclean
  simp only [List.length_nil, List.length_replicate] at hclean
  have hall := chain_iterations stepO hzero hclean
  refine ⟨finalState, ?_⟩
  change (stepO^[fuel.length + 2 * w + 5])
    (some (cappedShiftCfg (.countdown .scan)
      state w word 0 fuel m base)) = _
  rw [show fuel.length + 2 * w + 5 =
    (w + 2) + (fuel.length + 0 + w + 3) by omega]
  exact hall

theorem cappedShift_positive_noFuel_finish {N : Nat} (rightShift : Bool)
    (w word count : Nat) (hcount0 : 0 < count)
    (hcount : count < 2 ^ w)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N)
    (hcountdown : FullInterpreterState.countdownLens.get state = default) :
    ∃ finalState,
      ((fun x => x.bind (TM2.step (cappedShiftProgram rightShift)))^[
          3 * w + 7])
        (some (cappedShiftCfg (.countdown .scan)
          state w word count [] m base)) =
      some (controllerCfg .done finalState
        (operandBoundaryBase w word m base)) := by
  rcases cappedCountdown_positive_correct rightShift w count hcount0 hcount state
      (shiftRoundBase w word count [] m base) with
    ⟨countState, hcountRun⟩
  rw [cappedCountdown_start_bridge w word count [] m base state] at hcountRun
  rw [cappedCountdown_positive_bridge countState w word count (count - 1)
      [] m base state] at hcountRun
  have hstate : FullInterpreterState.countdownLens.put state default = state := by
    rw [← hcountdown]
    exact FullInterpreterState.countdownLens.put_get state
  rw [hstate] at hcountRun
  let afterCount := FullInterpreterState.countdownLens.put state countState
  have hfuel := cappedShift_fuel_empty_step rightShift w word (count - 1)
    m base afterCount
  let afterFuel := FullInterpreterState.moveLens.put afterCount ⟨none⟩
  rcases cappedShift_cleanup_roundBase rightShift w word (count - 1) [] m base
      afterFuel with ⟨finalState, hclean⟩
  let stepO := fun x : Option (TM2.Cfg
      (fun _ : CoreStack => SparseSymbol) CappedShiftLabel
      (FullInterpreterState N)) =>
    x.bind (TM2.step (cappedShiftProgram rightShift))
  have hfuel' : (stepO^[1])
      (some (cappedShiftCfg .fuel afterCount w word (count - 1) [] m base)) =
      some (cappedShiftCfg .cleanupFuel afterFuel
        w word (count - 1) [] m base) := by
    simpa [stepO, afterFuel] using hfuel
  have h₁ := chain_iterations stepO hcountRun hfuel'
  have h₂ := chain_iterations stepO h₁ hclean
  refine ⟨finalState, ?_⟩
  change (stepO^[3 * w + 7])
    (some (cappedShiftCfg (.countdown .scan)
      state w word count [] m base)) = _
  rw [show 3 * w + 7 = (2 * w + 3) + 1 + (0 + w + 3) by omega]
  exact h₂

def cappedShiftLoopBound (w : Nat) : Nat -> Nat
  | 0 => 3 * w + 7
  | fuel + 1 => 6 * w + 14 + cappedShiftLoopBound w fuel

theorem fuel_le_cappedShiftLoopBound (w fuel : Nat) :
    fuel <= cappedShiftLoopBound w fuel := by
  induction fuel with
  | zero => simp [cappedShiftLoopBound]
  | succ fuel ih =>
      simp [cappedShiftLoopBound]
      omega

def cappedLeftValue (w word count : Nat) : Nat -> Nat
  | 0 => word
  | fuel + 1 =>
      if count = 0 then word
      else cappedLeftValue w ((2 * word) % 2 ^ w) (count - 1) fuel

def cappedRightValue (word count : Nat) : Nat -> Nat
  | 0 => word
  | fuel + 1 =>
      if count = 0 then word
      else cappedRightValue (word / 2) (count - 1) fuel

theorem min_succ_of_pos (count fuel : Nat) (hcount : 0 < count) :
    min count (fuel + 1) = min (count - 1) fuel + 1 := by
  omega

theorem cappedLeftValue_eq_min (w word count fuel : Nat)
    (hword : word < 2 ^ w) :
    cappedLeftValue w word count fuel =
      word * 2 ^ min count fuel % 2 ^ w := by
  induction fuel generalizing word count with
  | zero =>
      simp [cappedLeftValue, Nat.mod_eq_of_lt hword]
  | succ fuel ih =>
      by_cases hc0 : count = 0
      · subst count
        simp [cappedLeftValue, Nat.mod_eq_of_lt hword]
      · have hcpos : 0 < count := Nat.pos_of_ne_zero hc0
        let word' := 2 * word % 2 ^ w
        have hword' : word' < 2 ^ w := Nat.mod_lt _ (by positivity)
        rw [cappedLeftValue]
        simp only [hc0, ↓reduceIte]
        rw [ih word' (count - 1) hword', min_succ_of_pos count fuel hcpos,
          pow_succ]
        dsimp [word']
        rw [Nat.mod_mul_mod]
        congr 1
        ring

theorem cappedRightValue_eq_min (word count fuel : Nat) :
    cappedRightValue word count fuel = word / 2 ^ min count fuel := by
  induction fuel generalizing word count with
  | zero => simp [cappedRightValue]
  | succ fuel ih =>
      by_cases hc0 : count = 0
      · subst count
        simp [cappedRightValue]
      · have hcpos : 0 < count := Nat.pos_of_ne_zero hc0
        rw [cappedRightValue]
        simp only [hc0, ↓reduceIte]
        rw [ih, min_succ_of_pos count fuel hcpos, pow_succ,
          Nat.div_div_eq_div_mul]
        rw [Nat.mul_comm 2 (2 ^ min (count - 1) fuel)]

theorem cappedLeftValue_width (w word count : Nat)
    (hword : word < 2 ^ w) :
    cappedLeftValue w word count w = word * 2 ^ count % 2 ^ w := by
  rw [cappedLeftValue_eq_min w word count w hword]
  by_cases hc : count <= w
  · rw [Nat.min_eq_left hc]
  · have hwc : w < count := Nat.lt_of_not_ge hc
    rw [Nat.min_eq_right (Nat.le_of_lt hwc)]
    have hdvd : 2 ^ w ∣ 2 ^ count := Nat.pow_dvd_pow 2 (Nat.le_of_lt hwc)
    have hleft : word * 2 ^ w % 2 ^ w = 0 := by simp
    have hright : word * 2 ^ count % 2 ^ w = 0 := by
      exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hdvd word)
    rw [hleft, hright]

theorem cappedRightValue_width (w word count : Nat)
    (hword : word < 2 ^ w) :
    cappedRightValue word count w = word / 2 ^ count := by
  rw [cappedRightValue_eq_min]
  by_cases hc : count <= w
  · rw [Nat.min_eq_left hc]
  · have hwc : w < count := Nat.lt_of_not_ge hc
    rw [Nat.min_eq_right (Nat.le_of_lt hwc)]
    have hp : 2 ^ w <= 2 ^ count := Nat.pow_le_pow_right (by omega) hwc.le
    rw [Nat.div_eq_of_lt hword, Nat.div_eq_of_lt (lt_of_lt_of_le hword hp)]

theorem cappedLeft_loop_correct {N : Nat}
    (w word count : Nat) (hw : 0 < w) (hword : word < 2 ^ w)
    (hcount : count < 2 ^ w) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N)
    (hcountdown : FullInterpreterState.countdownLens.get state = default) :
    ∃ steps, steps <= cappedShiftLoopBound w fuel.length ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step (cappedShiftProgram false)))^[steps])
        (some (cappedShiftCfg (.countdown .scan)
          state w word count fuel m base)) =
      some (controllerCfg .done finalState
        (operandBoundaryBase w
          (cappedLeftValue w word count fuel.length) m base)) := by
  induction fuel generalizing word count state with
  | nil =>
      by_cases hc0 : count = 0
      · subst count
        rcases cappedShift_zero_finish false w word [] m base state hcountdown with
          ⟨finalState, hrun⟩
        refine ⟨2 * w + 5, ?_, finalState, ?_⟩
        · simp [cappedShiftLoopBound]; omega
        · simpa [cappedLeftValue] using hrun
      · have hcpos : 0 < count := Nat.pos_of_ne_zero hc0
        rcases cappedShift_positive_noFuel_finish false w word count hcpos
            hcount m base state hcountdown with ⟨finalState, hrun⟩
        exact ⟨3 * w + 7, by rfl, finalState, by
          simpa [cappedShiftLoopBound, cappedLeftValue] using hrun⟩
  | cons symbol fuel ih =>
      by_cases hc0 : count = 0
      · subst count
        rcases cappedShift_zero_finish false w word (symbol :: fuel) m base
            state hcountdown with ⟨finalState, hrun⟩
        refine ⟨(symbol :: fuel).length + 2 * w + 5, ?_, finalState, ?_⟩
        · simp [cappedShiftLoopBound]
          have hb := fuel_le_cappedShiftLoopBound w fuel.length
          omega
        · simpa [cappedLeftValue] using hrun
      · have hcpos : 0 < count := Nat.pos_of_ne_zero hc0
        rcases cappedLeft_cycle_correct w word count hw hcpos hcount symbol fuel
            m base state hcountdown with ⟨cycleState, hcycleCountdown, hcycle⟩
        let word' := (2 * word) % 2 ^ w
        have hword' : word' < 2 ^ w := by
          exact Nat.mod_lt _ (by positivity)
        have hcount' : count - 1 < 2 ^ w := lt_of_le_of_lt
          (Nat.sub_le count 1) hcount
        rcases ih word' (count - 1) hword' hcount' cycleState
            hcycleCountdown with ⟨restSteps, hrestBound, finalState, hrest⟩
        let stepO := fun x : Option (TM2.Cfg
            (fun _ : CoreStack => SparseSymbol) CappedShiftLabel
            (FullInterpreterState N)) =>
          x.bind (TM2.step (cappedShiftProgram false))
        have hall := chain_iterations stepO hcycle hrest
        refine ⟨(6 * w + 13) + restSteps, ?_, finalState, ?_⟩
        · simp [cappedShiftLoopBound]
          omega
        · change (stepO^[(6 * w + 13) + restSteps])
            (some (cappedShiftCfg (.countdown .scan)
              state w word count (symbol :: fuel) m base)) = _
          simpa [cappedLeftValue, hc0, word'] using hall

theorem cappedRight_loop_correct {N : Nat}
    (w word count : Nat) (hw : 0 < w) (hword : word < 2 ^ w)
    (hcount : count < 2 ^ w) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N)
    (hcountdown : FullInterpreterState.countdownLens.get state = default) :
    ∃ steps, steps <= cappedShiftLoopBound w fuel.length ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step (cappedShiftProgram true)))^[steps])
        (some (cappedShiftCfg (.countdown .scan)
          state w word count fuel m base)) =
      some (controllerCfg .done finalState
        (operandBoundaryBase w
          (cappedRightValue word count fuel.length) m base)) := by
  induction fuel generalizing word count state with
  | nil =>
      by_cases hc0 : count = 0
      · subst count
        rcases cappedShift_zero_finish true w word [] m base state hcountdown with
          ⟨finalState, hrun⟩
        refine ⟨2 * w + 5, ?_, finalState, ?_⟩
        · simp [cappedShiftLoopBound]; omega
        · simpa [cappedRightValue] using hrun
      · have hcpos : 0 < count := Nat.pos_of_ne_zero hc0
        rcases cappedShift_positive_noFuel_finish true w word count hcpos
            hcount m base state hcountdown with ⟨finalState, hrun⟩
        exact ⟨3 * w + 7, by rfl, finalState, by
          simpa [cappedShiftLoopBound, cappedRightValue] using hrun⟩
  | cons symbol fuel ih =>
      by_cases hc0 : count = 0
      · subst count
        rcases cappedShift_zero_finish true w word (symbol :: fuel) m base
            state hcountdown with ⟨finalState, hrun⟩
        refine ⟨(symbol :: fuel).length + 2 * w + 5, ?_, finalState, ?_⟩
        · simp [cappedShiftLoopBound]
          have hb := fuel_le_cappedShiftLoopBound w fuel.length
          omega
        · simpa [cappedRightValue] using hrun
      · have hcpos : 0 < count := Nat.pos_of_ne_zero hc0
        rcases cappedRight_cycle_correct w word count hw hword hcpos hcount
            symbol fuel m base state hcountdown with
          ⟨cycleState, hcycleCountdown, hcycle⟩
        have hword' : word / 2 < 2 ^ w :=
          lt_of_le_of_lt (Nat.div_le_self word 2) hword
        have hcount' : count - 1 < 2 ^ w := lt_of_le_of_lt
          (Nat.sub_le count 1) hcount
        rcases ih (word / 2) (count - 1) hword' hcount' cycleState
            hcycleCountdown with ⟨restSteps, hrestBound, finalState, hrest⟩
        let stepO := fun x : Option (TM2.Cfg
            (fun _ : CoreStack => SparseSymbol) CappedShiftLabel
            (FullInterpreterState N)) =>
          x.bind (TM2.step (cappedShiftProgram true))
        have hall := chain_iterations stepO hcycle hrest
        refine ⟨(6 * w + 12) + restSteps, ?_, finalState, ?_⟩
        · simp [cappedShiftLoopBound]
          omega
        · change (stepO^[(6 * w + 12) + restSteps])
            (some (cappedShiftCfg (.countdown .scan)
              state w word count (symbol :: fuel) m base)) = _
          simpa [cappedRightValue, hc0] using hall

end Lax20Proofs.RamToTM
