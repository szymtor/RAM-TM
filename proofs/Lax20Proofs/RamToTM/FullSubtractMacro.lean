import Lax20Proofs.RamToTM.ConditionalSubtractInstall

namespace Lax20Proofs.RamToTM

open Turing TM2

def fullStateIdentityLens (N : Nat) :
    StateLens (FullInterpreterState N) (FullInterpreterState N) where
  get := id
  put := fun _ value => value
  get_put := by intros; rfl
  put_get := by intros; rfl
  put_put := by intros; rfl

abbrev SubtractInstallPhaseLabel (R : Type) :=
  Sum ConditionalInstallLabel R

abbrev FullSubtractTailLabel (R : Type) :=
  Sum AddLabel (SubtractInstallPhaseLabel R)

abbrev FullSubtractLabel (R : Type) :=
  Sum SymbolMoveLabel (FullSubtractTailLabel R)

def subtractInstallPhaseProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    SubtractInstallPhaseLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (SubtractInstallPhaseLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft coreIdentityRenaming (fullStateIdentityLens N)
      (conditionalInstallProgram N) .done returnLabel)
    right

def fullSubtractTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullSubtractTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullSubtractTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft binaryCoreRenaming FullInterpreterState.subLens
      sparseSubCoreProgram .done (Sum.inl ConditionalInstallLabel.loop))
    (subtractInstallPhaseProgram returnLabel right)

def fullSubtractProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullSubtractLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullSubtractLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl AddLabel.loop))
    (fullSubtractTailProgram returnLabel right)

def subtractReadyStacks (w a b : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) : CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w a).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work1 => (fixedBits w b).map SparseSymbol.bit
  | .work0 | .work2 | .work3 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

def subtractResultStacks (w a b : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) : CoreStack -> List SparseSymbol :=
  operandBoundaryBase w (a - b) m base

theorem subtractMove_bridge {N : Nat} {R : Type}
    (w a b : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N)
    (hsub : FullInterpreterState.subLens.get state = default) :
    phaseReturnCfg
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens
      (Sum.inl AddLabel.loop : FullSubtractTailLabel R)
      (symbolMoveLocalCfg .done [] ((fixedBits w b).map SparseSymbol.bit))
      state (operandResultBase w a b m base) =
    lensRenamedCfg binaryCoreRenaming FullInterpreterState.subLens
      (sparseSubLocalCfg false (fixedBits w a) (fixedBits w b) [])
      (FullInterpreterState.moveLens.put state default)
      (subtractReadyStacks w a b m base) := by
  simp [phaseReturnCfg, lensRenamedCfg, symbolMoveCoreRenaming,
    symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks,
    operandResultBase, subtractReadyStacks, sparseSubLocalCfg,
    sparseSubCfg, subCfg, addStackFamily, mapAlphabetStacks,
    sparseBitEncode, renamedStacks, binaryCoreRenaming, binaryCoreDecode]
  constructor
  · have hs : FullInterpreterState.subLens.get
        (FullInterpreterState.moveLens.put state default) = default := by
      simpa using hsub
    symm
    calc
      FullInterpreterState.subLens.put
          (FullInterpreterState.moveLens.put state default) default =
        FullInterpreterState.subLens.put
          (FullInterpreterState.moveLens.put state default)
          (FullInterpreterState.subLens.get
            (FullInterpreterState.moveLens.put state default)) := by rw [hs]
      _ = FullInterpreterState.moveLens.put state default :=
        FullInterpreterState.subLens.put_get _
  · funext k
    cases k <;> simp [operandResultBase, subtractReadyStacks,
      symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
      symbolMoveStacks, renamedStacks, binaryCoreRenaming,
      binaryCoreDecode, sparseSubLocalCfg, sparseSubCfg, subCfg,
      addStackFamily, mapAlphabetStacks, sparseBitEncode,
      List.map_reverse]

theorem subtractCore_install_bridge {N : Nat} {R : Type}
    (w a b : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    cleanReturnCfg (Sum.inl ConditionalInstallLabel.loop :
        SubtractInstallPhaseLabel R)
      (FullInterpreterState.subLens.put state
        ⟨decide (a < b), none, none⟩)
      (subtractCoreResultStacks w a b (subtractReadyStacks w a b m base)) =
    mapLabelCfg Sum.inl (conditionalInstallCfg .loop
      (FullInterpreterState.subLens.put state
        ⟨decide (a < b), none, none⟩)
      ((subBits (fixedBits w a) (fixedBits w b) false).reverse.map
        SparseSymbol.bit) []
      (operandBoundaryBase w a m base)) := by
  simp [cleanReturnCfg, conditionalInstallCfg, subtractCoreResultStacks,
    subtractReadyStacks, operandBoundaryBase, mapLabelCfg]
  funext k
  cases k <;> simp [subtractCoreResultStacks, subtractReadyStacks,
    List.map_reverse]

theorem conditionalInstalled_subBits (w a b : Nat) :
    conditionalInstalled (decide (a < b))
      ((subBits (fixedBits w a) (fixedBits w b) false).reverse.map
        SparseSymbol.bit) =
      (fixedBits w (a - b)).map SparseSymbol.bit := by
  by_cases h : a < b
  · have hab : a - b = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt h)
    simp [conditionalInstalled, h, hab, subBits_length_fixed]
  · have hba : b ≤ a := Nat.le_of_not_gt h
    simp [conditionalInstalled, h, fixedBits_sub_of_le w hba,
      List.map_reverse]

theorem conditionalInstalled_subBits_or (force : Bool) (w a b : Nat) :
    conditionalInstalled (decide (a < b) || force)
      ((subBits (fixedBits w a) (fixedBits w b) false).reverse.map
        SparseSymbol.bit) =
      (fixedBits w (if force then 0 else a - b)).map SparseSymbol.bit := by
  cases force
  · simpa using conditionalInstalled_subBits w a b
  · simp [conditionalInstalled, subBits_length_fixed]

theorem subtractInstall_return_bridge {N : Nat} {R : Type}
    (returnLabel : R) (force : Bool) (w a b : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N)
    (hborrow : subtractInstallZero state = (decide (a < b) || force)) :
    phaseReturnCfg coreIdentityRenaming (fullStateIdentityLens N) returnLabel
      (conditionalInstallCfg .done
        (FullInterpreterState.moveLens.put state default) []
        (conditionalInstalled (subtractInstallZero state)
          ((subBits (fixedBits w a) (fixedBits w b) false).reverse.map
            SparseSymbol.bit))
        (operandBoundaryBase w a m base))
      state (operandBoundaryBase w a m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.moveLens.put state default)
      (operandBoundaryBase w (if force then 0 else a - b) m base) := by
  simp [phaseReturnCfg, cleanReturnCfg, conditionalInstallCfg,
    fullStateIdentityLens, renamedStacks_coreIdentity,
    subtractReadyStacks]
  funext k
  cases k <;> simp [operandBoundaryBase, hborrow]
  simpa [List.map_reverse] using conditionalInstalled_subBits_or force w a b

theorem fullSubtract_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a b : Nat) (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N)
    (hsub : FullInterpreterState.subLens.get state = default)
    (force : Bool) (hforce : state.subtractForceZero = force) :
    ∃ finalState,
      ((fun o => o.bind (TM2.step
        (fullSubtractProgram returnLabel right)))^[3 * w + 6])
        (some (lensRenamedCfg
          (symbolMoveCoreRenaming .work0 .work1 (by decide))
          FullInterpreterState.moveLens
          (symbolMoveLocalCfg .loop
            ((fixedBits w b).reverse.map SparseSymbol.bit) [])
          state (operandResultBase w a b m base))) =
      some (mapLabelCfg (fun l : FullSubtractTailLabel R => Sum.inr l)
        (mapLabelCfg (fun l : SubtractInstallPhaseLabel R => Sum.inr l)
          (mapLabelCfg (fun l : R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w (if force then 0 else a - b) m base))))) := by
  have hmove := run_lensPhase_to_right
    (symbolMoveCoreRenaming .work0 .work1 (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl AddLabel.loop)
    (fullSubtractTailProgram returnLabel right)
    (symbolMoveLocal_correct
      ((fixedBits w b).reverse.map SparseSymbol.bit) []) rfl state
    (operandResultBase w a b m base)
  simp only [List.length_map, List.length_reverse, fixedBits_length,
    List.append_nil, List.map_reverse, List.reverse_reverse] at hmove
  rw [subtractMove_bridge w a b m base state hsub] at hmove
  let moveState := FullInterpreterState.moveLens.put state default
  have hcore := fullSubtractCore_correct
    (Sum.inl ConditionalInstallLabel.loop : SubtractInstallPhaseLabel R)
    (subtractInstallPhaseProgram returnLabel right)
    w a b ha hb (subtractReadyStacks w a b m base) moveState
  rw [subtractCore_install_bridge (R := R) w a b m base moveState] at hcore
  let coreState := FullInterpreterState.subLens.put moveState
    ⟨decide (a < b), none, none⟩
  have hinstallRaw := run_lensPhase_to_right coreIdentityRenaming
    (fullStateIdentityLens N) (conditionalInstallProgram N) .done (by rfl)
    returnLabel right
    (conditionalInstall_correct coreState
      ((subBits (fixedBits w a) (fixedBits w b) false).reverse.map
        SparseSymbol.bit)
      (operandBoundaryBase w a m base) (by rfl)) rfl
    coreState (operandBoundaryBase w a m base)
  simp only [List.length_map, List.length_reverse, subBits_length_fixed]
    at hinstallRaw
  rw [subtractInstall_return_bridge returnLabel force w a b m base coreState
    (by
      change (decide (a < b) || state.subtractForceZero) =
        (decide (a < b) || force)
      rw [hforce])]
    at hinstallRaw
  have htail := chain_liftRightProgram (m := w + 2) (n := w + 2)
    (lensPhaseLeft binaryCoreRenaming FullInterpreterState.subLens
      sparseSubCoreProgram .done (Sum.inl ConditionalInstallLabel.loop))
    (subtractInstallPhaseProgram returnLabel right) hcore hinstallRaw
  have htail' :
      ((fun o => o.bind (TM2.step
        (fullSubtractTailProgram returnLabel right)))^[2 * w + 4])
        (some (lensRenamedCfg binaryCoreRenaming FullInterpreterState.subLens
          (sparseSubLocalCfg false (fixedBits w a) (fixedBits w b) [])
          moveState (subtractReadyStacks w a b m base))) =
      some (mapLabelCfg (fun l : SubtractInstallPhaseLabel R => Sum.inr l)
        (mapLabelCfg (fun l : R => Sum.inr l)
          (cleanReturnCfg returnLabel
            (FullInterpreterState.moveLens.put coreState default)
            (operandBoundaryBase w (if force then 0 else a - b) m base)))) := by
    simpa only [show w + 2 + (w + 2) = 2 * w + 4 by omega] using htail
  have hall := chain_liftRightProgram (m := w + 2) (n := 2 * w + 4)
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl AddLabel.loop))
    (fullSubtractTailProgram returnLabel right) hmove htail'
  refine ⟨FullInterpreterState.moveLens.put coreState default, ?_⟩
  have htime : 3 * w + 6 = (w + 2) + (2 * w + 4) := by omega
  rw [htime]
  simpa [fullSubtractProgram, moveState, coreState] using hall

end Lax20Proofs.RamToTM
