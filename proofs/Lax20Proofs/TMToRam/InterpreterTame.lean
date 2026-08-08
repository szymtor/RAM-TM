import Lax20Proofs.TMToRam.ValueBounds

namespace Lax20Proofs.TMToRam

open Lax13Proofs.Imp

attribute [aesop safe apply] ExprTame.lit ExprTame.var ExprTame.get
  ExprTame.add ExprTame.sub ExprTame.div ExprTame.mul_lit_right
  ExprTame.mul_lit_left CondTame.eq CondTame.lt ComTame.skip
  ComTame.read ComTame.assign ComTame.write ComTame.store ComTame.seq
  ComTame.ite ComTame.«while»

theorem seqs_tame {cs : List Com} (h : ∀ c ∈ cs, comTame c) : comTame (seqs cs) := by
  induction cs with
  | nil => simp [seqs]; aesop
  | cons c cs ih =>
      simp only [seqs]
      apply ComTame.seq
      · exact h c (by simp)
      · apply ih
        intro d hd
        exact h d (by simp [hd])

theorem tableRead_tame (name target : String) (index : Expr) (hi : exprTame index) :
    comTame (tableRead name target index) := by
  unfold tableRead
  aesop

theorem readHead_tame (k : ℕ) : comTame (readHead k) := by
  unfold readHead
  apply ComTame.ite <;> aesop
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro c (rfl | rfl | h) <;> aesop

theorem readHeadAndPop_tame (k : ℕ) : comTame (readHeadAndPop k) := by
  unfold readHeadAndPop
  apply ComTame.ite <;> aesop
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro c (rfl | rfl | rfl | h) <;> aesop

theorem compileNumericStmt_tame (q : NumericStmt) (fresh : ℕ) :
    comTame (compileNumericStmt q fresh).com := by
  induction q generalizing fresh with
  | push k table next ih =>
      simp only [compileNumericStmt]
      apply seqs_tame
      simp only [List.mem_cons, List.mem_singleton]
      rintro c (rfl | rfl | rfl | rfl | h)
      · apply tableRead_tame; aesop
      · aesop
      · aesop
      · exact ih (fresh + 1)
      · contradiction
  | peek k width table next ih =>
      simp only [compileNumericStmt]
      apply seqs_tame
      simp only [List.mem_cons, List.mem_singleton]
      rintro c (rfl | rfl | rfl | rfl | h)
      · exact readHead_tame k
      · aesop
      · apply tableRead_tame; aesop
      · exact ih (fresh + 1)
      · contradiction
  | pop k width table next ih =>
      simp only [compileNumericStmt]
      apply seqs_tame
      simp only [List.mem_cons, List.mem_singleton]
      rintro c (rfl | rfl | rfl | rfl | h)
      · exact readHeadAndPop_tame k
      · aesop
      · apply tableRead_tame; aesop
      · exact ih (fresh + 1)
      · contradiction
  | load table next ih =>
      simp only [compileNumericStmt]
      apply ComTame.seq
      · apply tableRead_tame; aesop
      · exact ih (fresh + 1)
  | branch table yes no ihy ihn =>
      simp only [compileNumericStmt]
      apply ComTame.seq
      · apply tableRead_tame; aesop
      · apply ComTame.ite
        · aesop
        · exact ihn (compileNumericStmt yes (fresh + 1)).nextTable
        · exact ihy (fresh + 1)
  | goto table =>
      simp only [compileNumericStmt]
      apply seqs_tame
      simp only [List.mem_cons, List.mem_singleton]
      rintro c (rfl | rfl | h)
      · apply tableRead_tame; aesop
      · aesop
      · contradiction
  | halt => simp [compileNumericStmt]; aesop

theorem initializeArrayFrom_tame (name : String) (i : ℕ) (values : List ℕ) :
    comTame (initializeArrayFrom name i values) := by
  induction values generalizing i with
  | nil => simp [initializeArrayFrom]; aesop
  | cons v values ih =>
      simp only [initializeArrayFrom]
      apply ComTame.seq
      · aesop
      · exact ih (i + 1)

theorem initializeTables_tame (tables : List (String × List ℕ)) :
    comTame (initializeTables tables) := by
  induction tables with
  | nil => simp [initializeTables, seqs]; aesop
  | cons nv tables ih =>
      rcases nv with ⟨name, values⟩
      simp only [initializeTables, seqs]
      apply ComTame.seq
      · simp only [initializeArray]
        exact initializeArrayFrom_tame name 0 values
      · exact ih

theorem compileLabelList_tame (tm : Turing.FinTM2) [Fintype tm.Λ]
    [DecidableEq tm.Λ] (labels : List tm.Λ) (fresh : ℕ) :
    comTame (compileLabelList tm labels fresh).com := by
  induction labels generalizing fresh with
  | nil => simp [compileLabelList]; aesop
  | cons l labels ih =>
      simp only [compileLabelList]
      apply ComTame.ite
      · aesop
      · exact compileNumericStmt_tame _ fresh
      · exact ih (compileNumericStmt (numericStmt tm (tm.m l)
          (FinTM2.generatedBy_main_available tm l)) fresh).nextTable

theorem FinTM2.compileMachine_tame (tm : Turing.FinTM2) :
    comTame (FinTM2.compileMachine tm) := by
  letI := tm.ΛFin
  letI : DecidableEq tm.Λ := Classical.decEq _
  unfold FinTM2.compileMachine FinTM2.compileDispatcher
  apply ComTame.seq
  · exact initializeTables_tame _
  · apply ComTame.«while»
    · aesop
    · exact compileLabelList_tame tm (FinTM2.labelList tm) 0

theorem appendScratch_tame {code : Expr} (hcode : exprTame code) :
    comTame (appendScratch code) := by
  unfold appendScratch
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro c (rfl | rfl | h) <;> aesop

theorem encodeBitsBody_tame (zeroCode oneCode : ℕ) :
    comTame (encodeBitsBody zeroCode oneCode) := by
  unfold encodeBitsBody
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro c (rfl | rfl | rfl | rfl | h)
  · aesop
  · aesop
  · apply ComTame.ite
    · aesop
    · apply appendScratch_tame; aesop
    · apply appendScratch_tame; aesop
  · aesop
  · contradiction

theorem encodeBitsLoop_tame (zeroCode oneCode : ℕ) :
    comTame (encodeBitsLoop zeroCode oneCode) := by
  unfold encodeBitsLoop
  aesop (add safe encodeBitsBody_tame)

theorem encodeInputBody_tame (separatorCode zeroCode oneCode : ℕ) :
    comTame (encodeInputBody separatorCode zeroCode oneCode) := by
  unfold encodeInputBody
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro c (rfl | rfl | rfl | rfl | h)
  · aesop
  · apply appendScratch_tame; aesop
  · exact encodeBitsLoop_tame zeroCode oneCode
  · aesop
  · contradiction

theorem encodeInputLoop_tame (separatorCode zeroCode oneCode : ℕ) :
    comTame (encodeInputLoop separatorCode zeroCode oneCode) := by
  unfold encodeInputLoop
  aesop (add safe encodeInputBody_tame)

theorem encodeNativeInputToScratch_tame (separatorCode zeroCode oneCode : ℕ) :
    comTame (encodeNativeInputToScratch separatorCode zeroCode oneCode) := by
  unfold encodeNativeInputToScratch
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro c (rfl | rfl | rfl | h)
  · aesop
  · aesop
  · exact encodeInputLoop_tame separatorCode zeroCode oneCode
  · contradiction

theorem reverseScratchBody_tame (stack : ℕ) : comTame (reverseScratchBody stack) := by
  unfold reverseScratchBody
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro c (rfl | rfl | rfl | rfl | h) <;> aesop

theorem reverseScratchLoop_tame (stack : ℕ) : comTame (reverseScratchLoop stack) := by
  unfold reverseScratchLoop
  aesop (add safe reverseScratchBody_tame)

theorem reverseScratchIntoStack_tame (stack : ℕ) :
    comTame (reverseScratchIntoStack stack) := by
  unfold reverseScratchIntoStack
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro c (rfl | rfl | rfl | h)
  · aesop
  · aesop
  · exact reverseScratchLoop_tame stack
  · contradiction

theorem compileInputCodec_tame (inputStack separatorCode zeroCode oneCode
    initialStateCode mainLabelCode : ℕ) :
    comTame (compileInputCodec inputStack separatorCode zeroCode oneCode
      initialStateCode mainLabelCode) := by
  unfold compileInputCodec
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro c (rfl | rfl | rfl | rfl | h)
  · exact encodeNativeInputToScratch_tame separatorCode zeroCode oneCode
  · exact reverseScratchIntoStack_tame inputStack
  · aesop
  · aesop
  · contradiction

theorem consumeOutputSymbol_tame (separatorCode zeroCode oneCode : ℕ) :
    comTame (consumeOutputSymbol separatorCode zeroCode oneCode) := by
  unfold consumeOutputSymbol
  apply ComTame.ite
  · aesop
  · apply seqs_tame
    simp only [List.mem_cons, List.mem_singleton]
    rintro c (rfl | rfl | rfl | rfl | h)
    · aesop
    · aesop
    · aesop
    · aesop
    · contradiction
  · apply ComTame.ite
    · aesop
    · aesop
    · apply seqs_tame
      simp only [List.mem_cons, List.mem_singleton]
      rintro c (rfl | rfl | h) <;> aesop

theorem compileOutputCodec_tame (outputStack separatorCode zeroCode oneCode : ℕ) :
    comTame (compileOutputCodec outputStack separatorCode zeroCode oneCode) := by
  unfold compileOutputCodec
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro c (rfl | rfl | rfl | rfl | rfl | rfl | h)
  · aesop
  · aesop
  · aesop
  · aesop
  · apply ComTame.«while»
    · aesop
    · apply seqs_tame
      simp only [List.mem_cons, List.mem_singleton]
      rintro d (rfl | rfl | rfl | h')
      · aesop
      · aesop
      · exact consumeOutputSymbol_tame separatorCode zeroCode oneCode
      · contradiction
  · aesop
  · contradiction

theorem FinTM2.compileNativeMachine_tame (tm : Turing.FinTM2)
    (inputStack outputStack separatorIn zeroIn oneIn separatorOut zeroOut oneOut
      initialStateCode mainLabelCode : ℕ) :
    comTame (FinTM2.compileNativeMachine tm inputStack outputStack separatorIn zeroIn oneIn
      separatorOut zeroOut oneOut initialStateCode mainLabelCode) := by
  unfold FinTM2.compileNativeMachine
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro c (rfl | rfl | rfl | h)
  · exact compileInputCodec_tame inputStack separatorIn zeroIn oneIn
      initialStateCode mainLabelCode
  · exact FinTM2.compileMachine_tame tm
  · exact compileOutputCodec_tame outputStack separatorOut zeroOut oneOut
  · contradiction

noncomputable def FinTM2.nativeBitGrowth (tm : Turing.FinTM2)
    (inputStack outputStack separatorIn zeroIn oneIn separatorOut zeroOut oneOut
      initialStateCode mainLabelCode : ℕ) : ℕ :=
  Classical.choose (FinTM2.compileNativeMachine_tame tm inputStack outputStack
    separatorIn zeroIn oneIn separatorOut zeroOut oneOut initialStateCode mainLabelCode)

theorem FinTM2.compileNativeMachine_bitGrowth (tm : Turing.FinTM2)
    (inputStack outputStack separatorIn zeroIn oneIn separatorOut zeroOut oneOut
      initialStateCode mainLabelCode : ℕ) :
    comBitGrowth (FinTM2.compileNativeMachine tm inputStack outputStack separatorIn zeroIn oneIn
      separatorOut zeroOut oneOut initialStateCode mainLabelCode) =
      some (FinTM2.nativeBitGrowth tm inputStack outputStack separatorIn zeroIn oneIn
        separatorOut zeroOut oneOut initialStateCode mainLabelCode) :=
  Classical.choose_spec (FinTM2.compileNativeMachine_tame tm inputStack outputStack
    separatorIn zeroIn oneIn separatorOut zeroOut oneOut initialStateCode mainLabelCode)

end Lax20Proofs.TMToRam
