import Lax20Proofs.TMToRam.ValueBounds

namespace Lax20Proofs.TMToRam

open Lax13Proofs.Imp

attribute [aesop safe apply] Expr.Tame.lit Expr.Tame.var Expr.Tame.get
  Expr.Tame.add Expr.Tame.sub Expr.Tame.div Expr.Tame.mul_lit_right
  Expr.Tame.mul_lit_left Cond.Tame.eq Cond.Tame.lt Com.Tame.skip
  Com.Tame.read Com.Tame.assign Com.Tame.write Com.Tame.store Com.Tame.seq
  Com.Tame.ite Com.Tame.«while»

theorem seqs_tame {cs : List Com} (h : ∀ c ∈ cs, c.Tame) : (seqs cs).Tame := by
  induction cs with
  | nil => simp [seqs]; aesop
  | cons c cs ih =>
      simp only [seqs]
      apply Com.Tame.seq
      · exact h c (by simp)
      · apply ih
        intro d hd
        exact h d (by simp [hd])

theorem tableRead_tame (name target : String) (index : Expr) (hi : index.Tame) :
    (tableRead name target index).Tame := by
  unfold tableRead
  aesop

theorem readHead_tame (k : ℕ) : (readHead k).Tame := by
  unfold readHead
  apply Com.Tame.ite <;> aesop
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro c (rfl | rfl | h) <;> aesop

theorem readHeadAndPop_tame (k : ℕ) : (readHeadAndPop k).Tame := by
  unfold readHeadAndPop
  apply Com.Tame.ite <;> aesop
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro c (rfl | rfl | rfl | h) <;> aesop

theorem compileNumericStmt_tame (q : NumericStmt) (fresh : ℕ) :
    (compileNumericStmt q fresh).com.Tame := by
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
      apply Com.Tame.seq
      · apply tableRead_tame; aesop
      · exact ih (fresh + 1)
  | branch table yes no ihy ihn =>
      simp only [compileNumericStmt]
      apply Com.Tame.seq
      · apply tableRead_tame; aesop
      · apply Com.Tame.ite
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
    (initializeArrayFrom name i values).Tame := by
  induction values generalizing i with
  | nil => simp [initializeArrayFrom]; aesop
  | cons v values ih =>
      simp only [initializeArrayFrom]
      apply Com.Tame.seq
      · aesop
      · exact ih (i + 1)

theorem initializeTables_tame (tables : List (String × List ℕ)) :
    (initializeTables tables).Tame := by
  induction tables with
  | nil => simp [initializeTables, seqs]; aesop
  | cons nv tables ih =>
      rcases nv with ⟨name, values⟩
      simp only [initializeTables, seqs]
      apply Com.Tame.seq
      · simp only [initializeArray]
        exact initializeArrayFrom_tame name 0 values
      · exact ih

theorem compileLabelList_tame (tm : Turing.FinTM2) [Fintype tm.Λ]
    [DecidableEq tm.Λ] (labels : List tm.Λ) (fresh : ℕ) :
    (compileLabelList tm labels fresh).com.Tame := by
  induction labels generalizing fresh with
  | nil => simp [compileLabelList]; aesop
  | cons l labels ih =>
      simp only [compileLabelList]
      apply Com.Tame.ite
      · aesop
      · exact compileNumericStmt_tame _ fresh
      · exact ih (compileNumericStmt (numericStmt tm (tm.m l)
          (FinTM2.generatedBy_main_available tm l)) fresh).nextTable

theorem FinTM2.compileMachine_tame (tm : Turing.FinTM2) :
    (FinTM2.compileMachine tm).Tame := by
  letI := tm.ΛFin
  letI : DecidableEq tm.Λ := Classical.decEq _
  unfold FinTM2.compileMachine FinTM2.compileDispatcher
  apply Com.Tame.seq
  · exact initializeTables_tame _
  · apply Com.Tame.«while»
    · aesop
    · exact compileLabelList_tame tm (FinTM2.labelList tm) 0

theorem appendScratch_tame {code : Expr} (hcode : code.Tame) :
    (appendScratch code).Tame := by
  unfold appendScratch
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro c (rfl | rfl | h) <;> aesop

theorem encodeBitsBody_tame (zeroCode oneCode : ℕ) :
    (encodeBitsBody zeroCode oneCode).Tame := by
  unfold encodeBitsBody
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro c (rfl | rfl | rfl | rfl | h)
  · aesop
  · aesop
  · apply Com.Tame.ite
    · aesop
    · apply appendScratch_tame; aesop
    · apply appendScratch_tame; aesop
  · aesop
  · contradiction

theorem encodeBitsLoop_tame (zeroCode oneCode : ℕ) :
    (encodeBitsLoop zeroCode oneCode).Tame := by
  unfold encodeBitsLoop
  aesop (add safe encodeBitsBody_tame)

theorem encodeInputBody_tame (separatorCode zeroCode oneCode : ℕ) :
    (encodeInputBody separatorCode zeroCode oneCode).Tame := by
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
    (encodeInputLoop separatorCode zeroCode oneCode).Tame := by
  unfold encodeInputLoop
  aesop (add safe encodeInputBody_tame)

theorem encodeNativeInputToScratch_tame (separatorCode zeroCode oneCode : ℕ) :
    (encodeNativeInputToScratch separatorCode zeroCode oneCode).Tame := by
  unfold encodeNativeInputToScratch
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro c (rfl | rfl | rfl | h)
  · aesop
  · aesop
  · exact encodeInputLoop_tame separatorCode zeroCode oneCode
  · contradiction

theorem reverseScratchBody_tame (stack : ℕ) : (reverseScratchBody stack).Tame := by
  unfold reverseScratchBody
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro c (rfl | rfl | rfl | rfl | h) <;> aesop

theorem reverseScratchLoop_tame (stack : ℕ) : (reverseScratchLoop stack).Tame := by
  unfold reverseScratchLoop
  aesop (add safe reverseScratchBody_tame)

theorem reverseScratchIntoStack_tame (stack : ℕ) :
    (reverseScratchIntoStack stack).Tame := by
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
    (compileInputCodec inputStack separatorCode zeroCode oneCode
      initialStateCode mainLabelCode).Tame := by
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
    (consumeOutputSymbol separatorCode zeroCode oneCode).Tame := by
  unfold consumeOutputSymbol
  apply Com.Tame.ite
  · aesop
  · apply seqs_tame
    simp only [List.mem_cons, List.mem_singleton]
    rintro c (rfl | rfl | rfl | rfl | h)
    · aesop
    · aesop
    · aesop
    · aesop
    · contradiction
  · apply Com.Tame.ite
    · aesop
    · aesop
    · apply seqs_tame
      simp only [List.mem_cons, List.mem_singleton]
      rintro c (rfl | rfl | h) <;> aesop

theorem compileOutputCodec_tame (outputStack separatorCode zeroCode oneCode : ℕ) :
    (compileOutputCodec outputStack separatorCode zeroCode oneCode).Tame := by
  unfold compileOutputCodec
  apply seqs_tame
  simp only [List.mem_cons, List.mem_singleton]
  rintro c (rfl | rfl | rfl | rfl | rfl | rfl | h)
  · aesop
  · aesop
  · aesop
  · aesop
  · apply Com.Tame.«while»
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
    (FinTM2.compileNativeMachine tm inputStack outputStack separatorIn zeroIn oneIn
      separatorOut zeroOut oneOut initialStateCode mainLabelCode).Tame := by
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
    (FinTM2.compileNativeMachine tm inputStack outputStack separatorIn zeroIn oneIn
      separatorOut zeroOut oneOut initialStateCode mainLabelCode).bitGrowth =
      some (FinTM2.nativeBitGrowth tm inputStack outputStack separatorIn zeroIn oneIn
        separatorOut zeroOut oneOut initialStateCode mainLabelCode) :=
  Classical.choose_spec (FinTM2.compileNativeMachine_tame tm inputStack outputStack
    separatorIn zeroIn oneIn separatorOut zeroOut oneOut initialStateCode mainLabelCode)

end Lax20Proofs.TMToRam
