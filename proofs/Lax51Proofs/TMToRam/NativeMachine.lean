import Lax51Proofs.TMToRam.OutputCompiler

namespace Lax51Proofs.TMToRam

open Lax13Proofs.Imp

theorem compileNumericStmt_noWrite (q : NumericStmt) (fresh : ℕ) :
    (compileNumericStmt q fresh).com.NoWrite := by
  induction q generalizing fresh with
  | push k table next ih =>
      simp [compileNumericStmt, seqs, tableRead, Com.NoWrite, ih]
  | peek k width table next ih =>
      simp [compileNumericStmt, seqs, tableRead, readHead, Com.NoWrite, ih]
  | pop k width table next ih =>
      simp [compileNumericStmt, seqs, tableRead, readHeadAndPop,
        Com.NoWrite, ih]
  | load table next ih =>
      simp [compileNumericStmt, seqs, tableRead, Com.NoWrite, ih]
  | branch table yes no ihYes ihNo =>
      simp [compileNumericStmt, tableRead, Com.NoWrite, ihYes, ihNo]
  | goto table | halt =>
      simp [compileNumericStmt, seqs, tableRead, Com.NoWrite]

theorem compileLabelList_noWrite (tm : Turing.FinTM2) [Fintype tm.Λ]
    [DecidableEq tm.Λ] (labels : List tm.Λ) (fresh : ℕ) :
    (compileLabelList tm labels fresh).com.NoWrite := by
  induction labels generalizing fresh with
  | nil => simp [compileLabelList, Com.NoWrite]
  | cons l labels ih =>
      simp [compileLabelList, Com.NoWrite, compileNumericStmt_noWrite, ih]

theorem initializeArrayFrom_noWrite (name : String) (i : ℕ)
    (values : List ℕ) : (initializeArrayFrom name i values).NoWrite := by
  induction values generalizing i with
  | nil => simp [initializeArrayFrom, Com.NoWrite]
  | cons v values ih => simp [initializeArrayFrom, Com.NoWrite, ih]

theorem initializeTables_noWrite (tables : List (String × List ℕ)) :
    (initializeTables tables).NoWrite := by
  induction tables with
  | nil => simp [initializeTables, seqs, Com.NoWrite]
  | cons nv tables ih =>
      rcases nv with ⟨name, values⟩
      change (initializeArray name values).NoWrite ∧
        (initializeTables tables).NoWrite
      exact ⟨by
        simp [initializeArray, initializeArrayFrom_noWrite], ih⟩

theorem FinTM2.compileMachine_noWrite (tm : Turing.FinTM2) :
    (FinTM2.compileMachine tm).NoWrite := by
  letI := tm.ΛFin
  letI : DecidableEq tm.Λ := Classical.decEq _
  simp [FinTM2.compileMachine, FinTM2.compileDispatcher, FinTM2.labelList,
    Com.NoWrite, initializeTables_noWrite, compileLabelList_noWrite]

noncomputable def baseArrayLength (capacity : ℕ → ℕ) (scratchCapacity : ℕ)
    (name : String) : ℕ := by
  classical
  exact if name = scratchName then scratchCapacity
    else if h : ∃ j, name = stackName j then capacity (Nat.find h) else 0

theorem baseArrayLength_stack (capacity : ℕ → ℕ) (scratchCapacity j : ℕ) :
    baseArrayLength capacity scratchCapacity (stackName j) = capacity j := by
  classical
  unfold baseArrayLength
  rw [if_neg (scratchName_ne_stackName j).symm]
  let h : ∃ i, stackName j = stackName i := ⟨j, rfl⟩
  rw [dif_pos h]
  have hfind := Nat.find_spec h
  have := stackName_injective hfind.symm
  rw [this]

def installArrayLengths : List (String × List ℕ) →
    (String → ℕ) → String → ℕ
  | [], base => base
  | (name, values) :: tables, base =>
      Function.update (installArrayLengths tables base) name values.length

theorem installArrayLengths_mem (tables : List (String × List ℕ))
    (hpair : List.Pairwise (fun a b => a.1 ≠ b.1) tables)
    (base : String → ℕ) (name : String) (values : List ℕ)
    (hm : (name, values) ∈ tables) :
    installArrayLengths tables base name = values.length := by
  induction tables with
  | nil => simp at hm
  | cons entry tables ih =>
      rcases entry with ⟨headName, headValues⟩
      rw [List.pairwise_cons] at hpair
      simp only [List.mem_cons] at hm
      rcases hm with hhead | htail
      · injection hhead with hn hv
        subst name
        subst values
        simp [installArrayLengths]
      · have hne : name ≠ headName := by
          intro heq
          subst name
          exact hpair.1 (headName, values) htail rfl
        simp [installArrayLengths, Function.update, hne,
          ih hpair.2 htail]

theorem installArrayLengths_of_not_mem_names
    (tables : List (String × List ℕ)) (base : String → ℕ) (name : String)
    (hne : ∀ values, (name, values) ∉ tables) :
    installArrayLengths tables base name = base name := by
  induction tables with
  | nil => rfl
  | cons entry tables ih =>
      rcases entry with ⟨headName, headValues⟩
      have hhead : name ≠ headName := by
        intro heq
        subst name
        exact hne headValues (by simp)
      simp [installArrayLengths, Function.update, hhead,
        ih (fun values hm => hne values (by simp [hm]))]

theorem FinTM2.encodeWordCodes_eq_initialCodeStack (tm : Turing.FinTM2)
    (inputAlphabet : tm.Γ tm.k₀ ≃ Lax51.BinaryWordEncoding.Symbol)
    (x : List ℕ) :
    let input := List.map inputAlphabet.invFun
      (Lax51.BinaryWordEncoding.encode x)
    let hinput := FinTM2.initList_stacksWithin tm input
    encodeWordCodes
        (FinTM2.inputSymbolCode tm inputAlphabet .separator)
        (FinTM2.inputSymbolCode tm inputAlphabet .zero)
        (FinTM2.inputSymbolCode tm inputAlphabet .one) x =
      FinTM2.codeStack tm tm.k₀ input
        (fun a ha => hinput tm.k₀ a (by simpa [Turing.initList] using ha)) := by
  dsimp
  rw [encodeWordCodes_eq_inputSymbolCodes]
  symm
  apply FinTM2.codeStack_map_inputAlphabet

/-- The native input prelude establishes the full numeric representation of
the initial typed TM configuration, including every empty non-input stack. -/
theorem FinTM2.compileInputCodec_initialRep (tm : Turing.FinTM2)
    (inputAlphabet : tm.Γ tm.k₀ ≃ Lax51.BinaryWordEncoding.Symbol)
    (capacity : ℕ → ℕ) (ext : String → ℕ) (x : List ℕ)
    (hstackLengths : ∀ j, ext (stackName j) = capacity j)
    (hscratch : (Lax51.BinaryWordEncoding.encode x).length ≤ ext scratchName)
    (hinputCapacity : (Lax51.BinaryWordEncoding.encode x).length ≤
      capacity (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₀)) :
    ∃ σ' cost,
      BigStep (compileInputCodec
        (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₀)
        (FinTM2.inputSymbolCode tm inputAlphabet .separator)
        (FinTM2.inputSymbolCode tm inputAlphabet .zero)
        (FinTM2.inputSymbolCode tm inputAlphabet .one)
        (@finCode tm.σ tm.σFin (Classical.decEq tm.σ) tm.initialState)
        (@finCode tm.Λ tm.ΛFin (Classical.decEq tm.Λ) tm.main))
        (initEnv ext (x.length :: x)) σ' cost ∧
      cost = encodeInputLoopCost x +
        19 * (Lax51.BinaryWordEncoding.encode x).length + 18 ∧
      NumericRep σ' capacity
        (FinTM2.encodeNumericState tm
          (Turing.initList tm (List.map inputAlphabet.invFun
            (Lax51.BinaryWordEncoding.encode x)))
          (FinTM2.initList_stacksWithin tm
            (List.map inputAlphabet.invFun
              (Lax51.BinaryWordEncoding.encode x)))) := by
  let input := List.map inputAlphabet.invFun
    (Lax51.BinaryWordEncoding.encode x)
  let hc := FinTM2.initList_stacksWithin tm input
  let inputStack := @finCode tm.K tm.kFin tm.kDecidableEq tm.k₀
  let separatorCode := FinTM2.inputSymbolCode tm inputAlphabet
    Lax51.BinaryWordEncoding.Symbol.separator
  let zeroCode := FinTM2.inputSymbolCode tm inputAlphabet
    Lax51.BinaryWordEncoding.Symbol.zero
  let oneCode := FinTM2.inputSymbolCode tm inputAlphabet
    Lax51.BinaryWordEncoding.Symbol.one
  let codes := encodeWordCodes separatorCode zeroCode oneCode x
  have hcodesLength : codes.length =
      (Lax51.BinaryWordEncoding.encode x).length := by
    dsimp [codes, separatorCode, zeroCode, oneCode]
    rw [encodeWordCodes_eq_inputSymbolCodes]
    simp
  have hscratch' : codes.length ≤
      ((initEnv ext (x.length :: x)).arrs scratchName).length := by
    simp [initEnv, hcodesLength, hscratch]
  have hstack' : codes.length ≤
      ((initEnv ext (x.length :: x)).arrs (stackName inputStack)).length := by
    simp [initEnv, hstackLengths, hcodesLength, inputStack, hinputCapacity]
  obtain ⟨σ', cost, hrun, hcost, hinp, hstate, hlabel, htop, hprefix⟩ :=
    compileInputCodec_correct inputStack separatorCode zeroCode oneCode
      (@finCode tm.σ tm.σFin (Classical.decEq tm.σ) tm.initialState)
      (@finCode tm.Λ tm.ΛFin (Classical.decEq tm.Λ) tm.main)
      (initEnv ext (x.length :: x)) x rfl hscratch' hstack'
  refine ⟨σ', cost, by simpa [inputStack, separatorCode, zeroCode, oneCode]
      using hrun, ?_, ?_⟩
  · rw [hcost, hcodesLength]
  · change NumericRep σ' capacity
      (FinTM2.encodeNumericState tm (Turing.initList tm input) hc)
    refine ⟨?_, ?_, ?_⟩
    · simpa [FinTM2.encodeNumericState, Turing.initList] using hstate
    · simpa [FinTM2.encodeNumericState, Turing.initList] using hlabel
    · intro j
      have harrLength : (σ'.arrs (stackName j)).length = capacity j := by
        rw [BigStep.arr_length_eq hrun (stackName j)]
        simp [initEnv, hstackLengths]
      by_cases hj : j = inputStack
      · subst j
        have hcodeStack :
            (FinTM2.encodeNumericState tm (Turing.initList tm input) hc).stackData
                inputStack = codes := by
          dsimp [inputStack]
          rw [FinTM2.encodeNumericState_stack]
          simpa [input, hc, codes, separatorCode, zeroCode, oneCode,
            Turing.initList] using
            (FinTM2.encodeWordCodes_eq_initialCodeStack tm inputAlphabet x).symm
        rw [hcodeStack]
        exact ⟨htop, harrLength, hprefix⟩
      · have htarget :
            (FinTM2.encodeNumericState tm (Turing.initList tm input) hc).stackData
                j = [] := by
          simp only [FinTM2.encodeNumericState, FinTM2.codeStackFamily]
          split
          · rfl
          · rename_i k hdecode
            have hkcode : @finCode tm.K tm.kFin tm.kDecidableEq k = j :=
              @finCode_of_finDecode_eq_some tm.K tm.kFin tm.kDecidableEq
                j k hdecode
            have hk : k ≠ tm.k₀ := by
              intro heq
              subst k
              exact hj hkcode.symm
            simp [Turing.initList, hk]
        rw [htarget]
        refine ⟨?_, harrLength, by simp⟩
        rw [hrun.vars_eq]
        · simp [initEnv]
        · simp [compileInputCodec, encodeNativeInputToScratch, encodeInputLoop,
            encodeInputBody, encodeBitsLoop, encodeBitsBody, appendScratch,
            reverseScratchIntoStack, reverseScratchLoop, reverseScratchBody,
            seqs, Com.wvars, hj, topName_injective.eq_iff,
            topName_ne_inputCountVar, topName_ne_inputValueVar,
            topName_ne_inputHalfVar, topName_ne_inputBitVar,
            topName_ne_encodedLengthVar, topName_ne_copyIndexVar,
            topName_ne_ioValueVar, (stateVar_ne_topName j).symm,
            (labelVar_ne_topName j).symm]

/-- Full native-tape IMP+ execution for a supplied safe typed run. -/
theorem FinTM2.compileNativeMachine_safeRun (tm : Turing.FinTM2)
    (inputAlphabet : tm.Γ tm.k₀ ≃ Lax51.BinaryWordEncoding.Symbol)
    (outputAlphabet : tm.Γ tm.k₁ ≃ Lax51.BinaryWordEncoding.Symbol)
    (x y : List ℕ) (capacity : ℕ → ℕ) (ext : String → ℕ)
    (hrun : SafeRun tm capacity
      (Turing.initList tm (List.map inputAlphabet.invFun
        (Lax51.BinaryWordEncoding.encode x)))
      (Turing.haltList tm (List.map outputAlphabet.invFun
        (Lax51.BinaryWordEncoding.encode y))))
    (hstackLengths : ∀ j, ext (stackName j) = capacity j)
    (hscratch : (Lax51.BinaryWordEncoding.encode x).length ≤ ext scratchName)
    (hinputCapacity : (Lax51.BinaryWordEncoding.encode x).length ≤
      capacity (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₀))
    (htableLengths : ∀ name values,
      (name, values) ∈ (FinTM2.compileDispatcher tm 0).tables →
      ext name = values.length) :
    ∃ σ' cost,
      BigStep (FinTM2.compileNativeMachine tm
        (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₀)
        (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₁)
        (FinTM2.inputSymbolCode tm inputAlphabet .separator)
        (FinTM2.inputSymbolCode tm inputAlphabet .zero)
        (FinTM2.inputSymbolCode tm inputAlphabet .one)
        (FinTM2.outputSymbolCode tm outputAlphabet .separator)
        (FinTM2.outputSymbolCode tm outputAlphabet .zero)
        (FinTM2.outputSymbolCode tm outputAlphabet .one)
        (@finCode tm.σ tm.σFin (Classical.decEq tm.σ) tm.initialState)
        (@finCode tm.Λ tm.ΛFin (Classical.decEq tm.Λ) tm.main))
        (initEnv ext (x.length :: x)) σ' cost ∧
      cost ≤
        (encodeInputLoopCost x +
          19 * (Lax51.BinaryWordEncoding.encode x).length + 18) +
        (initializeTablesCost (FinTM2.compileDispatcher tm 0).tables +
          (1 + Cond.size (.lt (.lit 0) (.var labelVar)) +
            maxCost (FinTM2.compileDispatcher tm 0).com) * hrun.steps +
          (1 + Cond.size (.lt (.lit 0) (.var labelVar)))) +
        (29 * (Lax51.BinaryWordEncoding.encode y).length + 19) + 1 ∧
      σ'.out = y := by
  letI := tm.ΛFin
  letI : DecidableEq tm.Λ := Classical.decEq _
  let input := List.map inputAlphabet.invFun
    (Lax51.BinaryWordEncoding.encode x)
  let output := List.map outputAlphabet.invFun
    (Lax51.BinaryWordEncoding.encode y)
  let hc := FinTM2.initList_stacksWithin tm input
  obtain ⟨σ₁, preCost, hpre, hpreCost, hpreRep⟩ :=
    FinTM2.compileInputCodec_initialRep tm inputAlphabet capacity ext x
      hstackLengths hscratch hinputCapacity
  have hzero : ∀ name values,
      (name, values) ∈ (FinTM2.compileDispatcher tm 0).tables →
      σ₁.arrs name = List.replicate values.length 0 := by
    intro name values hm
    have hname := compileLabelList_tables_name tm (FinTM2.labelList tm) 0
      name values (by simpa [FinTM2.compileDispatcher] using hm)
    obtain ⟨i, rfl⟩ := hname
    rw [hpre.arrs_eq]
    · simp [initEnv, htableLengths (tableName i) values hm]
    · simp [compileInputCodec, encodeNativeInputToScratch, encodeInputLoop,
        encodeInputBody, encodeBitsLoop, encodeBitsBody, appendScratch,
        reverseScratchIntoStack, reverseScratchLoop, reverseScratchBody,
        seqs, Com.warrs, (scratchName_ne_tableName i).symm,
        (stackName_ne_tableName _ i).symm]
  obtain ⟨σ₂, coreCost, hcore, hcoreCost, hfinal, hfinalRep, htables⟩ :=
    FinTM2.compileMachine_safeRun tm capacity
      (Turing.initList tm input) (Turing.haltList tm output) hc hrun σ₁
      (by simpa [input, hc] using hpreRep) hzero
  have hcoreOut : σ₂.out = [] := by
    rw [hcore.out_eq]
    · rw [hpre.out_eq]
      · rfl
      · simp [compileInputCodec, encodeNativeInputToScratch, encodeInputLoop,
          encodeInputBody, encodeBitsLoop, encodeBitsBody, appendScratch,
          reverseScratchIntoStack, reverseScratchLoop, reverseScratchBody,
          seqs, Com.NoWrite]
    · exact FinTM2.compileMachine_noWrite tm
  obtain ⟨σ₃, outCost, houtRun, houtCost, houtput⟩ :=
    FinTM2.compileOutputCodec_haltList tm outputAlphabet y σ₂ capacity
      (by simpa [output] using hfinal)
      (by simpa [output] using hfinalRep) hcoreOut
  have hall := BigStep.seq hpre (BigStep.seq hcore
    (BigStep.seq houtRun (BigStep.skip (σ := σ₃))))
  refine ⟨σ₃, preCost + coreCost + outCost + 1, ?_, ?_, houtput⟩
  · simpa only [FinTM2.compileNativeMachine, seqs, Nat.add_assoc] using hall
  · rw [hpreCost]
    omega

/-- A bounded typed TM execution yields a complete native IMP+ execution;
all array extents are constructed internally. -/
theorem FinTM2.compileNativeMachine_outputsInTime (tm : Turing.FinTM2)
    (inputAlphabet : tm.Γ tm.k₀ ≃ Lax51.BinaryWordEncoding.Symbol)
    (outputAlphabet : tm.Γ tm.k₁ ≃ Lax51.BinaryWordEncoding.Symbol)
    (x y : List ℕ) (bound : ℕ)
    (hrun : Turing.TM2OutputsInTime tm
      (List.map inputAlphabet.invFun (Lax51.BinaryWordEncoding.encode x))
      (some (List.map outputAlphabet.invFun
        (Lax51.BinaryWordEncoding.encode y))) bound) :
    ∃ ext σ' cost,
      BigStep (FinTM2.compileNativeMachine tm
        (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₀)
        (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₁)
        (FinTM2.inputSymbolCode tm inputAlphabet .separator)
        (FinTM2.inputSymbolCode tm inputAlphabet .zero)
        (FinTM2.inputSymbolCode tm inputAlphabet .one)
        (FinTM2.outputSymbolCode tm outputAlphabet .separator)
        (FinTM2.outputSymbolCode tm outputAlphabet .zero)
        (FinTM2.outputSymbolCode tm outputAlphabet .one)
        (@finCode tm.σ tm.σFin (Classical.decEq tm.σ) tm.initialState)
        (@finCode tm.Λ tm.ΛFin (Classical.decEq tm.Λ) tm.main))
        (initEnv ext (x.length :: x)) σ' cost ∧
      cost ≤
        (encodeInputLoopCost x +
          19 * (Lax51.BinaryWordEncoding.encode x).length + 18) +
        (initializeTablesCost (FinTM2.compileDispatcher tm 0).tables +
          (1 + Cond.size (.lt (.lit 0) (.var labelVar)) +
            maxCost (FinTM2.compileDispatcher tm 0).com) * bound +
          (1 + Cond.size (.lt (.lit 0) (.var labelVar)))) +
        (29 * (Lax51.BinaryWordEncoding.encode y).length + 19) + 1 ∧
      σ'.out = y := by
  letI := tm.ΛFin
  letI : DecidableEq tm.Λ := Classical.decEq _
  let input := List.map inputAlphabet.invFun
    (Lax51.BinaryWordEncoding.encode x)
  let output := List.map outputAlphabet.invFun
    (Lax51.BinaryWordEncoding.encode y)
  let witness := FinTM2.safeRunWitness_of_outputsInTime tm input output bound hrun
  let tables := (FinTM2.compileDispatcher tm 0).tables
  let base := baseArrayLength witness.capacity
    (Lax51.BinaryWordEncoding.encode x).length
  let ext := installArrayLengths tables base
  have hpair : List.Pairwise (fun a b => a.1 ≠ b.1) tables := by
    simpa [tables] using FinTM2.compileDispatcher_tables_pairwise tm 0
  have htableLengths : ∀ name values, (name, values) ∈ tables →
      ext name = values.length := by
    intro name values hm
    exact installArrayLengths_mem tables hpair base name values hm
  have hstackLengths : ∀ j, ext (stackName j) = witness.capacity j := by
    intro j
    rw [show ext (stackName j) = base (stackName j) by
      apply installArrayLengths_of_not_mem_names
      intro values hm
      have hname := compileLabelList_tables_name tm (FinTM2.labelList tm) 0
        (stackName j) values (by simpa [tables, FinTM2.compileDispatcher] using hm)
      obtain ⟨i, hi⟩ := hname
      exact stackName_ne_tableName j i hi]
    exact baseArrayLength_stack witness.capacity
      (Lax51.BinaryWordEncoding.encode x).length j
  have hscratch : (Lax51.BinaryWordEncoding.encode x).length ≤
      ext scratchName := by
    rw [show ext scratchName = base scratchName by
      apply installArrayLengths_of_not_mem_names
      intro values hm
      have hname := compileLabelList_tables_name tm (FinTM2.labelList tm) 0
        scratchName values (by simpa [tables, FinTM2.compileDispatcher] using hm)
      obtain ⟨i, hi⟩ := hname
      exact scratchName_ne_tableName i hi]
    simp [base, baseArrayLength]
  have hinputCapacity : (Lax51.BinaryWordEncoding.encode x).length ≤
      witness.capacity (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₀) := by
    have hinputLength : input.length =
        (Lax51.BinaryWordEncoding.encode x).length := by simp [input]
    rw [← hinputLength]
    change input.length ≤ witness.capacity
      (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₀)
    change input.length ≤
      FinTM2.traceCapacity tm (Turing.initList tm input) hrun.steps
        (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₀)
    rw [FinTM2.traceCapacity_finCode]
    simp [Turing.initList]
  obtain ⟨σ', cost, hbig, hcost, hout⟩ :=
    FinTM2.compileNativeMachine_safeRun tm inputAlphabet outputAlphabet x y
      witness.capacity ext witness.run hstackLengths hscratch hinputCapacity
      (by simpa [tables] using htableLengths)
  refine ⟨ext, σ', cost, hbig, ?_, hout⟩
  rw [witness.run_steps] at hcost
  have hsteps := witness.steps_le
  have hmul := Nat.mul_le_mul_left
    (1 + Cond.size (.lt (.lit 0) (.var labelVar)) +
      maxCost (FinTM2.compileDispatcher tm 0).com) hsteps
  omega

end Lax51Proofs.TMToRam
