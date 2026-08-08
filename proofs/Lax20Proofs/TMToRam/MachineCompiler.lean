import Lax20Proofs.TMToRam.ImpSimulation
import Lax20Proofs.TMToRam.NumericMachine

/-!
Assembly of the per-statement compiler into a uniform interpreter for one
fixed finite TM2.  The generated dispatcher tests the encoded label and runs
the corresponding compiled statement.  Its enclosing loop stops precisely
when the zero/`none` label is reached.
-/

namespace Lax20Proofs.TMToRam

open Turing
open Lax13Proofs.Imp

theorem tableName_injective : Function.Injective tableName := by
  intro i j h
  have hdigits : Nat.toDigits 10 i = Nat.toDigits 10 j := by
    have hlists := congrArg String.toList h
    simpa [tableName, Nat.toString_eq_ofList_toDigits] using hlists
  calc
    i = Nat.ofDigitChars 10 (Nat.toDigits 10 i) 0 :=
      Nat.ofDigitChars_ten_toDigits.symm
    _ = Nat.ofDigitChars 10 (Nat.toDigits 10 j) 0 := by rw [hdigits]
    _ = j := Nat.ofDigitChars_ten_toDigits

private theorem allocation_cons (fresh nextTable : ℕ) (table : List ℕ)
    (tables : List (String × List ℕ))
    (hnext : fresh + 1 ≤ nextTable)
    (hrange : ∀ name values, (name, values) ∈ tables →
      ∃ i, name = tableName i ∧ fresh + 1 ≤ i ∧ i < nextTable)
    (hpair : List.Pairwise (fun a b => a.1 ≠ b.1) tables) :
    fresh ≤ nextTable ∧
      (∀ name values, (name, values) ∈ (tableName fresh, table) :: tables →
        ∃ i, name = tableName i ∧ fresh ≤ i ∧ i < nextTable) ∧
      List.Pairwise (fun a b => a.1 ≠ b.1)
        ((tableName fresh, table) :: tables) := by
  refine ⟨(Nat.le_add_right fresh 1).trans hnext, ?_, ?_⟩
  · intro name values hm
    rcases List.mem_cons.mp hm with h | h
    · cases h
      exact ⟨fresh, rfl, Nat.le_refl _, lt_of_lt_of_le (Nat.lt_succ_self _) hnext⟩
    · obtain ⟨i, rfl, hlo, hhi⟩ := hrange name values h
      exact ⟨i, rfl, (Nat.le_add_right fresh 1).trans hlo, hhi⟩
  · rw [List.pairwise_cons]
    refine ⟨?_, hpair⟩
    intro entry he
    obtain ⟨i, hname, hlo, _⟩ := hrange entry.1 entry.2 he
    rw [hname]
    intro heq
    have := tableName_injective heq
    omega

/-- Every literal table allocated by a statement occupies a fresh numeric
identifier in the half-open interval returned by the compiler. -/
theorem compileNumericStmt_allocation (q : NumericStmt) (fresh : ℕ) :
    fresh ≤ (compileNumericStmt q fresh).nextTable ∧
    (∀ name values, (name, values) ∈ (compileNumericStmt q fresh).tables →
      ∃ i, name = tableName i ∧ fresh ≤ i ∧
        i < (compileNumericStmt q fresh).nextTable) ∧
    List.Pairwise (fun a b => a.1 ≠ b.1)
      (compileNumericStmt q fresh).tables := by
  induction q generalizing fresh with
  | halt => simp [compileNumericStmt]
  | goto table =>
      refine ⟨by simp [compileNumericStmt], ?_, by simp [compileNumericStmt]⟩
      intro name values hm
      have h : (name, values) = (tableName fresh, table) := by
        simpa [compileNumericStmt] using hm
      cases h
      exact ⟨fresh, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩
  | push k table next ih =>
      obtain ⟨hnext, hrange, hpair⟩ := ih (fresh + 1)
      simpa [compileNumericStmt] using
        allocation_cons fresh (compileNumericStmt next (fresh + 1)).nextTable
          table (compileNumericStmt next (fresh + 1)).tables hnext hrange hpair
  | peek k width table next ih =>
      obtain ⟨hnext, hrange, hpair⟩ := ih (fresh + 1)
      simpa [compileNumericStmt] using
        allocation_cons fresh (compileNumericStmt next (fresh + 1)).nextTable
          table (compileNumericStmt next (fresh + 1)).tables hnext hrange hpair
  | pop k width table next ih =>
      obtain ⟨hnext, hrange, hpair⟩ := ih (fresh + 1)
      simpa [compileNumericStmt] using
        allocation_cons fresh (compileNumericStmt next (fresh + 1)).nextTable
          table (compileNumericStmt next (fresh + 1)).tables hnext hrange hpair
  | load table next ih =>
      obtain ⟨hnext, hrange, hpair⟩ := ih (fresh + 1)
      simpa [compileNumericStmt] using
        allocation_cons fresh (compileNumericStmt next (fresh + 1)).nextTable
          table (compileNumericStmt next (fresh + 1)).tables hnext hrange hpair
  | branch table yes no ihy ihn =>
      obtain ⟨hyNext, hyRange, hyPair⟩ := ihy (fresh + 1)
      obtain ⟨hnNext, hnRange, hnPair⟩ :=
        ihn (compileNumericStmt yes (fresh + 1)).nextTable
      simp only [compileNumericStmt]
      refine ⟨Nat.le_trans (Nat.le_add_right fresh 1) (hyNext.trans hnNext), ?_, ?_⟩
      · intro name values hm
        rcases List.mem_cons.mp hm with h | h
        · cases h
          exact ⟨fresh, rfl, Nat.le_refl _,
            lt_of_lt_of_le (Nat.lt_succ_self _) (hyNext.trans hnNext)⟩
        · rcases List.mem_append.mp h with h | h
          · obtain ⟨i, rfl, hlo, hhi⟩ := hyRange name values h
            exact ⟨i, rfl, hlo.trans' (Nat.le_add_right fresh 1), hhi.trans_le hnNext⟩
          · obtain ⟨i, rfl, hlo, hhi⟩ := hnRange name values h
            exact ⟨i, rfl,
              (Nat.le_add_right fresh 1).trans (hyNext.trans hlo), hhi⟩
      · rw [List.pairwise_cons]
        refine ⟨?_, ?_⟩
        · intro entry he
          rcases List.mem_append.mp he with he | he
          · obtain ⟨i, hname, hlo, _⟩ := hyRange entry.1 entry.2 he
            rw [hname]
            intro heq
            have := tableName_injective heq
            omega
          · obtain ⟨i, hname, hlo, _⟩ := hnRange entry.1 entry.2 he
            rw [hname]
            intro heq
            have := tableName_injective heq
            omega
        · rw [List.pairwise_append]
          refine ⟨hyPair, hnPair, ?_⟩
          intro a ha b hb
          obtain ⟨i, hai, _, hi⟩ := hyRange a.1 a.2 ha
          obtain ⟨j, hbj, hj, _⟩ := hnRange b.1 b.2 hb
          rw [hai, hbj]
          intro heq
          have := tableName_injective heq
          omega

/-- Commands without an internal loop have a syntax-determined cost bound. -/
def LoopFree : Com → Prop
  | .skip | .assign _ _ | .store _ _ _ | .read _ | .write _ => True
  | .seq c d => LoopFree c ∧ LoopFree d
  | .ite _ c d => LoopFree c ∧ LoopFree d
  | .while _ _ => False

def maxCost : Com → ℕ
  | .skip => 1
  | .assign _ e => 1 + e.size
  | .store _ i e => 1 + i.size + e.size
  | .seq c d => maxCost c + maxCost d
  | .ite b c d => 1 + b.size + max (maxCost c) (maxCost d)
  | .while _ _ => 0
  | .read _ => 1
  | .write e => 1 + e.size

theorem BigStep.cost_le_maxCost {com : Com} {σ σ' : Env} {cost : ℕ}
    (hrun : BigStep com σ σ' cost) (hfree : LoopFree com) :
    cost ≤ maxCost com := by
  induction hrun with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => rfl
  | seq _ _ ih₁ ih₂ =>
      exact Nat.add_le_add (ih₁ hfree.1) (ih₂ hfree.2)
  | ite_true _ _ ih =>
      simp only [LoopFree] at hfree
      simp only [maxCost]
      have hk := ih hfree.1
      exact Nat.add_le_add_left (hk.trans (Nat.le_max_left _ _)) _
  | ite_false _ _ ih =>
      simp only [LoopFree] at hfree
      simp only [maxCost]
      have hk := ih hfree.2
      exact Nat.add_le_add_left (hk.trans (Nat.le_max_right _ _)) _
  | while_true => simp [LoopFree] at hfree
  | while_false => simp [LoopFree] at hfree
  | read _ => rfl
  | write _ => rfl

/-- Compile a finite list of labelled statements into a linear dispatcher. -/
noncomputable def compileLabelList (tm : FinTM2) [Fintype tm.Λ]
    [DecidableEq tm.Λ] : List tm.Λ → ℕ → StmtCompilation
  | [], fresh =>
      { com := .assign labelVar (.lit 0), tables := [], nextTable := fresh }
  | l :: ls, fresh =>
      let current := compileNumericStmt
        (numericStmt tm (tm.m l) (FinTM2.generatedBy_main_available tm l)) fresh
      let rest := compileLabelList tm ls current.nextTable
      let command := Com.ite (Cond.eq (Expr.var labelVar) (Expr.lit (finCode l + 1)))
        current.com rest.com
      ⟨command, current.tables ++ rest.tables, rest.nextTable⟩

/-- All labels, in the canonical finite enumeration order. -/
noncomputable def FinTM2.labelList (tm : FinTM2) : List tm.Λ := by
  letI := tm.ΛFin
  exact Finset.univ.toList

theorem FinTM2.mem_labelList (tm : FinTM2) (l : tm.Λ) :
    l ∈ FinTM2.labelList tm := by
  letI := tm.ΛFin
  simp [FinTM2.labelList]

/-- The complete finite-control dispatcher. -/
noncomputable def FinTM2.compileDispatcher (tm : FinTM2) (fresh : ℕ := 0) :
    StmtCompilation := by
  letI := tm.ΛFin
  letI : DecidableEq tm.Λ := Classical.decEq _
  exact compileLabelList tm (FinTM2.labelList tm) fresh

theorem compileLabelList_allocation (tm : FinTM2) [Fintype tm.Λ]
    [DecidableEq tm.Λ] (labels : List tm.Λ) (fresh : ℕ) :
    fresh ≤ (compileLabelList tm labels fresh).nextTable ∧
    (∀ name values, (name, values) ∈ (compileLabelList tm labels fresh).tables →
      ∃ i, name = tableName i ∧ fresh ≤ i ∧
        i < (compileLabelList tm labels fresh).nextTable) ∧
    List.Pairwise (fun a b => a.1 ≠ b.1)
      (compileLabelList tm labels fresh).tables := by
  induction labels generalizing fresh with
  | nil => simp [compileLabelList]
  | cons l labels ih =>
      let current := compileNumericStmt
        (numericStmt tm (tm.m l) (FinTM2.generatedBy_main_available tm l)) fresh
      obtain ⟨hcNext, hcRange, hcPair⟩ :=
        compileNumericStmt_allocation
          (numericStmt tm (tm.m l) (FinTM2.generatedBy_main_available tm l)) fresh
      obtain ⟨hrNext, hrRange, hrPair⟩ := ih current.nextTable
      simp only [compileLabelList]
      change fresh ≤ (compileLabelList tm labels current.nextTable).nextTable ∧ _
      refine ⟨hcNext.trans hrNext, ?_, ?_⟩
      · intro name values hm
        rcases List.mem_append.mp hm with hm | hm
        · obtain ⟨i, rfl, hlo, hhi⟩ := hcRange name values hm
          exact ⟨i, rfl, hlo, hhi.trans_le hrNext⟩
        · obtain ⟨i, rfl, hlo, hhi⟩ := hrRange name values hm
          exact ⟨i, rfl, hcNext.trans hlo, hhi⟩
      · rw [List.pairwise_append]
        refine ⟨hcPair, hrPair, ?_⟩
        intro a ha b hb
        obtain ⟨i, hai, _, hi⟩ := hcRange a.1 a.2 ha
        obtain ⟨j, hbj, hj, _⟩ := hrRange b.1 b.2 hb
        change i < current.nextTable at hi
        rw [hai, hbj]
        intro heq
        have := tableName_injective heq
        omega

theorem FinTM2.compileDispatcher_tables_pairwise (tm : FinTM2) (fresh : ℕ) :
    List.Pairwise (fun a b => a.1 ≠ b.1)
      (FinTM2.compileDispatcher tm fresh).tables := by
  letI := tm.ΛFin
  letI : DecidableEq tm.Λ := Classical.decEq _
  exact (compileLabelList_allocation tm (FinTM2.labelList tm) fresh).2.2

/-- The interpreter loop.  Labels use the zero/successor encoding, so a
positive label means that another machine transition must be executed. -/
noncomputable def FinTM2.compileLoop (tm : FinTM2) : Com :=
  .while (.lt (.lit 0) (.var labelVar)) (FinTM2.compileDispatcher tm 0).com

/-- Store a literal list into a preallocated IMP+ array, beginning at an
explicit index.  Keeping the index in the recursion (rather than recovering
it with `zipIdx`) makes the initializer's operational proof structural. -/
def initializeArrayFrom (name : String) : ℕ → List ℕ → Com
  | _, [] => .skip
  | i, v :: values =>
      .seq (.store name (.lit i) (.lit v))
        (initializeArrayFrom name (i + 1) values)

/-- Store a literal list into a preallocated IMP+ array. -/
def initializeArray (name : String) (values : List ℕ) : Com :=
  initializeArrayFrom name 0 values

/-- The mathematical state transformer implemented by
`initializeArrayFrom`. -/
def storeLiterals (name : String) : ℕ → List ℕ → Env → Env
  | _, [], σ => σ
  | i, v :: values, σ =>
      storeLiterals name (i + 1) values (σ.setArr name i v)

theorem initializeArrayFrom_correct (name : String) (i : ℕ)
    (values : List ℕ) (σ : Env)
    (hspace : i + values.length ≤ (σ.arrs name).length) :
    BigStep (initializeArrayFrom name i values) σ
      (storeLiterals name i values σ) (3 * values.length + 1) := by
  induction values generalizing i σ with
  | nil => simpa [initializeArrayFrom, storeLiterals] using (BigStep.skip (σ := σ))
  | cons v values ih =>
      have hi : i < (σ.arrs name).length := by
        simpa using lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos _)) hspace
      have hlen : ((σ.setArr name i v).arrs name).length =
          (σ.arrs name).length := by
        simp [Env.setArr]
      have htail : i + 1 + values.length ≤
          ((σ.setArr name i v).arrs name).length := by
        rw [hlen]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hspace
      have hstore : BigStep (.store name (.lit i) (.lit v)) σ
          (σ.setArr name i v) 3 := by
        simpa [Expr.eval, Expr.size] using
          (BigStep.store (σ := σ) (a := name) (i := .lit i) (e := .lit v)
            (k := i) (v := v) rfl rfl hi)
      have hrest := ih (i + 1) (σ.setArr name i v) htail
      simpa [initializeArrayFrom, storeLiterals, List.length_cons,
        Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        BigStep.seq hstore hrest

private theorem set_prefix_replicate (pre suffix : List ℕ) (v : ℕ)
    (n : ℕ) :
    (pre ++ List.replicate (n + 1) 0 ++ suffix).set pre.length v =
      pre ++ v :: List.replicate n 0 ++ suffix := by
  rw [List.set_eq_take_cons_drop]
  · simp
  · simp

/-- On a zeroed interval, `storeLiterals` replaces precisely that interval
by the supplied literals. -/
theorem storeLiterals_materializes (name : String) (pre suffix values : List ℕ)
    (σ : Env)
    (harr : σ.arrs name =
      pre ++ List.replicate values.length 0 ++ suffix) :
    (storeLiterals name pre.length values σ).arrs name =
      pre ++ values ++ suffix := by
  induction values generalizing pre σ with
  | nil => simpa [storeLiterals] using harr
  | cons v values ih =>
      simp only [List.length_cons] at harr
      have hset : (σ.setArr name pre.length v).arrs name =
          (pre ++ [v]) ++ List.replicate values.length 0 ++ suffix := by
        simp only [Env.setArr, if_pos]
        rw [harr, set_prefix_replicate]
        simp [List.append_assoc]
      simpa [storeLiterals, List.length_cons, List.append_assoc] using
        ih (pre ++ [v]) (σ.setArr name pre.length v) hset

theorem initializeArray_correct (name : String) (values : List ℕ) (σ : Env)
    (harr : σ.arrs name = List.replicate values.length 0) :
    BigStep (initializeArray name values) σ
      (storeLiterals name 0 values σ) (3 * values.length + 1) ∧
    (storeLiterals name 0 values σ).arrs name = values := by
  constructor
  · apply initializeArrayFrom_correct
    simp [harr]
  · simpa using storeLiterals_materializes name [] [] values σ (by simpa using harr)

@[simp] theorem storeLiterals_vars (name : String) (i : ℕ)
    (values : List ℕ) (σ : Env) :
    (storeLiterals name i values σ).vars = σ.vars := by
  induction values generalizing i σ with
  | nil => rfl
  | cons v values ih => simpa [storeLiterals] using ih (i + 1) (σ.setArr name i v)

@[simp] theorem storeLiterals_inp (name : String) (i : ℕ)
    (values : List ℕ) (σ : Env) :
    (storeLiterals name i values σ).inp = σ.inp := by
  induction values generalizing i σ with
  | nil => rfl
  | cons v values ih => simpa [storeLiterals] using ih (i + 1) (σ.setArr name i v)

@[simp] theorem storeLiterals_out (name : String) (i : ℕ)
    (values : List ℕ) (σ : Env) :
    (storeLiterals name i values σ).out = σ.out := by
  induction values generalizing i σ with
  | nil => rfl
  | cons v values ih => simpa [storeLiterals] using ih (i + 1) (σ.setArr name i v)

theorem storeLiterals_arrs_of_ne (name other : String) (hne : other ≠ name)
    (i : ℕ) (values : List ℕ) (σ : Env) :
    (storeLiterals name i values σ).arrs other = σ.arrs other := by
  induction values generalizing i σ with
  | nil => rfl
  | cons v values ih =>
      rw [storeLiterals, ih]
      simp [Env.setArr, hne]

/-- Materialize every table allocated by a statement/machine compilation. -/
def initializeTables (tables : List (String × List ℕ)) : Com :=
  seqs (tables.map fun nv => initializeArray nv.1 nv.2)

/-- State transformer and exact cost of the table-list initializer. -/
def storeTables : List (String × List ℕ) → Env → Env
  | [], σ => σ
  | (name, values) :: tables, σ =>
      storeTables tables (storeLiterals name 0 values σ)

def initializeTablesCost : List (String × List ℕ) → ℕ
  | [] => 1
  | (_, values) :: tables => 3 * values.length + 1 + initializeTablesCost tables

@[simp] theorem storeTables_vars (tables : List (String × List ℕ)) (σ : Env) :
    (storeTables tables σ).vars = σ.vars := by
  induction tables generalizing σ with
  | nil => rfl
  | cons entry tables ih =>
      rcases entry with ⟨name, values⟩
      simpa [storeTables] using ih (storeLiterals name 0 values σ)

@[simp] theorem storeTables_inp (tables : List (String × List ℕ)) (σ : Env) :
    (storeTables tables σ).inp = σ.inp := by
  induction tables generalizing σ with
  | nil => rfl
  | cons entry tables ih =>
      rcases entry with ⟨name, values⟩
      simpa [storeTables] using ih (storeLiterals name 0 values σ)

@[simp] theorem storeTables_out (tables : List (String × List ℕ)) (σ : Env) :
    (storeTables tables σ).out = σ.out := by
  induction tables generalizing σ with
  | nil => rfl
  | cons entry tables ih =>
      rcases entry with ⟨name, values⟩
      simpa [storeTables] using ih (storeLiterals name 0 values σ)

theorem storeTables_arrs_of_not_mem (tables : List (String × List ℕ))
    (σ : Env) (name : String)
    (hname : name ∉ tables.map Prod.fst) :
    (storeTables tables σ).arrs name = σ.arrs name := by
  induction tables generalizing σ with
  | nil => rfl
  | cons entry tables ih =>
      rcases entry with ⟨other, values⟩
      simp only [List.map_cons, List.mem_cons, not_or] at hname
      rw [storeTables, ih (storeLiterals other 0 values σ) hname.2]
      exact storeLiterals_arrs_of_ne other name hname.1 0 values σ

/-- A list of pairwise-distinct literal tables is materialized exactly from
zero-filled arrays of the corresponding sizes. -/
theorem initializeTables_correct (tables : List (String × List ℕ)) (σ : Env)
    (hdistinct : List.Pairwise (fun a b => a.1 ≠ b.1) tables)
    (hzero : ∀ name values, (name, values) ∈ tables →
      σ.arrs name = List.replicate values.length 0) :
    BigStep (initializeTables tables) σ (storeTables tables σ)
        (initializeTablesCost tables) ∧
      TablesRep (storeTables tables σ) tables := by
  induction tables generalizing σ with
  | nil =>
      constructor
      · simpa [initializeTables, initializeTablesCost, seqs, storeTables] using
          (BigStep.skip (σ := σ))
      · simp [TablesRep]
  | cons entry tables ih =>
      rcases entry with ⟨name, values⟩
      simp only [List.pairwise_cons] at hdistinct
      obtain ⟨hfirstRun, hfirstArr⟩ := initializeArray_correct name values σ
        (hzero name values (by simp))
      have hzeroTail : ∀ other vals, (other, vals) ∈ tables →
          (storeLiterals name 0 values σ).arrs other =
            List.replicate vals.length 0 := by
        intro other vals hm
        have hne : other ≠ name := by
          exact (hdistinct.1 (other, vals) hm).symm
        rw [storeLiterals_arrs_of_ne name other hne 0 values σ]
        exact hzero other vals (by simp [hm])
      obtain ⟨htailRun, htailRep⟩ :=
        ih (storeLiterals name 0 values σ) hdistinct.2 hzeroTail
      constructor
      · simpa [initializeTables, initializeTablesCost, seqs, storeTables] using
          BigStep.seq hfirstRun htailRun
      · intro other vals hm
        rcases List.mem_cons.mp hm with hhead | htail
        · have hn : other = name := (Prod.mk.inj hhead).1
          have hv : vals = values := (Prod.mk.inj hhead).2
          subst other
          subst vals
          rw [storeTables, storeTables_arrs_of_not_mem tables
            (storeLiterals name 0 values σ) name]
          · exact hfirstArr
          · intro hmem
            obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
            exact hdistinct.1 entry hentry heq.symm
        · exact htailRep other vals htail

theorem compileNumericStmt_loopFree (q : NumericStmt) (fresh : ℕ) :
    LoopFree (compileNumericStmt q fresh).com := by
  induction q generalizing fresh with
  | push k table next ih =>
      simp [compileNumericStmt, tableRead, seqs, LoopFree, ih]
  | peek k width table next ih =>
      simp [compileNumericStmt, tableRead, readHead, seqs, LoopFree, ih]
  | pop k width table next ih =>
      simp [compileNumericStmt, tableRead, readHeadAndPop, seqs, LoopFree, ih]
  | load table next ih => simp [compileNumericStmt, tableRead, LoopFree, ih]
  | branch table yes no ihy ihn =>
      simp [compileNumericStmt, tableRead, LoopFree, ihy, ihn]
  | goto table => simp [compileNumericStmt, tableRead, seqs, LoopFree]
  | halt => simp [compileNumericStmt, LoopFree]

theorem compileLabelList_loopFree (tm : FinTM2) [Fintype tm.Λ]
    [DecidableEq tm.Λ] (labels : List tm.Λ) (fresh : ℕ) :
    LoopFree (compileLabelList tm labels fresh).com := by
  induction labels generalizing fresh with
  | nil => simp [compileLabelList, LoopFree]
  | cons l labels ih =>
      simp [compileLabelList, LoopFree, compileNumericStmt_loopFree, ih]

theorem FinTM2.compileDispatcher_loopFree (tm : FinTM2) (fresh : ℕ) :
    LoopFree (FinTM2.compileDispatcher tm fresh).com := by
  letI := tm.ΛFin
  letI : DecidableEq tm.Λ := Classical.decEq _
  simpa [FinTM2.compileDispatcher] using
    compileLabelList_loopFree tm (FinTM2.labelList tm) fresh

theorem compileLabelList_tables_name (tm : FinTM2) [Fintype tm.Λ]
    [DecidableEq tm.Λ] (labels : List tm.Λ) (fresh : ℕ)
    (name : String) (values : List ℕ)
    (hm : (name, values) ∈ (compileLabelList tm labels fresh).tables) :
    ∃ i, name = tableName i := by
  induction labels generalizing fresh with
  | nil => simp [compileLabelList] at hm
  | cons l labels ih =>
      simp only [compileLabelList] at hm
      rcases List.mem_append.mp hm with hcur | hrest
      · exact compileNumericStmt_tables_name _ _ _ _ hcur
      · exact ih _ hrest

theorem NumericRep.storeDispatcherTables (tm : FinTM2) (fresh : ℕ)
    {capacity : ℕ → ℕ} {c : NumericMachineState} {σ : Env}
    (hrep : NumericRep σ capacity c) :
    NumericRep
      (storeTables (FinTM2.compileDispatcher tm fresh).tables σ) capacity c := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using hrep.1
  · simpa using hrep.2.1
  · intro k
    have hnot : stackName k ∉
        (FinTM2.compileDispatcher tm fresh).tables.map Prod.fst := by
      intro hm
      obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hm
      obtain ⟨i, hname⟩ := by
        letI := tm.ΛFin
        letI : DecidableEq tm.Λ := Classical.decEq _
        exact compileLabelList_tables_name tm (FinTM2.labelList tm) fresh
          entry.1 entry.2 (by
            simpa [FinTM2.compileDispatcher] using hentry)
      exact stackName_ne_tableName k i (heq.symm.trans hname)
    unfold StackRep
    rw [storeTables_vars,
      storeTables_arrs_of_not_mem _ _ (stackName k) hnot]
    exact hrep.2.2 k

/-- Dispatch only mutates simulated stack arrays, never literal tables. -/
theorem tableName_not_mem_compileLabelList_warrs (tm : FinTM2) [Fintype tm.Λ]
    [DecidableEq tm.Λ] (labels : List tm.Λ) (fresh i : ℕ) :
    tableName i ∉ (compileLabelList tm labels fresh).com.warrs := by
  induction labels generalizing fresh with
  | nil => simp [compileLabelList, Com.warrs]
  | cons l labels ih =>
      simp [compileLabelList, Com.warrs,
        tableName_not_mem_compileNumericStmt_warrs, ih]

theorem TablesRep.preserved_compileLabelList (tm : FinTM2) [Fintype tm.Λ]
    [DecidableEq tm.Λ] {labels : List tm.Λ} {fresh : ℕ}
    {σ σ' : Env} {cost : ℕ}
    (htables : TablesRep σ (compileLabelList tm labels fresh).tables)
    (hrun : BigStep (compileLabelList tm labels fresh).com σ σ' cost) :
    TablesRep σ' (compileLabelList tm labels fresh).tables := by
  intro name values hm
  obtain ⟨i, rfl⟩ := compileLabelList_tables_name tm labels fresh name values hm
  rw [hrun.arrs_eq (tableName_not_mem_compileLabelList_warrs tm labels fresh i)]
  exact htables (tableName i) values hm

/-- Initializer followed by the machine interpreter loop. -/
noncomputable def FinTM2.compileMachine (tm : FinTM2) : Com :=
  let dispatch := FinTM2.compileDispatcher tm 0
  .seq (initializeTables dispatch.tables)
    (.while (.lt (.lit 0) (.var labelVar)) dispatch.com)

/-- The linear dispatcher selects and executes the statement belonging to
the encoded current label. -/
theorem compileLabelList_correct (tm : FinTM2) [Fintype tm.Λ]
    [DecidableEq tm.Λ] (labels : List tm.Λ) (target : tm.Λ) (fresh : ℕ)
    (capacity : ℕ → ℕ) (c : NumericMachineState) (σ : Env)
    (hlabel : c.label = some (finCode target))
    (hmem : target ∈ labels)
    (hrep : NumericRep σ capacity c)
    (htables : TablesRep σ (compileLabelList tm labels fresh).tables)
    (hsafe : SafeExec capacity
      (numericStmt tm (tm.m target)
        (FinTM2.generatedBy_main_available tm target)) c) :
    ∃ σ' cost, BigStep (compileLabelList tm labels fresh).com σ σ' cost ∧
      NumericRep σ' capacity
        ((numericStmt tm (tm.m target)
          (FinTM2.generatedBy_main_available tm target)).exec c) := by
  induction labels generalizing fresh σ with
  | nil => simp at hmem
  | cons l labels ih =>
      let ql := numericStmt tm (tm.m l)
        (FinTM2.generatedBy_main_available tm l)
      let current := compileNumericStmt ql fresh
      let rest := compileLabelList tm labels current.nextTable
      have hvar : σ.vars labelVar = finCode target + 1 := by
        rw [hrep.2.1, hlabel]
        rfl
      by_cases hlt : l = target
      · subst l
        have hcurTables : TablesRep σ current.tables := by
          exact TablesRep.append_left (by
            simpa [compileLabelList, ql, current, rest] using htables)
        obtain ⟨σ', cost, hrun, hfinal⟩ :=
          compileNumericStmt_correct ql fresh capacity c σ hrep hcurTables
            (by simpa [ql] using hsafe)
        refine ⟨σ', 1 + Cond.size
            (.eq (.var labelVar) (.lit (finCode target + 1))) + cost, ?_, ?_⟩
        · simpa [compileLabelList, ql, current, rest] using
            BigStep.ite_true (by simp [Cond.eval, Expr.eval, hvar]) hrun
        · simpa [ql] using hfinal
      · have hmem' : target ∈ labels := by
          rcases List.mem_cons.mp hmem with heq | hm
          · exact False.elim (hlt heq.symm)
          · exact hm
        have hrestTables : TablesRep σ rest.tables := by
          exact TablesRep.append_right (by
            simpa [compileLabelList, ql, current, rest] using htables)
        obtain ⟨σ', cost, hrun, hfinal⟩ :=
          ih current.nextTable σ hmem' hrep
            (by simpa [rest] using hrestTables)
        have hcode : finCode target + 1 ≠ finCode l + 1 := by
          intro h
          apply hlt
          apply finCode_injective
          omega
        have hcode0 : finCode target ≠ finCode l := by
          intro h
          exact hcode (congrArg (· + 1) h)
        refine ⟨σ', 1 + Cond.size
            (.eq (.var labelVar) (.lit (finCode l + 1))) + cost, ?_, hfinal⟩
        simpa [compileLabelList, ql, current, rest] using
          BigStep.ite_false (by simp [Cond.eval, Expr.eval, hvar, hcode0]) hrun

/-- Correctness of the complete dispatcher at any valid machine label. -/
theorem FinTM2.compileDispatcher_correct (tm : FinTM2) (target : tm.Λ)
    (fresh : ℕ) (capacity : ℕ → ℕ) (c : NumericMachineState) (σ : Env)
    (hlabel : c.label = some
      (@finCode tm.Λ tm.ΛFin (Classical.decEq tm.Λ) target))
    (hrep : NumericRep σ capacity c)
    (htables : TablesRep σ (FinTM2.compileDispatcher tm fresh).tables)
    (hsafe : SafeExec capacity
      (numericStmt tm (tm.m target)
        (FinTM2.generatedBy_main_available tm target)) c) :
    ∃ σ' cost,
      BigStep (FinTM2.compileDispatcher tm fresh).com σ σ' cost ∧
      NumericRep σ' capacity
        ((numericStmt tm (tm.m target)
          (FinTM2.generatedBy_main_available tm target)).exec c) := by
  letI := tm.ΛFin
  letI : DecidableEq tm.Λ := Classical.decEq _
  exact compileLabelList_correct tm (FinTM2.labelList tm) target fresh capacity c σ
    hlabel (FinTM2.mem_labelList tm target) hrep
    (by simpa [FinTM2.compileDispatcher] using htables) hsafe

/-- Framed form used by the enclosing interpreter loop: transition tables
remain available for the next dispatch. -/
theorem FinTM2.compileDispatcher_correct_framed (tm : FinTM2) (target : tm.Λ)
    (fresh : ℕ) (capacity : ℕ → ℕ) (c : NumericMachineState) (σ : Env)
    (hlabel : c.label = some
      (@finCode tm.Λ tm.ΛFin (Classical.decEq tm.Λ) target))
    (hrep : NumericRep σ capacity c)
    (htables : TablesRep σ (FinTM2.compileDispatcher tm fresh).tables)
    (hsafe : SafeExec capacity
      (numericStmt tm (tm.m target)
        (FinTM2.generatedBy_main_available tm target)) c) :
    ∃ σ' cost,
      BigStep (FinTM2.compileDispatcher tm fresh).com σ σ' cost ∧
      NumericRep σ' capacity
        ((numericStmt tm (tm.m target)
          (FinTM2.generatedBy_main_available tm target)).exec c) ∧
      TablesRep σ' (FinTM2.compileDispatcher tm fresh).tables := by
  obtain ⟨σ', cost, hrun, hfinal⟩ :=
    FinTM2.compileDispatcher_correct tm target fresh capacity c σ
      hlabel hrep htables hsafe
  refine ⟨σ', cost, hrun, hfinal, ?_⟩
  letI := tm.ΛFin
  letI : DecidableEq tm.Λ := Classical.decEq _
  apply TablesRep.preserved_compileLabelList tm
    (labels := FinTM2.labelList tm) (fresh := fresh)
    (σ := σ) (σ' := σ') (cost := cost)
  · simpa [FinTM2.compileDispatcher] using htables
  · simpa [FinTM2.compileDispatcher] using hrun

/-- On an encoded typed configuration, one dispatcher execution represents
exactly the successor typed configuration. -/
theorem FinTM2.compileDispatcher_encode_step (tm : FinTM2) (l : tm.Λ)
    (s : tm.σ) (S : ∀ k, List (tm.Γ k))
    (hS : StacksWithin (FinTM2.availableSymbols tm) S)
    (fresh : ℕ) (capacity : ℕ → ℕ) (σ : Env)
    (hrep : NumericRep σ capacity
      (FinTM2.encodeNumericState tm ⟨some l, s, S⟩ hS))
    (htables : TablesRep σ (FinTM2.compileDispatcher tm fresh).tables)
    (hsafe : SafeExec capacity
      (numericStmt tm (tm.m l) (FinTM2.generatedBy_main_available tm l))
      (FinTM2.encodeNumericState tm ⟨some l, s, S⟩ hS)) :
    ∃ σ' cost,
      BigStep (FinTM2.compileDispatcher tm fresh).com σ σ' cost ∧
      NumericRep σ' capacity
        (FinTM2.encodeNumericState tm (TM2.stepAux (tm.m l) s S)
          (stepAux_stacksWithin _ _ _ _ hS
            (FinTM2.generatedBy_main_available tm l))) := by
  letI := tm.ΛFin
  letI : DecidableEq tm.Λ := Classical.decEq _
  obtain ⟨σ', cost, hrun, hfinal⟩ :=
    FinTM2.compileDispatcher_correct tm l fresh capacity
      (FinTM2.encodeNumericState tm ⟨some l, s, S⟩ hS) σ
      (by simp [FinTM2.encodeNumericState, finCode]) hrep htables hsafe
  refine ⟨σ', cost, hrun, ?_⟩
  rw [numericStmt_exec_encode] at hfinal
  exact hfinal

/-- A finite typed run together with exactly the array-capacity obligations
needed by the compiled stack operations. -/
inductive SafeRun (tm : FinTM2) (capacity : ℕ → ℕ) : tm.Cfg → tm.Cfg → Type
  | halt (c : tm.Cfg)
      (hc : StacksWithin (FinTM2.availableSymbols tm) c.stk)
      (hhalt : c.l = none) : SafeRun tm capacity c c
  | step (l : tm.Λ) (s : tm.σ) (S : ∀ k, List (tm.Γ k))
      (hS : StacksWithin (FinTM2.availableSymbols tm) S)
      (final : tm.Cfg)
      (hsafe : SafeExec capacity
        (numericStmt tm (tm.m l) (FinTM2.generatedBy_main_available tm l))
        (FinTM2.encodeNumericState tm ⟨some l, s, S⟩ hS))
      (tail : SafeRun tm capacity (TM2.stepAux (tm.m l) s S) final) :
      SafeRun tm capacity ⟨some l, s, S⟩ final

def SafeRun.steps {tm : FinTM2} {capacity : ℕ → ℕ} {c final : tm.Cfg} :
    SafeRun tm capacity c final → ℕ
  | .halt _ _ _ => 0
  | .step _ _ _ _ _ _ tail => tail.steps + 1

/-- The compiled `while` loop executes every transition in a safe finite run
and stops at its final halted configuration. -/
theorem FinTM2.compileLoop_safeRun (tm : FinTM2) (capacity : ℕ → ℕ)
    (c final : tm.Cfg) (hc : StacksWithin (FinTM2.availableSymbols tm) c.stk)
    (hrun : SafeRun tm capacity c final) (σ : Env)
    (hrep : NumericRep σ capacity (FinTM2.encodeNumericState tm c hc))
    (htables : TablesRep σ (FinTM2.compileDispatcher tm 0).tables) :
    ∃ σ' cost, BigStep (FinTM2.compileLoop tm) σ σ' cost ∧
      cost ≤
        (1 + Cond.size (.lt (.lit 0) (.var labelVar)) +
          maxCost (FinTM2.compileDispatcher tm 0).com) * hrun.steps +
          (1 + Cond.size (.lt (.lit 0) (.var labelVar))) ∧
      ∃ hfinal : StacksWithin (FinTM2.availableSymbols tm) final.stk,
        NumericRep σ' capacity (FinTM2.encodeNumericState tm final hfinal) ∧
        TablesRep σ' (FinTM2.compileDispatcher tm 0).tables := by
  letI := tm.ΛFin
  letI : DecidableEq tm.Λ := Classical.decEq _
  induction hrun generalizing σ with
  | halt c hwithin hhalt =>
      subst_vars
      have hzero : σ.vars labelVar = 0 := by
        rw [hrep.2.1]
        simp [FinTM2.encodeNumericState, hhalt]
      refine ⟨σ, 1 + Cond.size (.lt (.lit 0) (.var labelVar)), ?_,
        by simp [SafeRun.steps], hwithin, hrep, htables⟩
      unfold FinTM2.compileLoop
      exact BigStep.while_false (by simp [Cond.eval, Expr.eval, hzero])
  | step l s S hS final hsafe tail ih =>
      have hpositive : σ.vars labelVar = finCode l + 1 := by
        rw [hrep.2.1]
        simp [FinTM2.encodeNumericState]
      obtain ⟨σ₁, costStep, hstep, hrep₁, htables₁⟩ :=
        FinTM2.compileDispatcher_correct_framed tm l 0 capacity
          (FinTM2.encodeNumericState tm ⟨some l, s, S⟩ hc) σ
          (by simp [FinTM2.encodeNumericState]) hrep htables
          (by simpa using hsafe)
      let hnext : StacksWithin (FinTM2.availableSymbols tm)
          (TM2.stepAux (tm.m l) s S).stk :=
        stepAux_stacksWithin _ _ _ _ hS
          (FinTM2.generatedBy_main_available tm l)
      have hrepNext : NumericRep σ₁ capacity
          (FinTM2.encodeNumericState tm (TM2.stepAux (tm.m l) s S) hnext) := by
        rw [numericStmt_exec_encode] at hrep₁
        exact hrep₁
      obtain ⟨σ₂, costTail, hloop, hcostTail, hfinal, hrepFinal, htablesFinal⟩ :=
        ih hnext σ₁ hrepNext htables₁
      have hcostStep : costStep ≤ maxCost (FinTM2.compileDispatcher tm 0).com :=
        BigStep.cost_le_maxCost hstep (FinTM2.compileDispatcher_loopFree tm 0)
      refine ⟨σ₂,
        1 + Cond.size (.lt (.lit 0) (.var labelVar)) + costStep + costTail,
        ?_, ?_, hfinal, hrepFinal, htablesFinal⟩
      · unfold FinTM2.compileLoop at hloop ⊢
        exact BigStep.while_true
          (by simp [Cond.eval, Expr.eval, hpositive]) hstep hloop
      · simp only [SafeRun.steps]
        rw [Nat.mul_add]
        simp only [Nat.mul_one]
        omega

/-- End-to-end correctness of the concrete table initializer followed by the
interpreter loop, for an already encoded initial configuration. -/
theorem FinTM2.compileMachine_safeRun (tm : FinTM2) (capacity : ℕ → ℕ)
    (c final : tm.Cfg) (hc : StacksWithin (FinTM2.availableSymbols tm) c.stk)
    (hrun : SafeRun tm capacity c final) (σ : Env)
    (hrep : NumericRep σ capacity (FinTM2.encodeNumericState tm c hc))
    (hzero : ∀ name values,
      (name, values) ∈ (FinTM2.compileDispatcher tm 0).tables →
      σ.arrs name = List.replicate values.length 0) :
    ∃ σ' cost, BigStep (FinTM2.compileMachine tm) σ σ' cost ∧
      cost ≤ initializeTablesCost (FinTM2.compileDispatcher tm 0).tables +
        (1 + Cond.size (.lt (.lit 0) (.var labelVar)) +
          maxCost (FinTM2.compileDispatcher tm 0).com) * hrun.steps +
        (1 + Cond.size (.lt (.lit 0) (.var labelVar))) ∧
      ∃ hfinal : StacksWithin (FinTM2.availableSymbols tm) final.stk,
        NumericRep σ' capacity (FinTM2.encodeNumericState tm final hfinal) ∧
        TablesRep σ' (FinTM2.compileDispatcher tm 0).tables := by
  let tables := (FinTM2.compileDispatcher tm 0).tables
  obtain ⟨hinit, htables⟩ := initializeTables_correct tables σ
    (FinTM2.compileDispatcher_tables_pairwise tm 0) (by
      simpa [tables] using hzero)
  have hrepInit : NumericRep (storeTables tables σ) capacity
      (FinTM2.encodeNumericState tm c hc) := by
    simpa [tables] using NumericRep.storeDispatcherTables tm 0 hrep
  obtain ⟨σ', loopCost, hloop, hloopCost, hfinal, hfinalRep, hfinalTables⟩ :=
    FinTM2.compileLoop_safeRun tm capacity c final hc hrun
      (storeTables tables σ) hrepInit (by simpa [tables] using htables)
  refine ⟨σ', initializeTablesCost tables + loopCost, ?_, ?_, hfinal,
    hfinalRep, hfinalTables⟩
  · simpa [FinTM2.compileMachine, FinTM2.compileLoop, tables] using
      BigStep.seq hinit hloop
  · simpa [tables, Nat.add_assoc] using Nat.add_le_add_left hloopCost
      (initializeTablesCost tables)

end Lax20Proofs.TMToRam
