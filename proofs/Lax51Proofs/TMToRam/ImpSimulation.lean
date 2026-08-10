import Lax51Proofs.TMToRam.ImpCompiler
import Lax13Proofs.Frame
import Lax51Proofs.TMToRam.Simulation

/-!
The representation invariant used to verify the IMP+ implementation.  The
active part of each physical stack array is the reverse of the logical
top-first stack; cells beyond the top pointer are deliberately unconstrained,
which makes the invariant stable under `pop` without clearing memory.
-/

namespace Lax51Proofs.TMToRam

open Lax13Proofs.Imp

theorem stackName_injective : Function.Injective stackName := by
  intro j k h
  simpa [stackName, toString] using h

theorem topName_injective : Function.Injective topName := by
  intro j k h
  simpa [topName, toString] using h

theorem stateVar_ne_topName (k : ℕ) : stateVar ≠ topName k := by
  intro h
  have hh := congrArg String.toList h
  simp [stateVar, topName] at hh

theorem stateVar_ne_stackName (k : ℕ) : stateVar ≠ stackName k := by
  intro h
  have hh := congrArg String.toList h
  simp [stateVar, stackName] at hh

theorem labelVar_ne_topName (k : ℕ) : labelVar ≠ topName k := by
  intro h
  have hh := congrArg String.toList h
  simp [labelVar, topName] at hh

theorem labelVar_ne_stackName (k : ℕ) : labelVar ≠ stackName k := by
  intro h
  have hh := congrArg String.toList h
  simp [labelVar, stackName] at hh

theorem topName_ne_stackName (j k : ℕ) : topName j ≠ stackName k := by
  intro h
  have hh := congrArg String.toList h
  simp [topName, stackName] at hh

theorem stackName_ne_tableName (k i : ℕ) : stackName k ≠ tableName i := by
  intro h
  have hh := congrArg String.toList h
  simp [stackName, tableName] at hh

theorem tableName_ne_stackName (i k : ℕ) : tableName i ≠ stackName k :=
  (stackName_ne_tableName k i).symm

theorem tempVar_ne_stateVar : tempVar ≠ stateVar := by decide
theorem tempVar_ne_labelVar : tempVar ≠ labelVar := by decide
theorem tempVar_ne_headVar : tempVar ≠ headVar := by decide
theorem headVar_ne_tempVar : headVar ≠ tempVar := by decide
theorem stateVar_ne_labelVar : stateVar ≠ labelVar := by decide
theorem headVar_ne_stateVar : headVar ≠ stateVar := by decide
theorem headVar_ne_labelVar : headVar ≠ labelVar := by decide
theorem indexVar_ne_stateVar : indexVar ≠ stateVar := by decide
theorem indexVar_ne_labelVar : indexVar ≠ labelVar := by decide

theorem tempVar_ne_topName (k : ℕ) : tempVar ≠ topName k := by
  intro h
  have hh := congrArg String.toList h
  simp [tempVar, topName] at hh

theorem headVar_ne_topName (k : ℕ) : headVar ≠ topName k := by
  intro h
  have hh := congrArg String.toList h
  simp [headVar, topName] at hh

theorem indexVar_ne_topName (k : ℕ) : indexVar ≠ topName k := by
  intro h
  have hh := congrArg String.toList h
  simp [indexVar, topName] at hh

@[simp] theorem Env.setVar_vars_self (σ : Env) (x : String) (v : ℕ) :
    (σ.setVar x v).vars x = v := by simp [Env.setVar]

theorem Env.setVar_vars_of_ne (σ : Env) {x y : String} (v : ℕ) (h : y ≠ x) :
    (σ.setVar x v).vars y = σ.vars y := by simp [Env.setVar, h]

@[simp] theorem Env.setVar_arrs (σ : Env) (x : String) (v : ℕ) :
    (σ.setVar x v).arrs = σ.arrs := rfl

@[simp] theorem Env.setArr_vars (σ : Env) (a : String) (i v : ℕ) :
    (σ.setArr a i v).vars = σ.vars := rfl

@[simp] theorem Env.setArr_arrs_self (σ : Env) (a : String) (i v : ℕ) :
    (σ.setArr a i v).arrs a = (σ.arrs a).set i v := by simp [Env.setArr]

theorem Env.setArr_arrs_of_ne (σ : Env) {a b : String} (i v : ℕ) (h : b ≠ a) :
    (σ.setArr a i v).arrs b = σ.arrs b := by simp [Env.setArr, h]

/-- Representation of one numeric stack in a fixed-capacity IMP+ array. -/
def StackRep (σ : Env) (k capacity : ℕ) (xs : List ℕ) : Prop :=
  σ.vars (topName k) = xs.length ∧
    (σ.arrs (stackName k)).length = capacity ∧
    (σ.arrs (stackName k)).take xs.length = xs.reverse

/-- Scalar and stack portion of the numeric-machine representation.  A
capacity function is used because the IMP semantics assigns array lengths in
the initial environment. -/
def NumericRep (σ : Env) (capacity : ℕ → ℕ) (c : NumericMachineState) : Prop :=
  σ.vars stateVar = c.state ∧
    σ.vars labelVar = (c.label.map (· + 1)).getD 0 ∧
    ∀ k, StackRep σ k (capacity k) (c.stackData k)

/-- The literal arrays allocated while compiling a statement. -/
def TablesRep (σ : Env) (tables : List (String × List ℕ)) : Prop :=
  ∀ name values, (name, values) ∈ tables → σ.arrs name = values

theorem TablesRep.head {σ : Env} {name : String} {values : List ℕ}
    {rest : List (String × List ℕ)}
    (h : TablesRep σ ((name, values) :: rest)) : σ.arrs name = values := by
  exact h name values (by simp)

theorem TablesRep.tail {σ : Env} {entry : String × List ℕ}
    {rest : List (String × List ℕ)}
    (h : TablesRep σ (entry :: rest)) : TablesRep σ rest := by
  intro name values hm
  exact h name values (by simp [hm])

theorem TablesRep.setVar {σ : Env} {tables : List (String × List ℕ)}
    (h : TablesRep σ tables) (x : String) (v : ℕ) :
    TablesRep (σ.setVar x v) tables := by
  simpa [TablesRep] using h

theorem TablesRep.append_left {σ : Env} {left right : List (String × List ℕ)}
    (h : TablesRep σ (left ++ right)) : TablesRep σ left := by
  intro name values hm
  exact h name values (List.mem_append_left _ hm)

theorem TablesRep.append_right {σ : Env} {left right : List (String × List ℕ)}
    (h : TablesRep σ (left ++ right)) : TablesRep σ right := by
  intro name values hm
  exact h name values (List.mem_append_right _ hm)

theorem compileNumericStmt_tables_name (q : NumericStmt) (fresh : ℕ)
    (name : String) (values : List ℕ)
    (h : (name, values) ∈ (compileNumericStmt q fresh).tables) :
    ∃ i, name = tableName i := by
  induction q generalizing fresh with
  | push k table next ih =>
      rcases (by simpa [compileNumericStmt] using h) with ⟨rfl, rfl⟩ | hrest
      · exact ⟨fresh, rfl⟩
      · exact ih (fresh + 1) hrest
  | peek k width table next ih =>
      rcases (by simpa [compileNumericStmt] using h) with ⟨rfl, rfl⟩ | hrest
      · exact ⟨fresh, rfl⟩
      · exact ih (fresh + 1) hrest
  | pop k width table next ih =>
      rcases (by simpa [compileNumericStmt] using h) with ⟨rfl, rfl⟩ | hrest
      · exact ⟨fresh, rfl⟩
      · exact ih (fresh + 1) hrest
  | load table next ih =>
      rcases (by simpa [compileNumericStmt] using h) with ⟨rfl, rfl⟩ | hrest
      · exact ⟨fresh, rfl⟩
      · exact ih (fresh + 1) hrest
  | branch table yes no ihy ihn =>
      rcases (by simpa [compileNumericStmt] using h) with
        ⟨rfl, rfl⟩ | hleft | hright
      · exact ⟨fresh, rfl⟩
      · exact ihy (fresh + 1) hleft
      · exact ihn (compileNumericStmt yes (fresh + 1)).nextTable hright
  | goto table =>
      have heq : (name, values) = (tableName fresh, table) := by
        simpa [compileNumericStmt] using h
      exact ⟨fresh, (Prod.mk.inj heq).1⟩
  | halt => simp [compileNumericStmt] at h

theorem TablesRep.setStackArr {σ : Env} {q : NumericStmt} {fresh k i v : ℕ}
    (h : TablesRep σ (compileNumericStmt q fresh).tables) :
    TablesRep (σ.setArr (stackName k) i v) (compileNumericStmt q fresh).tables := by
  intro name values hm
  obtain ⟨j, rfl⟩ := compileNumericStmt_tables_name q fresh name values hm
  rw [Env.setArr_arrs_of_ne σ i v (stackName_ne_tableName k j).symm]
  exact h (tableName j) values hm

/-- Safety obligations that turn the total, defaulting numeric reference
semantics into a non-stuck IMP+ execution. -/
def SafeExec (capacity : ℕ → ℕ) : NumericStmt → NumericMachineState → Prop
  | .push k table next, c =>
      c.state < table.length ∧ (c.stackData k).length < capacity k ∧
        SafeExec capacity next
          { c with stackData := (Function.update c.stackData k
              (table.getD c.state 0 :: c.stackData k)) }
  | .peek k width table next, c =>
      c.state * width + headCode (c.stackData k) < table.length ∧
        SafeExec capacity next
          { c with state := (table.getD
              (c.state * width + headCode (c.stackData k)) 0) }
  | .pop k width table next, c =>
      c.state * width + headCode (c.stackData k) < table.length ∧
        SafeExec capacity next
          { { c with state := (table.getD
                (c.state * width + headCode (c.stackData k)) 0) } with
            stackData := (Function.update c.stackData k (c.stackData k).tail) }
  | .load table next, c =>
      c.state < table.length ∧
        SafeExec capacity next { c with state := (table.getD c.state 0) }
  | .branch table yes no, c =>
      c.state < table.length ∧
        if table.getD c.state 0 = 0 then SafeExec capacity no c
        else SafeExec capacity yes c
  | .goto table, c => c.state < table.length
  | .halt, _ => True

theorem StackRep.top_eq {σ : Env} {k capacity : ℕ} {xs : List ℕ}
    (h : StackRep σ k capacity xs) : σ.vars (topName k) = xs.length := h.1

theorem StackRep.length_eq {σ : Env} {k capacity : ℕ} {xs : List ℕ}
    (h : StackRep σ k capacity xs) :
    (σ.arrs (stackName k)).length = capacity := h.2.1

theorem StackRep.take_eq {σ : Env} {k capacity : ℕ} {xs : List ℕ}
    (h : StackRep σ k capacity xs) :
    (σ.arrs (stackName k)).take xs.length = xs.reverse := h.2.2

theorem StackRep.setVar_of_ne {σ : Env} {k capacity : ℕ} {xs : List ℕ}
    {x : String} {v : ℕ} (h : StackRep σ k capacity xs)
    (hne : topName k ≠ x) : StackRep (σ.setVar x v) k capacity xs := by
  exact ⟨by simpa [Env.setVar, hne] using h.1, h.2⟩

theorem StackRep.setArr_of_ne {σ : Env} {k capacity : ℕ} {xs : List ℕ}
    {a : String} {i v : ℕ} (h : StackRep σ k capacity xs)
    (hne : stackName k ≠ a) : StackRep (σ.setArr a i v) k capacity xs := by
  exact ⟨h.1, by simpa [Env.setArr, hne] using h.2⟩

theorem NumericRep.setTemp (σ : Env) (capacity : ℕ → ℕ)
    (c : NumericMachineState) (v : ℕ) (h : NumericRep σ capacity c) :
    NumericRep (σ.setVar tempVar v) capacity c := by
  rcases h with ⟨hs, hl, hst⟩
  refine ⟨?_, ?_, fun k => ?_⟩
  · simpa [Env.setVar, tempVar_ne_stateVar] using hs
  · simpa [Env.setVar, tempVar_ne_labelVar] using hl
  · exact (hst k).setVar_of_ne (fun he => tempVar_ne_topName k he.symm)

theorem NumericRep.setHead (σ : Env) (capacity : ℕ → ℕ)
    (c : NumericMachineState) (v : ℕ) (h : NumericRep σ capacity c) :
    NumericRep (σ.setVar headVar v) capacity c := by
  rcases h with ⟨hs, hl, hst⟩
  refine ⟨?_, ?_, fun k => ?_⟩
  · simpa [Env.setVar, headVar_ne_stateVar] using hs
  · simpa [Env.setVar, headVar_ne_labelVar] using hl
  · exact (hst k).setVar_of_ne (fun he => headVar_ne_topName k he.symm)

theorem NumericRep.setIndex (σ : Env) (capacity : ℕ → ℕ)
    (c : NumericMachineState) (v : ℕ) (h : NumericRep σ capacity c) :
    NumericRep (σ.setVar indexVar v) capacity c := by
  rcases h with ⟨hs, hl, hst⟩
  refine ⟨?_, ?_, fun k => ?_⟩
  · simpa [Env.setVar, indexVar_ne_stateVar] using hs
  · simpa [Env.setVar, indexVar_ne_labelVar] using hl
  · exact (hst k).setVar_of_ne (fun he => indexVar_ne_topName k he.symm)

theorem NumericRep.setState (σ : Env) (capacity : ℕ → ℕ)
    (c : NumericMachineState) (v : ℕ) (h : NumericRep σ capacity c) :
    NumericRep (σ.setVar stateVar v) capacity { c with state := v } := by
  rcases h with ⟨hs, hl, hst⟩
  refine ⟨by simp, ?_, fun k => ?_⟩
  · simpa [Env.setVar, stateVar_ne_labelVar.symm] using hl
  · exact (hst k).setVar_of_ne (stateVar_ne_topName k).symm

theorem NumericRep.setLabel (σ : Env) (capacity : ℕ → ℕ)
    (c : NumericMachineState) (v : ℕ) (h : NumericRep σ capacity c) :
    NumericRep (σ.setVar labelVar v) capacity
      { c with label := if v = 0 then none else some (v - 1) } := by
  rcases h with ⟨hs, hl, hst⟩
  refine ⟨?_, ?_, fun k => ?_⟩
  · simpa [Env.setVar, stateVar_ne_labelVar] using hs
  · by_cases hv : v = 0
    · simp [Env.setVar, hv]
    · simp [Env.setVar, hv]
      omega
  · exact (hst k).setVar_of_ne (labelVar_ne_topName k).symm

@[simp] theorem set_at_length (xs : List ℕ) (a : ℕ) :
    xs.set xs.length a = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.set, ih]

/-- Updating the first inactive cell extends the represented active prefix
by one element. -/
theorem take_set_top (arr xs : List ℕ) (a : ℕ)
    (htake : arr.take xs.length = xs.reverse)
    (hroom : xs.length < arr.length) :
    (arr.set xs.length a).take (a :: xs).length = (a :: xs).reverse := by
  rw [List.length_cons, List.take_succ, List.getElem?_set]
  simp only [List.take_set, if_pos rfl, if_pos hroom, Option.toList_some,
    List.reverse_cons]
  rw [htake]
  have hset : xs.reverse.set xs.length a = xs.reverse := by
    rw [show xs.length = xs.reverse.length by simp, set_at_length]
  simp [hset]

/-- Storing at the current top and incrementing the top pointer represents a
logical push. -/
theorem NumericRep.push (σ : Env) (capacity : ℕ → ℕ)
    (c : NumericMachineState) (k v : ℕ) (h : NumericRep σ capacity c)
    (hroom : (c.stackData k).length < capacity k) :
    NumericRep
      ((σ.setArr (stackName k) (c.stackData k).length v).setVar
        (topName k) ((c.stackData k).length + 1)) capacity
      { c with stackData := (Function.update c.stackData k (v :: c.stackData k)) } := by
  rcases h with ⟨hs, hl, hst⟩
  refine ⟨?_, ?_, fun j => ?_⟩
  · simpa [Env.setVar, stateVar_ne_topName k] using hs
  · simpa [Env.setVar, labelVar_ne_topName k] using hl
  · by_cases hj : j = k
    · subst j
      change StackRep _ k (capacity k)
        ((Function.update c.stackData k (v :: c.stackData k)) k)
      rw [Function.update_self]
      refine ⟨by simp, ?_, ?_⟩
      · simpa [Env.setArr] using (hst k).length_eq
      · simp only [Env.setVar_arrs, Env.setArr_arrs_self]
        exact take_set_top _ _ _ (hst k).take_eq (by
          rw [(hst k).length_eq]
          exact hroom)
    · change StackRep _ j (capacity j)
        ((Function.update c.stackData k (v :: c.stackData k)) j)
      rw [Function.update_of_ne hj]
      apply StackRep.setVar_of_ne
      · apply StackRep.setArr_of_ne (hst j)
        intro he
        exact hj (stackName_injective he)
      · intro he
        exact hj (topName_injective he)

/-- Lowering a top pointer represents removing the logical head; the array
cell itself need not be cleared. -/
theorem StackRep.setTop_tail {σ : Env} {k capacity : ℕ} {xs : List ℕ}
    (h : StackRep σ k capacity xs) :
    StackRep (σ.setVar (topName k) xs.tail.length) k capacity xs.tail := by
  cases xs with
  | nil =>
      exact ⟨by simp, h.2⟩
  | cons a xs =>
      refine ⟨by simp, h.length_eq, ?_⟩
      have ht := congrArg (List.take xs.length) h.take_eq
      simpa [List.take_take, List.reverse_cons] using ht

/-- Environment-level representation update for a logical pop. -/
theorem NumericRep.pop (σ : Env) (capacity : ℕ → ℕ)
    (c : NumericMachineState) (k : ℕ) (h : NumericRep σ capacity c) :
    NumericRep (σ.setVar (topName k) (c.stackData k).tail.length) capacity
      { c with stackData := (Function.update c.stackData k (c.stackData k).tail) } := by
  rcases h with ⟨hs, hl, hst⟩
  refine ⟨?_, ?_, fun j => ?_⟩
  · simpa [Env.setVar, stateVar_ne_topName k] using hs
  · simpa [Env.setVar, labelVar_ne_topName k] using hl
  · by_cases hj : j = k
    · subst j
      change StackRep _ k (capacity k)
        ((Function.update c.stackData k (c.stackData k).tail) k)
      rw [Function.update_self]
      exact (hst k).setTop_tail
    · change StackRep _ j (capacity j)
        ((Function.update c.stackData k (c.stackData k).tail) j)
      rw [Function.update_of_ne hj]
      apply StackRep.setVar_of_ne (hst j)
      intro he
      exact hj (topName_injective he)

theorem StackRep.capacity_ge {σ : Env} {k capacity : ℕ} {xs : List ℕ}
    (h : StackRep σ k capacity xs) : xs.length ≤ capacity := by
  have ht := congrArg List.length h.take_eq
  simp only [List.length_take, List.length_reverse] at ht
  rw [← h.length_eq]
  omega

/-- In a represented nonempty stack, the cell immediately below the top
pointer contains the logical head. -/
theorem StackRep.get_head {σ : Env} {k capacity a : ℕ} {xs : List ℕ}
    (h : StackRep σ k capacity (a :: xs)) :
    (σ.arrs (stackName k))[xs.length]? = some a := by
  have hg := congrArg (fun ys : List ℕ => ys[xs.length]?) h.take_eq
  simpa [List.getElem?_take, List.reverse_cons] using hg

/-- The non-destructive head-reading fragment implements `headCode`. -/
theorem readHead_correct (k : ℕ) (capacity : ℕ → ℕ)
    (c : NumericMachineState) (σ : Env) (hrep : NumericRep σ capacity c) :
    ∃ σ' cost, BigStep (readHead k) σ σ' cost ∧
      NumericRep σ' capacity c ∧ σ'.vars headVar = headCode (c.stackData k) ∧
        σ'.arrs = σ.arrs := by
  have hk := hrep.2.2 k
  cases hs : c.stackData k with
  | nil =>
      let σ' := σ.setVar headVar 0
      have hcond : Cond.eval (.eq (.var (topName k)) (.lit 0)) σ = some true := by
        simp [Cond.eval, Expr.eval, hk.top_eq, hs]
      have hassign : BigStep (.assign headVar (.lit 0)) σ σ' 2 := .assign rfl
      have hrun : ∃ cost, BigStep (readHead k) σ σ' cost := by
        refine ⟨1 + Cond.size (.eq (.var (topName k)) (.lit 0)) + 2, ?_⟩
        rw [readHead]
        exact BigStep.ite_true hcond hassign
      obtain ⟨cost, hrun⟩ := hrun
      refine ⟨σ', cost, hrun, ?_, ?_, rfl⟩
      · exact hrep.setHead σ capacity c 0
      · simp [σ', headCode]
  | cons a xs =>
      have htop : σ.vars (topName k) = xs.length + 1 := by
        simpa [hs] using hk.top_eq
      have hcell : (σ.arrs (stackName k))[xs.length]? = some a := by
        have hk' : StackRep σ k (capacity k) (a :: xs) := by simpa [hs] using hk
        exact hk'.get_head
      let σ₁ := σ.setVar tempVar xs.length
      let σ₂ := σ₁.setVar headVar (a + 1)
      have htemp : BigStep
          (.assign tempVar (.sub (.var (topName k)) (.lit 1))) σ σ₁ 4 := by
        apply BigStep.assign
        simp [Expr.eval, htop, σ₁]
      have hhead : BigStep
          (.assign headVar (.add (.get (stackName k) (.var tempVar)) (.lit 1)))
            σ₁ σ₂ 5 := by
        apply BigStep.assign
        simp [Expr.eval, σ₁, hcell]
      have hcond : Cond.eval (.eq (.var (topName k)) (.lit 0)) σ = some false := by
        simp [Cond.eval, Expr.eval, htop]
      have hbody : BigStep (seqs [
          .assign tempVar (.sub (.var (topName k)) (.lit 1)),
          .assign headVar (.add (.get (stackName k) (.var tempVar)) (.lit 1))])
          σ σ₂ (4 + (5 + 1)) := by
        simp only [seqs]
        exact .seq htemp (.seq hhead .skip)
      have hrun : ∃ cost, BigStep (readHead k) σ σ₂ cost := by
        refine ⟨1 + Cond.size (.eq (.var (topName k)) (.lit 0)) +
          (4 + (5 + 1)), ?_⟩
        rw [readHead]
        exact BigStep.ite_false hcond hbody
      obtain ⟨cost, hrun⟩ := hrun
      refine ⟨σ₂, cost, hrun, ?_, ?_, rfl⟩
      · exact (hrep.setTemp σ capacity c xs.length).setHead σ₁ capacity c (a + 1)
      · simp [σ₂, headCode, hs]

/-- The destructive head-reading fragment implements `headCode` and logical
stack tail simultaneously. -/
theorem readHeadAndPop_correct (k : ℕ) (capacity : ℕ → ℕ)
    (c : NumericMachineState) (σ : Env) (hrep : NumericRep σ capacity c) :
    ∃ σ' cost, BigStep (readHeadAndPop k) σ σ' cost ∧
      NumericRep σ' capacity
        { c with stackData := (Function.update c.stackData k (c.stackData k).tail) } ∧
      σ'.vars headVar = headCode (c.stackData k) ∧ σ'.arrs = σ.arrs := by
  have hk := hrep.2.2 k
  cases hs : c.stackData k with
  | nil =>
      let σ' := σ.setVar headVar 0
      have hcond : Cond.eval (.eq (.var (topName k)) (.lit 0)) σ = some true := by
        simp [Cond.eval, Expr.eval, hk.top_eq, hs]
      have hassign : BigStep (.assign headVar (.lit 0)) σ σ' 2 := .assign rfl
      have hrun : ∃ cost, BigStep (readHeadAndPop k) σ σ' cost := by
        refine ⟨1 + Cond.size (.eq (.var (topName k)) (.lit 0)) + 2, ?_⟩
        rw [readHeadAndPop]
        exact BigStep.ite_true hcond hassign
      obtain ⟨cost, hrun⟩ := hrun
      refine ⟨σ', cost, hrun, ?_, by simp [σ', headCode], rfl⟩
      have heq : Function.update c.stackData k (c.stackData k).tail = c.stackData := by
        funext j
        by_cases hj : j = k
        · subst j
          simp [hs]
        · rw [Function.update_of_ne hj]
      have heq' : Function.update c.stackData k [] = c.stackData := by
        simpa [hs] using heq
      simpa [heq'] using hrep.setHead σ capacity c 0
  | cons a xs =>
      have htop : σ.vars (topName k) = xs.length + 1 := by
        simpa [hs] using hk.top_eq
      have hcell : (σ.arrs (stackName k))[xs.length]? = some a := by
        exact (show StackRep σ k (capacity k) (a :: xs) by simpa [hs] using hk).get_head
      let σ₁ := σ.setVar tempVar xs.length
      let σ₂ := σ₁.setVar headVar (a + 1)
      let σ₃ := σ₂.setVar (topName k) xs.length
      have htemp : BigStep
          (.assign tempVar (.sub (.var (topName k)) (.lit 1))) σ σ₁ 4 := by
        apply BigStep.assign
        simp [Expr.eval, htop, σ₁]
      have hhead : BigStep
          (.assign headVar (.add (.get (stackName k) (.var tempVar)) (.lit 1)))
            σ₁ σ₂ 5 := by
        apply BigStep.assign
        simp [Expr.eval, σ₁, hcell]
      have htopSet : BigStep (.assign (topName k) (.var tempVar)) σ₂ σ₃ 2 := by
        apply BigStep.assign
        simp [Expr.eval, σ₂, σ₁, Env.setVar, tempVar_ne_headVar]
      have hcond : Cond.eval (.eq (.var (topName k)) (.lit 0)) σ = some false := by
        simp [Cond.eval, Expr.eval, htop]
      have hbody : BigStep (seqs [
          .assign tempVar (.sub (.var (topName k)) (.lit 1)),
          .assign headVar (.add (.get (stackName k) (.var tempVar)) (.lit 1)),
          .assign (topName k) (.var tempVar)]) σ σ₃ (4 + (5 + (2 + 1))) := by
        simp only [seqs]
        exact .seq htemp (.seq hhead (.seq htopSet .skip))
      have hrun : ∃ cost, BigStep (readHeadAndPop k) σ σ₃ cost := by
        refine ⟨1 + Cond.size (.eq (.var (topName k)) (.lit 0)) +
          (4 + (5 + (2 + 1))), ?_⟩
        rw [readHeadAndPop]
        exact BigStep.ite_false hcond hbody
      obtain ⟨cost, hrun⟩ := hrun
      refine ⟨σ₃, cost, hrun, ?_, ?_, rfl⟩
      · have hp := (hrep.setTemp σ capacity c xs.length).setHead σ₁ capacity c (a + 1)
        simpa [σ₃, hs] using hp.pop σ₂ capacity c k
      · change σ₂.vars headVar = a + 1
        simp [σ₂, Env.setVar]

@[simp] theorem eval_lit (σ : Env) (n : ℕ) : Expr.eval (.lit n) σ = some n := rfl

@[simp] theorem eval_var (σ : Env) (x : String) :
    Expr.eval (.var x) σ = some (σ.vars x) := rfl

@[simp] theorem eval_add (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.eval σ = some m) (hf : f.eval σ = some n) :
    Expr.eval (.add e f) σ = some (m + n) := by
  simp [Expr.eval, he, hf]

@[simp] theorem eval_sub (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.eval σ = some m) (hf : f.eval σ = some n) :
    Expr.eval (.sub e f) σ = some (m - n) := by
  simp [Expr.eval, he, hf]

@[simp] theorem eval_mul (σ : Env) (e f : Expr) (m n : ℕ)
    (he : e.eval σ = some m) (hf : f.eval σ = some n) :
    Expr.eval (.mul e f) σ = some (m * n) := by
  simp [Expr.eval, he, hf]

theorem eval_get (σ : Env) (a : String) (i : Expr) (k v : ℕ)
    (hi : i.eval σ = some k) (hv : (σ.arrs a)[k]? = some v) :
    Expr.eval (.get a i) σ = some v := by
  simp [Expr.eval, hi, hv]

/-- A table read has its expected one-command IMP+ execution whenever the
requested literal entry exists. -/
theorem tableRead_bigStep (σ : Env) (name target : String) (index : Expr)
    (i v : ℕ) (hi : index.eval σ = some i)
    (hv : (σ.arrs name)[i]? = some v) :
    BigStep (tableRead name target index) σ (σ.setVar target v)
      (1 + (Expr.get name index).size) := by
  exact .assign (eval_get σ name index i v hi hv)

theorem getElem?_eq_getD {xs : List ℕ} {i d : ℕ} (hi : i < xs.length) :
    xs[i]? = some (xs.getD i d) := by
  rw [List.getD_eq_getElem xs d hi, List.getElem?_eq_getElem hi]

/-- Sequentially composed command lists inherit big-step executions. -/
theorem seqs_bigStep {cs : List Com} {σ σ' : Env} {cost : ℕ}
    (h : match cs with
      | [] => σ' = σ ∧ cost = 1
      | c :: rest => ∃ τ k₁ k₂,
          BigStep c σ τ k₁ ∧ BigStep (seqs rest) τ σ' k₂ ∧ cost = k₁ + k₂) :
    BigStep (seqs cs) σ σ' cost := by
  cases cs with
  | nil => rcases h with ⟨rfl, rfl⟩; exact .skip
  | cons c cs =>
      rcases h with ⟨τ, k₁, k₂, hc, hs, rfl⟩
      exact .seq hc hs

theorem setVar_twice (σ : Env) (x : String) (v w : ℕ) :
    (σ.setVar x v).setVar x w = σ.setVar x w := by
  cases σ with
  | mk vars arrs inp out =>
  simp only [Env.setVar, Env.mk.injEq, and_self]
  constructor
  · funext y
    by_cases h : y = x <;> simp [Env.setVar, h]
  · trivial

/-- Correctness of the terminal jump fragment produced by the compiler. -/
theorem compileNumericStmt_goto_correct (table : List ℕ) (fresh : ℕ)
    (capacity : ℕ → ℕ) (c : NumericMachineState) (σ : Env)
    (hrep : NumericRep σ capacity c)
    (htables : TablesRep σ (compileNumericStmt (.goto table) fresh).tables)
    (hsafe : SafeExec capacity (.goto table) c) :
    ∃ σ' cost, BigStep (compileNumericStmt (.goto table) fresh).com σ σ' cost ∧
      NumericRep σ' capacity ((.goto table : NumericStmt).exec c) := by
  let v := table.getD c.state 0
  have harr : σ.arrs (tableName fresh) = table := by
    apply htables (tableName fresh) table
    simp [compileNumericStmt]
  have hget : (σ.arrs (tableName fresh))[c.state]? = some v := by
    rw [harr]
    exact getElem?_eq_getD (by simpa [SafeExec] using hsafe)
  let σ₁ := σ.setVar labelVar v
  let σ₂ := σ₁.setVar labelVar (v + 1)
  have hread : BigStep
      (tableRead (tableName fresh) labelVar (.var stateVar)) σ σ₁ 3 := by
    apply tableRead_bigStep σ (tableName fresh) labelVar (.var stateVar) c.state v
    · simpa [hrep.1]
    · exact hget
  have hadd : BigStep
      (.assign labelVar (.add (.var labelVar) (.lit 1))) σ₁ σ₂ 4 := by
    apply BigStep.assign
    simp [Expr.eval, σ₁, v]
  have hrun : BigStep (compileNumericStmt (.goto table) fresh).com σ σ₂ 8 := by
    simp only [compileNumericStmt, seqs]
    exact .seq hread (.seq hadd .skip)
  refine ⟨σ₂, 8, hrun, ?_⟩
  rw [show σ₂ = σ.setVar labelVar (v + 1) by simp [σ₂, σ₁, setVar_twice]]
  have hr := hrep.setLabel σ capacity c (v + 1)
  simpa [NumericStmt.exec, v] using hr

/-- Correctness of the terminal halt fragment produced by the compiler. -/
theorem compileNumericStmt_halt_correct (fresh : ℕ)
    (capacity : ℕ → ℕ) (c : NumericMachineState) (σ : Env)
    (hrep : NumericRep σ capacity c) :
    ∃ σ' cost, BigStep (compileNumericStmt .halt fresh).com σ σ' cost ∧
      NumericRep σ' capacity ((.halt : NumericStmt).exec c) := by
  refine ⟨σ.setVar labelVar 0, 2, ?_, ?_⟩
  · simp only [compileNumericStmt]
    exact .assign rfl
  · simpa [NumericStmt.exec] using hrep.setLabel σ capacity c 0

/-- The `load` compiler case, parameterized by correctness of its recursive
continuation. -/
theorem compileNumericStmt_load_correct (table : List ℕ) (next : NumericStmt)
    (fresh : ℕ) (capacity : ℕ → ℕ) (c : NumericMachineState) (σ : Env)
    (hrep : NumericRep σ capacity c)
    (htables : TablesRep σ (compileNumericStmt (.load table next) fresh).tables)
    (hsafe : SafeExec capacity (.load table next) c)
    (hnext : ∀ τ,
      NumericRep τ capacity { c with state := (table.getD c.state 0) } →
      TablesRep τ (compileNumericStmt next (fresh + 1)).tables →
      ∃ τ' cost, BigStep (compileNumericStmt next (fresh + 1)).com τ τ' cost ∧
        NumericRep τ' capacity
          (next.exec { c with state := (table.getD c.state 0) })) :
    ∃ σ' cost, BigStep (compileNumericStmt (.load table next) fresh).com σ σ' cost ∧
      NumericRep σ' capacity ((NumericStmt.load table next).exec c) := by
  let v := table.getD c.state 0
  have hs : c.state < table.length := hsafe.1
  have harr : σ.arrs (tableName fresh) = table := by
    apply htables (tableName fresh) table
    simp [compileNumericStmt]
  have hget : (σ.arrs (tableName fresh))[c.state]? = some v := by
    rw [harr]
    exact getElem?_eq_getD hs
  let σ₁ := σ.setVar stateVar v
  have hread : BigStep
      (tableRead (tableName fresh) stateVar (.var stateVar)) σ σ₁ 3 := by
    apply tableRead_bigStep σ (tableName fresh) stateVar (.var stateVar) c.state v
    · simpa [hrep.1]
    · exact hget
  have hrep₁ : NumericRep σ₁ capacity { c with state := v } := by
    exact hrep.setState σ capacity c v
  have htables₁ : TablesRep σ₁ (compileNumericStmt next (fresh + 1)).tables := by
    apply TablesRep.setVar
    exact TablesRep.tail (by simpa [compileNumericStmt] using htables)
  obtain ⟨σ₂, cost, hrun, hfinal⟩ := hnext σ₁ hrep₁ htables₁
  refine ⟨σ₂, 3 + cost, ?_, ?_⟩
  · simpa [compileNumericStmt] using BigStep.seq hread hrun
  · simpa [NumericStmt.exec, v] using hfinal

/-- The branching compiler case, parameterized by correctness of both
compiled continuations. -/
theorem compileNumericStmt_branch_correct (table : List ℕ)
    (yes no : NumericStmt) (fresh : ℕ) (capacity : ℕ → ℕ)
    (c : NumericMachineState) (σ : Env)
    (hrep : NumericRep σ capacity c)
    (htables : TablesRep σ (compileNumericStmt (.branch table yes no) fresh).tables)
    (hsafe : SafeExec capacity (.branch table yes no) c)
    (hyes : ∀ τ, NumericRep τ capacity c →
      TablesRep τ (compileNumericStmt yes (fresh + 1)).tables →
      SafeExec capacity yes c →
      ∃ τ' cost, BigStep (compileNumericStmt yes (fresh + 1)).com τ τ' cost ∧
        NumericRep τ' capacity (yes.exec c))
    (hno : ∀ τ, NumericRep τ capacity c →
      TablesRep τ (compileNumericStmt no
        (compileNumericStmt yes (fresh + 1)).nextTable).tables →
      SafeExec capacity no c →
      ∃ τ' cost, BigStep (compileNumericStmt no
          (compileNumericStmt yes (fresh + 1)).nextTable).com τ τ' cost ∧
        NumericRep τ' capacity (no.exec c)) :
    ∃ σ' cost, BigStep (compileNumericStmt (.branch table yes no) fresh).com σ σ' cost ∧
      NumericRep σ' capacity ((NumericStmt.branch table yes no).exec c) := by
  let v := table.getD c.state 0
  have hs : c.state < table.length := hsafe.1
  have harr : σ.arrs (tableName fresh) = table := by
    apply htables (tableName fresh) table
    simp [compileNumericStmt]
  have hget : (σ.arrs (tableName fresh))[c.state]? = some v := by
    rw [harr]
    exact getElem?_eq_getD hs
  let σ₁ := σ.setVar tempVar v
  have hread : BigStep
      (tableRead (tableName fresh) tempVar (.var stateVar)) σ σ₁ 3 := by
    apply tableRead_bigStep σ (tableName fresh) tempVar (.var stateVar) c.state v
    · simpa [hrep.1]
    · exact hget
  have hrep₁ : NumericRep σ₁ capacity c := hrep.setTemp σ capacity c v
  have htail : TablesRep σ₁
      ((compileNumericStmt yes (fresh + 1)).tables ++
        (compileNumericStmt no
          (compileNumericStmt yes (fresh + 1)).nextTable).tables) := by
    apply TablesRep.setVar
    exact TablesRep.tail (by simpa [compileNumericStmt] using htables)
  by_cases hv : v = 0
  · have hsafeNo : SafeExec capacity no c := by
      have hb := hsafe.2
      change (if v = 0 then SafeExec capacity no c else SafeExec capacity yes c) at hb
      simpa [hv] using hb
    obtain ⟨σ₂, cost, hrun, hfinal⟩ :=
      hno σ₁ hrep₁ (TablesRep.append_right htail) hsafeNo
    refine ⟨σ₂, 3 + (4 + cost), ?_, ?_⟩
    · simp only [compileNumericStmt]
      apply BigStep.seq hread
      apply BigStep.ite_true
      · simp [Cond.eval, Expr.eval, σ₁, hv]
      · exact hrun
    · change NumericRep σ₂ capacity
        (if table.getD c.state 0 = 0 then no.exec c else yes.exec c)
      rw [show table.getD c.state 0 = v by rfl, if_pos hv]
      exact hfinal
  · have hsafeYes : SafeExec capacity yes c := by
      have hb := hsafe.2
      change (if v = 0 then SafeExec capacity no c else SafeExec capacity yes c) at hb
      simpa [hv] using hb
    obtain ⟨σ₂, cost, hrun, hfinal⟩ :=
      hyes σ₁ hrep₁ (TablesRep.append_left htail) hsafeYes
    refine ⟨σ₂, 3 + (4 + cost), ?_, ?_⟩
    · simp only [compileNumericStmt]
      apply BigStep.seq hread
      apply BigStep.ite_false
      · simp [Cond.eval, Expr.eval, σ₁, hv]
      · exact hrun
    · change NumericRep σ₂ capacity
        (if table.getD c.state 0 = 0 then no.exec c else yes.exec c)
      rw [show table.getD c.state 0 = v by rfl, if_neg hv]
      exact hfinal

/-- The non-destructive stack-head (`peek`) compiler case. -/
theorem compileNumericStmt_peek_correct (k width : ℕ) (table : List ℕ)
    (next : NumericStmt) (fresh : ℕ) (capacity : ℕ → ℕ)
    (c : NumericMachineState) (σ : Env)
    (hrep : NumericRep σ capacity c)
    (htables : TablesRep σ (compileNumericStmt (.peek k width table next) fresh).tables)
    (hsafe : SafeExec capacity (.peek k width table next) c)
    (hnext : ∀ τ,
      NumericRep τ capacity
        { c with state := (table.getD
            (c.state * width + headCode (c.stackData k)) 0) } →
      TablesRep τ (compileNumericStmt next (fresh + 1)).tables →
      ∃ τ' cost, BigStep (compileNumericStmt next (fresh + 1)).com τ τ' cost ∧
        NumericRep τ' capacity
          (next.exec { c with state := (table.getD
            (c.state * width + headCode (c.stackData k)) 0) })) :
    ∃ σ' cost, BigStep (compileNumericStmt (.peek k width table next) fresh).com σ σ' cost ∧
      NumericRep σ' capacity ((NumericStmt.peek k width table next).exec c) := by
  let idx := c.state * width + headCode (c.stackData k)
  let v := table.getD idx 0
  have hs : idx < table.length := by simpa [SafeExec, idx] using hsafe.1
  have harr : σ.arrs (tableName fresh) = table := by
    apply htables (tableName fresh) table
    simp [compileNumericStmt]
  obtain ⟨σ₁, costHead, hreadHead, hrep₁, hhead, harrs₁⟩ :=
    readHead_correct k capacity c σ hrep
  let σ₂ := σ₁.setVar indexVar idx
  have hindex : BigStep
      (.assign indexVar
        (.add (.mul (.var stateVar) (.lit width)) (.var headVar))) σ₁ σ₂ 6 := by
    apply BigStep.assign
    simp [Expr.eval, σ₂, idx, hrep₁.1, hhead]
  have hrep₂ : NumericRep σ₂ capacity c := hrep₁.setIndex σ₁ capacity c idx
  have hget : (σ₂.arrs (tableName fresh))[idx]? = some v := by
    rw [show σ₂.arrs = σ.arrs by exact harrs₁, harr]
    exact getElem?_eq_getD hs
  let σ₃ := σ₂.setVar stateVar v
  have hreadTable : BigStep
      (tableRead (tableName fresh) stateVar (.var indexVar)) σ₂ σ₃ 3 := by
    apply tableRead_bigStep σ₂ (tableName fresh) stateVar (.var indexVar) idx v
    · simp [σ₂]
    · exact hget
  have hrep₃ : NumericRep σ₃ capacity { c with state := v } :=
    hrep₂.setState σ₂ capacity c v
  have htail : TablesRep σ (compileNumericStmt next (fresh + 1)).tables :=
    TablesRep.tail (by simpa [compileNumericStmt] using htables)
  have htail₁ : TablesRep σ₁ (compileNumericStmt next (fresh + 1)).tables := by
    intro name values hm
    rw [show σ₁.arrs = σ.arrs by exact harrs₁]
    exact htail name values hm
  have htables₃ : TablesRep σ₃ (compileNumericStmt next (fresh + 1)).tables := by
    exact (htail₁.setVar indexVar idx).setVar stateVar v
  obtain ⟨σ₄, costNext, hrunNext, hfinal⟩ := hnext σ₃ hrep₃ htables₃
  refine ⟨σ₄, costHead + (6 + (3 + (costNext + 1))), ?_, ?_⟩
  · simp only [compileNumericStmt, seqs]
    exact .seq hreadHead (.seq hindex (.seq hreadTable (.seq hrunNext .skip)))
  · simpa [NumericStmt.exec, idx, v] using hfinal

/-- The destructive stack-head (`pop`) compiler case. -/
theorem compileNumericStmt_pop_correct (k width : ℕ) (table : List ℕ)
    (next : NumericStmt) (fresh : ℕ) (capacity : ℕ → ℕ)
    (c : NumericMachineState) (σ : Env)
    (hrep : NumericRep σ capacity c)
    (htables : TablesRep σ (compileNumericStmt (.pop k width table next) fresh).tables)
    (hsafe : SafeExec capacity (.pop k width table next) c)
    (hnext : ∀ τ,
      NumericRep τ capacity
        { c with
          stackData := Function.update c.stackData k (c.stackData k).tail
          state := table.getD (c.state * width + headCode (c.stackData k)) 0 } →
      TablesRep τ (compileNumericStmt next (fresh + 1)).tables →
      ∃ τ' cost, BigStep (compileNumericStmt next (fresh + 1)).com τ τ' cost ∧
        NumericRep τ' capacity
          (next.exec { c with
            stackData := Function.update c.stackData k (c.stackData k).tail
            state := table.getD (c.state * width + headCode (c.stackData k)) 0 })) :
    ∃ σ' cost, BigStep (compileNumericStmt (.pop k width table next) fresh).com σ σ' cost ∧
      NumericRep σ' capacity ((NumericStmt.pop k width table next).exec c) := by
  let idx := c.state * width + headCode (c.stackData k)
  let v := table.getD idx 0
  let cp := { c with stackData := Function.update c.stackData k (c.stackData k).tail }
  have hs : idx < table.length := by simpa [SafeExec, idx] using hsafe.1
  have harr : σ.arrs (tableName fresh) = table := by
    apply htables (tableName fresh) table
    simp [compileNumericStmt]
  obtain ⟨σ₁, costHead, hreadHead, hrep₁, hhead, harrs₁⟩ :=
    readHeadAndPop_correct k capacity c σ hrep
  let σ₂ := σ₁.setVar indexVar idx
  have hindex : BigStep
      (.assign indexVar
        (.add (.mul (.var stateVar) (.lit width)) (.var headVar))) σ₁ σ₂ 6 := by
    apply BigStep.assign
    simp [Expr.eval, σ₂, idx, hrep₁.1, hhead]
  have hrep₂ : NumericRep σ₂ capacity cp := hrep₁.setIndex σ₁ capacity cp idx
  have hget : (σ₂.arrs (tableName fresh))[idx]? = some v := by
    rw [show σ₂.arrs = σ.arrs by exact harrs₁, harr]
    exact getElem?_eq_getD hs
  let σ₃ := σ₂.setVar stateVar v
  have hreadTable : BigStep
      (tableRead (tableName fresh) stateVar (.var indexVar)) σ₂ σ₃ 3 := by
    apply tableRead_bigStep σ₂ (tableName fresh) stateVar (.var indexVar) idx v
    · simp [σ₂]
    · exact hget
  have hrep₃ : NumericRep σ₃ capacity { cp with state := v } :=
    hrep₂.setState σ₂ capacity cp v
  have htail : TablesRep σ (compileNumericStmt next (fresh + 1)).tables :=
    TablesRep.tail (by simpa [compileNumericStmt] using htables)
  have htail₁ : TablesRep σ₁ (compileNumericStmt next (fresh + 1)).tables := by
    intro name values hm
    rw [show σ₁.arrs = σ.arrs by exact harrs₁]
    exact htail name values hm
  have htables₃ : TablesRep σ₃ (compileNumericStmt next (fresh + 1)).tables := by
    exact (htail₁.setVar indexVar idx).setVar stateVar v
  obtain ⟨σ₄, costNext, hrunNext, hfinal⟩ := hnext σ₃ hrep₃ htables₃
  refine ⟨σ₄, costHead + (6 + (3 + (costNext + 1))), ?_, ?_⟩
  · simp only [compileNumericStmt, seqs]
    exact .seq hreadHead (.seq hindex (.seq hreadTable (.seq hrunNext .skip)))
  · simpa [NumericStmt.exec, idx, v, cp] using hfinal

/-- The stack-push compiler case. -/
theorem compileNumericStmt_push_correct (k : ℕ) (table : List ℕ)
    (next : NumericStmt) (fresh : ℕ) (capacity : ℕ → ℕ)
    (c : NumericMachineState) (σ : Env)
    (hrep : NumericRep σ capacity c)
    (htables : TablesRep σ (compileNumericStmt (.push k table next) fresh).tables)
    (hsafe : SafeExec capacity (.push k table next) c)
    (hnext : ∀ τ,
      NumericRep τ capacity
        { c with stackData := (Function.update c.stackData k
            (table.getD c.state 0 :: c.stackData k)) } →
      TablesRep τ (compileNumericStmt next (fresh + 1)).tables →
      ∃ τ' cost, BigStep (compileNumericStmt next (fresh + 1)).com τ τ' cost ∧
        NumericRep τ' capacity
          (next.exec { c with stackData := (Function.update c.stackData k
            (table.getD c.state 0 :: c.stackData k)) })) :
    ∃ σ' cost, BigStep (compileNumericStmt (.push k table next) fresh).com σ σ' cost ∧
      NumericRep σ' capacity ((NumericStmt.push k table next).exec c) := by
  let v := table.getD c.state 0
  have hs : c.state < table.length := hsafe.1
  have hroom : (c.stackData k).length < capacity k := hsafe.2.1
  have harr : σ.arrs (tableName fresh) = table := by
    apply htables (tableName fresh) table
    simp [compileNumericStmt]
  have hget : (σ.arrs (tableName fresh))[c.state]? = some v := by
    rw [harr]
    exact getElem?_eq_getD hs
  let σ₁ := σ.setVar tempVar v
  have hread : BigStep
      (tableRead (tableName fresh) tempVar (.var stateVar)) σ σ₁ 3 := by
    apply tableRead_bigStep σ (tableName fresh) tempVar (.var stateVar) c.state v
    · simpa [hrep.1]
    · exact hget
  have hrep₁ : NumericRep σ₁ capacity c := hrep.setTemp σ capacity c v
  let σ₂ := σ₁.setArr (stackName k) (c.stackData k).length v
  have hstore : BigStep
      (.store (stackName k) (.var (topName k)) (.var tempVar)) σ₁ σ₂ 3 := by
    apply BigStep.store
    · simpa [hrep₁.2.2 k |>.top_eq]
    · simp [σ₁]
    · rw [(hrep₁.2.2 k).length_eq]
      exact hroom
  let σ₃ := σ₂.setVar (topName k) ((c.stackData k).length + 1)
  have htop : BigStep
      (.assign (topName k) (.add (.var (topName k)) (.lit 1))) σ₂ σ₃ 4 := by
    apply BigStep.assign
    simp [Expr.eval, σ₂, hrep₁.2.2 k |>.top_eq]
  have hrep₃ : NumericRep σ₃ capacity
      { c with stackData := (Function.update c.stackData k (v :: c.stackData k)) } := by
    exact hrep₁.push σ₁ capacity c k v hroom
  have htail : TablesRep σ (compileNumericStmt next (fresh + 1)).tables :=
    TablesRep.tail (by simpa [compileNumericStmt] using htables)
  have htables₃ : TablesRep σ₃ (compileNumericStmt next (fresh + 1)).tables := by
    exact ((htail.setVar tempVar v).setStackArr).setVar (topName k)
      ((c.stackData k).length + 1)
  obtain ⟨σ₄, costNext, hrunNext, hfinal⟩ := hnext σ₃ hrep₃ htables₃
  refine ⟨σ₄, 3 + (3 + (4 + (costNext + 1))), ?_, ?_⟩
  · simp only [compileNumericStmt, seqs]
    exact .seq hread (.seq hstore (.seq htop (.seq hrunNext .skip)))
  · simpa [NumericStmt.exec, v] using hfinal

/-- Structural correctness of the complete normalized-statement compiler. -/
theorem compileNumericStmt_correct (q : NumericStmt) (fresh : ℕ)
    (capacity : ℕ → ℕ) (c : NumericMachineState) (σ : Env)
    (hrep : NumericRep σ capacity c)
    (htables : TablesRep σ (compileNumericStmt q fresh).tables)
    (hsafe : SafeExec capacity q c) :
    ∃ σ' cost, BigStep (compileNumericStmt q fresh).com σ σ' cost ∧
      NumericRep σ' capacity (q.exec c) := by
  induction q generalizing fresh c σ with
  | push k table next ih =>
      apply compileNumericStmt_push_correct k table next fresh capacity c σ
        hrep htables hsafe
      intro τ hrep' htables'
      exact ih (fresh := fresh + 1) (c := _ ) (σ := τ)
        hrep' htables' hsafe.2.2
  | peek k width table next ih =>
      apply compileNumericStmt_peek_correct k width table next fresh capacity c σ
        hrep htables hsafe
      intro τ hrep' htables'
      exact ih (fresh := fresh + 1) (c := _) (σ := τ)
        hrep' htables' hsafe.2
  | pop k width table next ih =>
      apply compileNumericStmt_pop_correct k width table next fresh capacity c σ
        hrep htables hsafe
      intro τ hrep' htables'
      exact ih (fresh := fresh + 1) (c := _) (σ := τ)
        hrep' htables' (by simpa [SafeExec] using hsafe.2)
  | load table next ih =>
      apply compileNumericStmt_load_correct table next fresh capacity c σ
        hrep htables hsafe
      intro τ hrep' htables'
      exact ih (fresh := fresh + 1) (c := _) (σ := τ)
        hrep' htables' hsafe.2
  | branch table yes no ihYes ihNo =>
      apply compileNumericStmt_branch_correct table yes no fresh capacity c σ
        hrep htables hsafe
      · intro τ hrep' htables' hsafe'
        exact ihYes (fresh := fresh + 1) (c := c) (σ := τ)
          hrep' htables' hsafe'
      · intro τ hrep' htables' hsafe'
        exact ihNo
          (fresh := (compileNumericStmt yes (fresh + 1)).nextTable)
          (c := c) (σ := τ) hrep' htables' hsafe'
  | goto table =>
      exact compileNumericStmt_goto_correct table fresh capacity c σ hrep htables hsafe
  | halt =>
      exact compileNumericStmt_halt_correct fresh capacity c σ hrep

/-- Compiled statements never write to any literal transition-table array. -/
theorem tableName_not_mem_compileNumericStmt_warrs (q : NumericStmt)
    (fresh i : ℕ) :
    tableName i ∉ (compileNumericStmt q fresh).com.warrs := by
  induction q generalizing fresh with
  | push k table next ih =>
      simp [compileNumericStmt, tableRead, seqs, Com.warrs, tableName_ne_stackName, ih]
  | peek k width table next ih =>
      simp [compileNumericStmt, tableRead, readHead, seqs, Com.warrs, ih]
  | pop k width table next ih =>
      simp [compileNumericStmt, tableRead, readHeadAndPop, seqs, Com.warrs, ih]
  | load table next ih => simp [compileNumericStmt, tableRead, Com.warrs, ih]
  | branch table yes no ihy ihn =>
      simp [compileNumericStmt, tableRead, Com.warrs, ihy, ihn]
  | goto table => simp [compileNumericStmt, tableRead, seqs, Com.warrs]
  | halt => simp [compileNumericStmt, Com.warrs]

/-- Therefore the table representation used for an instruction remains true
after that compiled instruction executes. -/
theorem TablesRep.preserved_compileNumericStmt {q : NumericStmt} {fresh : ℕ}
    {σ σ' : Env} {cost : ℕ}
    (htables : TablesRep σ (compileNumericStmt q fresh).tables)
    (hrun : BigStep (compileNumericStmt q fresh).com σ σ' cost) :
    TablesRep σ' (compileNumericStmt q fresh).tables := by
  intro name values hm
  obtain ⟨i, rfl⟩ := compileNumericStmt_tables_name q fresh name values hm
  rw [hrun.arrs_eq (tableName_not_mem_compileNumericStmt_warrs q fresh i)]
  exact htables (tableName i) values hm

end Lax51Proofs.TMToRam
