import Lax51Proofs.Computability.NumericRuntime
import Lax51Proofs.Computability.PartrecNativeCodec
import Mathlib.Computability.RE

namespace Lax51Proofs.Computability

open Turing Lax51Proofs.TMToRam
open PartrecFiniteTM2
open PartrecNativeCodec

set_option maxHeartbeats 2000000

/-! Computable input encoding and running-time search for the finite
`ToPartrec` evaluator. -/

def bitsStrongStep (_a : ℕ) (previous : List (List Bool)) :
    Option (List Bool) :=
  let n := previous.length
  if n = 0 then some []
  else some (n.bodd :: previous.getD n.div2 [])

theorem bitsStrongStep_primrec₂ : Primrec₂ bitsStrongStep := by
  have hn : Primrec fun q : ℕ × List (List Bool) => q.2.length :=
    Primrec.list_length.comp Primrec.snd
  have hprevious : Primrec fun q : ℕ × List (List Bool) =>
      q.2.getD q.2.length.div2 [] :=
    (Primrec.list_getD ([] : List Bool)).comp Primrec.snd
      (Primrec.nat_div2.comp hn)
  have hcons : Primrec fun q : ℕ × List (List Bool) =>
      q.2.length.bodd :: q.2.getD q.2.length.div2 [] :=
    Primrec.list_cons.comp (Primrec.nat_bodd.comp hn) hprevious
  exact Primrec.ite (Primrec.eq.comp hn (Primrec.const 0))
    (Primrec.const (some [])) (Primrec.option_some.comp hcons)

theorem bitsStrongStep_range (a n : ℕ) :
    bitsStrongStep a ((List.range n).map Nat.bits) = some n.bits := by
  by_cases hn : n = 0
  · subst n
    rfl
  · have hhalf : n.div2 < n := Nat.binaryRec_decreasing hn
    have hget : ((List.range n).map Nat.bits).getD n.div2 [] =
        n.div2.bits := by
      simp [List.getD_eq_getElem?_getD, hhalf]
    unfold bitsStrongStep
    simp only [List.length_map, List.length_range, hn, if_false]
    rw [hget, Nat.bodd_eq_bits_head, Nat.div2_bits_eq_tail]
    cases hbits : n.bits with
    | nil =>
        have hlen : n.bits.length = 0 := by simp [hbits]
        rw [Nat.size_eq_bits_len] at hlen
        have : n = 0 := Nat.size_eq_zero.mp hlen
        contradiction
    | cons b bs => rfl

theorem nat_bits_primrec : Primrec Nat.bits := by
  have htwo : Primrec₂ fun (_a : ℕ) (n : ℕ) => n.bits :=
    Primrec.nat_strong_rec (fun (_a : ℕ) n => n.bits)
      bitsStrongStep_primrec₂ bitsStrongStep_range
  exact htwo.comp (Primrec.const 0) Primrec.id

theorem boolDigitCode_primrec (zeroCode oneCode : ℕ) :
    Primrec (boolDigitCode zeroCode oneCode) :=
  Primrec.dom_bool _

theorem encodePartrecNatCodes_primrec (consCode zeroCode oneCode : ℕ) :
    Primrec (encodePartrecNatCodes consCode zeroCode oneCode) := by
  have hmap : Primrec fun n : ℕ =>
      n.bits.map (boolDigitCode zeroCode oneCode) :=
    Primrec.list_map nat_bits_primrec
      ((boolDigitCode_primrec zeroCode oneCode).comp Primrec.snd).to₂
  exact (Primrec.list_append.comp hmap
    (Primrec.const [consCode])).of_eq fun _ => rfl

theorem encodePartrecListCodes_primrec (consCode zeroCode oneCode : ℕ) :
    Primrec (encodePartrecListCodes consCode zeroCode oneCode) := by
  have hflat : Primrec fun xs : List ℕ =>
      xs.flatMap (encodePartrecNatCodes consCode zeroCode oneCode) :=
    Primrec.list_flatMap Primrec.id
      ((encodePartrecNatCodes_primrec consCode zeroCode oneCode).comp
        Primrec.snd).to₂
  exact hflat.of_eq fun xs => by
    induction xs with
    | nil => rfl
    | cons n ns => simp [encodePartrecListCodes, *]

noncomputable def partrecSparseInit (c : ToPartrec.Code) (v : List ℕ) :
    SparseNumericState :=
  let tm := machine c
  { label := some (@finCode tm.Λ tm.ΛFin (Classical.decEq tm.Λ) tm.main)
    state := @finCode tm.σ tm.σFin (Classical.decEq tm.σ) tm.initialState
    stackData := [
      (@finCode tm.K tm.kFin tm.kDecidableEq tm.k₀,
        encodePartrecListCodes (symbolCode c .cons)
          (symbolCode c .bit0) (symbolCode c .bit1) v)] }

theorem partrecSparseInit_primrec (c : ToPartrec.Code) :
    Primrec (partrecSparseInit c) := by
  let tm := machine c
  let inputStack := @finCode tm.K tm.kFin tm.kDecidableEq tm.k₀
  let codes := encodePartrecListCodes (symbolCode c .cons)
    (symbolCode c .bit0) (symbolCode c .bit1)
  have hcodes : Primrec codes :=
    encodePartrecListCodes_primrec (symbolCode c .cons)
      (symbolCode c .bit0) (symbolCode c .bit1)
  have hstacks : Primrec fun v : List ℕ =>
      [(inputStack, codes v)] :=
    Primrec.list_cons.comp
      (Primrec.pair (Primrec.const inputStack) hcodes)
      (Primrec.const [])
  exact (sparseNumericState_mk_primrec
    (Primrec.const (some
      (@finCode tm.Λ tm.ΛFin (Classical.decEq tm.Λ) tm.main)))
    (Primrec.const
      (@finCode tm.σ tm.σFin (Classical.decEq tm.σ) tm.initialState))
    hstacks).of_eq fun v => by
      simp [partrecSparseInit, tm, inputStack, codes]

theorem partrecSparseInit_toNumeric (c : ToPartrec.Code) (v : List ℕ) :
    (partrecSparseInit c v).toNumeric =
      FinTM2.encodeNumericState (machine c)
        (Turing.initList (machine c) (Turing.PartrecToTM2.trList v))
        (FinTM2.initList_stacksWithin (machine c)
          (Turing.PartrecToTM2.trList v)) := by
  let tm := machine c
  let input := Turing.PartrecToTM2.trList v
  let hc := FinTM2.initList_stacksWithin tm input
  let inputStack := @finCode tm.K tm.kFin tm.kDecidableEq tm.k₀
  let codes := encodePartrecListCodes (symbolCode c .cons)
    (symbolCode c .bit0) (symbolCode c .bit1) v
  apply NumericMachineState.ext
  · simp [partrecSparseInit, SparseNumericState.toNumeric,
      FinTM2.encodeNumericState, Turing.initList, tm]
  · simp [partrecSparseInit, SparseNumericState.toNumeric,
      FinTM2.encodeNumericState, Turing.initList, FinTM2.stateCode, tm]
  · funext j
    by_cases hj : j = inputStack
    · subst j
      have havail : ∀ a ∈ input,
          (⟨tm.k₀, a⟩ : Σ k, tm.Γ k) ∈ FinTM2.availableSymbols tm := by
        intro a ha
        exact hc tm.k₀ a (by simpa [Turing.initList, input] using ha)
      have hcodeStack :
          FinTM2.codeStack tm tm.k₀ input havail = codes := by
        simpa [tm, input, codes] using codeStack_trList c v havail
      rw [FinTM2.encodeNumericState_stack]
      change sparseStackLookup [(inputStack, codes)] inputStack =
        FinTM2.codeStack tm tm.k₀ input _
      simp only [sparseStackLookup, List.lookup_cons_self, Option.getD_some]
      exact hcodeStack.symm
    · have hleft : sparseStackLookup
          [(inputStack, codes)] j = [] := by
        have hb : (j == inputStack) = false :=
          beq_eq_false_iff_ne.mpr hj
        simp only [sparseStackLookup, List.lookup_cons, hb,
          Option.getD_none]
        rfl
      rw [show (partrecSparseInit c v).toNumeric.stackData j = [] by
        simpa [partrecSparseInit, SparseNumericState.toNumeric, tm,
          inputStack, codes] using hleft]
      simp only [FinTM2.encodeNumericState, FinTM2.codeStackFamily]
      split
      · rfl
      · rename_i k hdecode
        have hkcode : @finCode tm.K tm.kFin tm.kDecidableEq k = j :=
          @finCode_of_finDecode_eq_some tm.K tm.kFin tm.kDecidableEq
            j k hdecode
        have hk : k ≠ tm.k₀ := by
          intro heq
          apply hj
          calc
            j = @finCode tm.K tm.kFin tm.kDecidableEq k := hkcode.symm
            _ = @finCode tm.K tm.kFin tm.kDecidableEq tm.k₀ :=
              congrArg (fun z => @finCode tm.K tm.kFin tm.kDecidableEq z) heq
            _ = inputStack := rfl
        change [] = FinTM2.codeStack tm k ((Turing.initList tm input).stk k) _
        simp [FinTM2.codeStack, Turing.initList, hk]

def sparseNumericHalted : Option SparseNumericState → Bool
  | none => false
  | some c => !c.label.isSome

theorem sparseNumericHalted_primrec : Primrec sparseNumericHalted := by
  have hs : Primrec fun c : SparseNumericState => !c.label.isSome :=
    (Primrec.dom_bool Bool.not).comp
      (Primrec.option_isSome.comp sparseNumericState_label_primrec)
  exact (Primrec.option_casesOn Primrec.id (Primrec.const false)
    (hs.comp Primrec.snd).to₂).of_eq fun oc => by cases oc <;> rfl

noncomputable def partrecPhysicalHaltedBool (c : ToPartrec.Code)
    (x : List ℕ) (t : ℕ) : Bool :=
  sparseNumericHalted
    (sparseNumericIter (machine c) t (partrecSparseInit c (x.length :: x)))

theorem partrecPhysicalHaltedBool_primrec₂ (c : ToPartrec.Code) :
    Primrec₂ (partrecPhysicalHaltedBool c) := by
  have hprefixed : Primrec fun x : List ℕ => x.length :: x :=
    Primrec.list_cons.comp (Primrec.list_length.comp Primrec.id) Primrec.id
  have hinit : Primrec fun x : List ℕ =>
      partrecSparseInit c (x.length :: x) :=
    (partrecSparseInit_primrec c).comp hprefixed
  have hiter : Primrec fun q : List ℕ × ℕ =>
      sparseNumericIter (machine c) q.2
        (partrecSparseInit c (q.1.length :: q.1)) :=
    (sparseNumericIter_primrec (machine c)).comp
      (Primrec.pair Primrec.snd (hinit.comp Primrec.fst))
  exact (sparseNumericHalted_primrec.comp hiter).to₂

def PartrecPhysicalHaltsAt (c : ToPartrec.Code) (x : List ℕ) (t : ℕ) :
    Prop :=
  partrecPhysicalHaltedBool c x t = true

theorem partrecPhysicalHaltsAt_computablePred (c : ToPartrec.Code) :
    ComputablePred fun q : List ℕ × ℕ =>
      PartrecPhysicalHaltsAt c q.1 q.2 := by
  letI : DecidablePred fun q : List ℕ × ℕ =>
      PartrecPhysicalHaltsAt c q.1 q.2 := by
    intro q
    unfold PartrecPhysicalHaltsAt
    infer_instance
  apply Computable.computablePred
  simpa [PartrecPhysicalHaltsAt] using
    ((partrecPhysicalHaltedBool_primrec₂ c).comp Primrec.fst
      Primrec.snd).to_comp

theorem optionIter_positive_of_halt {A : Type} (step : A → Option A)
    {a : A} (ha : step a = none) {n : ℕ} (hn : 0 < n) :
    ((fun o : Option A => o.bind step)^[n]) (some a) = none := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [Function.iterate_succ_apply]
  change ((fun o : Option A => o.bind step)^[n]) (step a) = none
  rw [ha]
  exact Lax51Proofs.TMToRam.iterate_bind_none step n

theorem optionIter_halt_time_unique {A : Type} (step : A → Option A)
    {start a b : A} {t u : ℕ}
    (ht : ((fun o : Option A => o.bind step)^[t]) (some start) = some a)
    (ha : step a = none)
    (hu : ((fun o : Option A => o.bind step)^[u]) (some start) = some b)
    (hb : step b = none) : t = u := by
  rcases lt_trichotomy t u with hlt | heq | hgt
  · have heu : u = (u - t) + t := by omega
    rw [heu, Function.iterate_add_apply, ht] at hu
    rw [optionIter_positive_of_halt step ha (by omega)] at hu
    contradiction
  · exact heq
  · have het : t = (t - u) + u := by omega
    rw [het, Function.iterate_add_apply, hu] at ht
    rw [optionIter_positive_of_halt step hb (by omega)] at ht
    contradiction

theorem partrecSparseHalt_of_eval {c : ToPartrec.Code}
    {v out : List ℕ} (h : c.eval v = pure out) :
    ∃ s : SparseNumericState,
      sparseNumericIter (machine c) (PartrecFiniteTM2.outputs h).steps
          (partrecSparseInit c v) = some s ∧
        s.label = none := by
  let tm := machine c
  let input := Turing.PartrecToTM2.trList v
  let output := Turing.PartrecToTM2.trList out
  let typed := PartrecFiniteTM2.outputs h
  let hc := FinTM2.initList_stacksWithin tm input
  obtain ⟨hhalt, hnum⟩ := FinTM2.numeric_iterate_encode tm typed.steps
    (Turing.initList tm input) (Turing.haltList tm output) hc
    (by simpa [typed, tm, input, output] using typed.evals_in_steps)
  change ((numericStepOption tm)^[typed.steps])
      (some (FinTM2.encodeNumericState tm (Turing.initList tm input) hc)) =
    some (FinTM2.encodeNumericState tm (Turing.haltList tm output) hhalt) at hnum
  have hsparse := sparseNumericIter_toNumeric tm typed.steps
    (partrecSparseInit c v)
  rw [partrecSparseInit_toNumeric c v] at hsparse
  change Option.map SparseNumericState.toNumeric
      (sparseNumericIter tm typed.steps (partrecSparseInit c v)) =
    ((numericStepOption tm)^[typed.steps])
      (some (FinTM2.encodeNumericState tm (Turing.initList tm input) hc)) at hsparse
  rw [hnum] at hsparse
  cases hs : sparseNumericIter tm typed.steps (partrecSparseInit c v) with
  | none => simp [hs] at hsparse
  | some s =>
      refine ⟨s, rfl, ?_⟩
      have hstate : s.toNumeric =
          FinTM2.encodeNumericState tm (Turing.haltList tm output) hhalt := by
        simpa [hs] using hsparse
      have hlabel := congrArg NumericMachineState.label hstate
      simpa [SparseNumericState.toNumeric, FinTM2.encodeNumericState,
        Turing.haltList] using hlabel

theorem partrecPhysicalHaltsAt_exists {c : ToPartrec.Code}
    {f : List ℕ → List ℕ}
    (h : ∀ x, c.eval (x.length :: x) = pure (f x)) :
    ∀ x, ∃ t, PartrecPhysicalHaltsAt c x t := by
  intro x
  obtain ⟨s, hs, hlabel⟩ := partrecSparseHalt_of_eval (h x)
  refine ⟨(PartrecFiniteTM2.outputs (h x)).steps, ?_⟩
  simp [PartrecPhysicalHaltsAt, partrecPhysicalHaltedBool,
    sparseNumericHalted, hs, hlabel]

end Lax51Proofs.Computability
