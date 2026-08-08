import Lax20Proofs.RamToTM.WrapperEmbedding

namespace Lax20Proofs.RamToTM

open Turing TM2
open Lax20.BinaryWordEncoding

noncomputable section

theorem fixedBits_eq_bits_append_replicate {w n : Nat} (h : n < 2 ^ w) :
    fixedBits w n = n.bits ++ List.replicate (w - n.bits.length) false := by
  induction w generalizing n with
  | zero =>
      have hn : n = 0 := by simpa using h
      subst n
      rfl
  | succ w ih =>
      by_cases hn : n = 0
      · subst n
        simp [fixedBits, List.replicate_succ]
      · have hd : n.div2 < 2 ^ w := by
          rw [← Nat.bit_bodd_div2 n] at h
          simp only [pow_succ] at h
          cases n.bodd <;> simp [Nat.bit_val] at h ⊢ <;> omega
        have htail := ih hd
        have hbits : n.bits = n.bodd :: n.div2.bits := by
          rw [← Nat.bit_bodd_div2 n]
          simpa [Nat.bodd_bit, Nat.div2_bit] using
            (Nat.bits_append_bit n.div2 n.bodd (by
          intro hz
          have : n.bodd = true := by
            have hbit : Nat.bit n.bodd 0 = n := by
              simpa [hz] using Nat.bit_bodd_div2 n
            cases hb : n.bodd
            · simp [Nat.bit, hb] at hbit
              exact False.elim (hn hbit.symm)
            · rfl
          exact this))
        have hlen : n.div2.bits.length <= w := by
          have := congrArg List.length htail
          simp only [fixedBits_length, List.length_append,
            List.length_replicate] at this
          omega
        rw [fixedBits, htail, hbits]
        simp only [List.cons_append, List.length_cons]
        congr 2
        simpa [Nat.add_comm] using congrArg
          (fun k => List.replicate k false)
          (Nat.succ_sub_succ_eq_sub w n.div2.bits.length).symm

def trimHighZeros (bitsMSB : List Bool) : List Bool :=
  (bitsMSB.dropWhile (· = false)).reverse

theorem dropWhile_false_reverse_bits (n : Nat) :
    (n.bits.reverse.dropWhile (· = false)).reverse = n.bits := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simp
      · have hdiv : n.div2 < n := by
          rw [Nat.div2_val]
          exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero hn) (by omega)
        have htail := ih n.div2 hdiv
        have hbit : n.bits = n.bodd :: n.div2.bits := by
          calc
            n.bits = (Nat.bit n.bodd n.div2).bits :=
              congrArg Nat.bits (Nat.bit_bodd_div2 n).symm
            _ = n.bodd :: n.div2.bits := Nat.bits_append_bit _ _ (by
              intro hz
              have heq : Nat.bit n.bodd 0 = n := by
                simpa [hz] using Nat.bit_bodd_div2 n
              cases hb : n.bodd
              · simp [Nat.bit, hb] at heq
                exact False.elim (hn heq.symm)
              · rfl)
        by_cases hz : n.div2 = 0
        · have hb : n.bodd = true := by
            have heq : Nat.bit n.bodd 0 = n := by
              simpa [hz] using Nat.bit_bodd_div2 n
            cases hb : n.bodd
            · simp [Nat.bit, hb] at heq
              exact False.elim (hn heq.symm)
            · rfl
          simp [hbit, hz, hb]
        · rw [hbit, List.reverse_cons, List.dropWhile_append]
          have hnonempty : n.div2.bits.reverse.isEmpty = false := by
            have hne : n.div2.bits ≠ [] := by
              have hmBits : n.div2.bits =
                  n.div2.bodd :: n.div2.div2.bits := by
                calc
                  n.div2.bits = (Nat.bit n.div2.bodd n.div2.div2).bits :=
                    congrArg Nat.bits (Nat.bit_bodd_div2 n.div2).symm
                  _ = _ := Nat.bits_append_bit _ _ (by
                    intro hzero
                    have heq : Nat.bit n.div2.bodd 0 = n.div2 := by
                      simpa [hzero] using Nat.bit_bodd_div2 n.div2
                    cases hb : n.div2.bodd
                    · simp [Nat.bit, hb] at heq
                      exact False.elim (hz heq.symm)
                    · rfl)
              rw [hmBits]
              simp
            simp [hne]
          rw [show n.div2.bits.reverse.dropWhile (· = false) =
              n.div2.bits.reverse by
            have := congrArg List.reverse htail
            simpa using this]
          simp [hnonempty]

theorem trimHighZeros_fixedBits_reverse {w n : Nat} (h : n < 2 ^ w) :
    trimHighZeros (fixedBits w n).reverse = n.bits := by
  rw [fixedBits_eq_bits_append_replicate h]
  unfold trimHighZeros
  rw [List.reverse_append, List.reverse_replicate]
  rw [List.dropWhile_append_of_pos (by intro a ha; simp at ha ⊢; exact ha.2)]
  exact dropWhile_false_reverse_bits n

inductive CleanupStack
  | input
  | core (stack : CoreStack)
  deriving DecidableEq, Fintype, Inhabited

def cleanupStack : CleanupStack -> WrapperStack
  | .input => .input
  | .core stack => .core stack

def nextCleanupStack : CleanupStack -> Option CleanupStack
  | .input => some (.core .accumulator)
  | .core .accumulator => some (.core .memory)
  | .core .memory => some (.core .input)
  | .core .input => some (.core .output)
  | .core .output => some (.core .work0)
  | .core .work0 => some (.core .work1)
  | .core .work1 => some (.core .work2)
  | .core .work2 => some (.core .work3)
  | .core .work3 => some (.core .work4)
  | .core .work4 => some (.core .work5)
  | .core .work5 => some (.core .work6)
  | .core .work6 => some (.core .work7)
  | .core .work7 => none

inductive OutputAdapterLabel
  | initialize
  | scan
  | decide
  | bit
  | delimiter
  | finish
  | cleanupPeek (stack : CleanupStack)
  | cleanupPop (stack : CleanupStack)
  | halt
  deriving DecidableEq, Fintype, Inhabited

def outputAdapterProgram {N : Nat} {L : Type} : OutputAdapterLabel ->
    TM2.Stmt WrapperAlphabet (Sum L OutputAdapterLabel) (WrapperState N)
  | .initialize =>
      .load (fun s => {s with heldSparse := none, flag := false, active := false}) <|
      .goto fun _ => .inr .scan
  | .scan =>
      .pop (.core .output) (fun s a => {s with heldSparse := a}) <|
      .goto fun _ => .inr .decide
  | .decide =>
      .branch (fun s => s.heldSparse = some .outputEnd)
        (.goto fun _ => .inr .finish) <|
      .branch (fun s => s.heldSparse = some .wordEnd)
        (.goto fun _ => .inr .delimiter) <|
      .goto fun _ => .inr .bit
  | .bit =>
      .branch (fun s => s.heldSparse = some (.bit true))
        (.push .output (fun _ => .one) <|
          .load (fun s => {s with heldSparse := none, flag := true}) <|
          .goto fun _ => .inr .scan) <|
      .branch (fun s => s.flag)
        (.push .output (fun _ => .zero) <|
          .load (fun s => {s with heldSparse := none}) <|
          .goto fun _ => .inr .scan)
        (.load (fun s => {s with heldSparse := none}) <|
          .goto fun _ => .inr .scan)
  | .delimiter =>
      .branch (fun s => s.active)
        (.push .output (fun _ => .separator) <|
          .load (fun s => {s with heldSparse := none, flag := false, active := true}) <|
          .goto fun _ => .inr .scan)
        (.load (fun s => {s with heldSparse := none, flag := false, active := true}) <|
          .goto fun _ => .inr .scan)
  | .finish =>
      .branch (fun s => s.active)
        (.push .output (fun _ => .separator) <|
          .goto fun _ => .inr (.cleanupPeek .input))
        (.goto fun _ => .inr (.cleanupPeek .input))
  | .cleanupPeek stack =>
      .peek (cleanupStack stack)
        (fun s a => {s with flag := a.isSome}) <|
      .branch (fun s => s.flag)
        (.goto fun _ => .inr (.cleanupPop stack)) <|
      match nextCleanupStack stack with
      | some next => .goto fun _ => .inr (.cleanupPeek next)
      | none => .goto fun _ => .inr .halt
  | .cleanupPop stack =>
      .pop (cleanupStack stack) (fun s _ => s) <|
      .goto fun _ => .inr (.cleanupPeek stack)
  | .halt =>
      .load (fun _ => default) .halt

def outputAdapterCfg {N : Nat} {L : Type} (label : OutputAdapterLabel)
    (state : WrapperState N)
    (tapes : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    TM2.Cfg WrapperAlphabet (Sum L OutputAdapterLabel) (WrapperState N) :=
  ⟨some (.inr label), state, tapes⟩

@[simp] theorem output_scan_step {N : Nat} {L : Type}
    (state : WrapperState N) (symbol : SparseSymbol)
    (tapes : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    TM2.step (liftCoreProgram (fun _ : Empty => .halt)
      (outputAdapterProgram (N := N) (L := Empty)))
      (outputAdapterCfg (L := Empty) .scan state
        (Function.update tapes (.core .output)
          (symbol :: tapes (.core .output)))) =
    some (outputAdapterCfg (L := Empty) .decide
      {state with heldSparse := some symbol}
      (Function.update tapes (.core .output) (tapes (.core .output)))) := by
  simp [outputAdapterCfg, liftCoreProgram, outputAdapterProgram, TM2.step] <;> rfl

@[simp] theorem output_decide_bit_step {N : Nat}
    (state : WrapperState N) (bit : Bool)
    (tapes : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    TM2.step (liftCoreProgram (fun _ : Empty => .halt)
      (outputAdapterProgram (N := N) (L := Empty)))
      (outputAdapterCfg (L := Empty) .decide
        {state with heldSparse := some (.bit bit)} tapes) =
    some (outputAdapterCfg (L := Empty) .bit
      {state with heldSparse := some (.bit bit)} tapes) := by
  simp [outputAdapterCfg, liftCoreProgram, outputAdapterProgram, TM2.step]

@[simp] theorem output_bit_true_step {N : Nat}
    (state : WrapperState N)
    (tapes : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    TM2.step (liftCoreProgram (fun _ : Empty => .halt)
      (outputAdapterProgram (N := N) (L := Empty)))
      (outputAdapterCfg (L := Empty) .bit
        {state with heldSparse := some (.bit true)} tapes) =
    some (outputAdapterCfg (L := Empty) .scan
      {state with heldSparse := none, flag := true}
      (Function.update tapes .output (.one :: tapes .output))) := by
  simp [outputAdapterCfg, liftCoreProgram, outputAdapterProgram, TM2.step]

@[simp] theorem output_bit_false_seen_step {N : Nat}
    (state : WrapperState N) (hseen : state.flag = true)
    (tapes : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    TM2.step (liftCoreProgram (fun _ : Empty => .halt)
      (outputAdapterProgram (N := N) (L := Empty)))
      (outputAdapterCfg (L := Empty) .bit
        {state with heldSparse := some (.bit false)} tapes) =
    some (outputAdapterCfg (L := Empty) .scan
      {state with heldSparse := none}
      (Function.update tapes .output (.zero :: tapes .output))) := by
  simp [outputAdapterCfg, liftCoreProgram, outputAdapterProgram, TM2.step, hseen]

@[simp] theorem output_bit_false_unseen_step {N : Nat}
    (state : WrapperState N) (hseen : state.flag = false)
    (tapes : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    TM2.step (liftCoreProgram (fun _ : Empty => .halt)
      (outputAdapterProgram (N := N) (L := Empty)))
      (outputAdapterCfg (L := Empty) .bit
        {state with heldSparse := some (.bit false)} tapes) =
    some (outputAdapterCfg (L := Empty) .scan
      {state with heldSparse := none} tapes) := by
  simp [outputAdapterCfg, liftCoreProgram, outputAdapterProgram, TM2.step, hseen]

def outputAdapterStacks (coreOutput : List SparseSymbol)
    (output : List Symbol)
    (base : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    (k : WrapperStack) -> List (WrapperAlphabet k) :=
  Function.update (Function.update base (.core .output) coreOutput) .output output

theorem outputAdapterStacks_cons (symbol : SparseSymbol)
    (rest : List SparseSymbol) (output : List Symbol)
    (base : (k : WrapperStack) → List (WrapperAlphabet k)) :
    outputAdapterStacks (symbol :: rest) output base =
      Function.update (outputAdapterStacks rest output base) (.core .output)
        (symbol :: outputAdapterStacks rest output base (.core .output)) := by
  funext k
  cases k with
  | input => simp [outputAdapterStacks, Function.update]
  | output => simp [outputAdapterStacks, Function.update]
  | core k =>
      cases k <;> simp [outputAdapterStacks, Function.update] <;> rfl

theorem update_coreOutput_same
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    Function.update tapes (.core .output) (tapes (.core .output)) = tapes := by
  funext k
  cases k with
  | input | output => simp [Function.update]
  | core k => cases k <;> simp [Function.update] <;> rfl

def scanOutputBits : Bool -> List Bool -> List Symbol -> Bool × List Symbol
  | seen, [], output => (seen, output)
  | seen, bit :: bits, output =>
      if bit then scanOutputBits true bits (.one :: output)
      else if seen then scanOutputBits true bits (.zero :: output)
      else scanOutputBits false bits output

@[simp] theorem scanOutputBits_nil (seen : Bool) (output : List Symbol) :
    scanOutputBits seen [] output = (seen, output) := rfl

def canonicalBitSymbol (bit : Bool) : Symbol :=
  if bit then .one else .zero

theorem scanOutputBits_true (bits : List Bool) (output : List Symbol) :
    scanOutputBits true bits output =
      (true, bits.reverse.map canonicalBitSymbol ++ output) := by
  induction bits generalizing output with
  | nil => rfl
  | cons bit bits ih =>
      cases bit <;>
        simp [scanOutputBits, ih, canonicalBitSymbol, List.map_reverse,
          List.append_assoc]

theorem scanOutputBits_false (bits : List Bool) (output : List Symbol) :
    (scanOutputBits false bits output).2 =
      (trimHighZeros bits).map canonicalBitSymbol ++ output := by
  induction bits generalizing output with
  | nil => rfl
  | cons bit bits ih =>
      cases bit
      · simpa [scanOutputBits, trimHighZeros] using ih output
      · simp [scanOutputBits, scanOutputBits_true, trimHighZeros,
          canonicalBitSymbol, List.map_reverse, List.append_assoc]

theorem scanOutputBits_fst (seen : Bool) (bits : List Bool)
    (output₁ output₂ : List Symbol) :
    (scanOutputBits seen bits output₁).1 =
      (scanOutputBits seen bits output₂).1 := by
  induction bits generalizing seen output₁ output₂ with
  | nil => rfl
  | cons bit bits ih =>
      cases bit <;> cases seen <;> simp only [scanOutputBits, ↓reduceIte] <;>
        apply ih

def outputFinalSeen (w : Nat) (words : List Nat) : Bool :=
  (scanOutputBits false
    (fixedBits w (words.getLast?.getD 0)).reverse []).1

theorem scanOutputBits_fixedBits {w n : Nat} (h : n < 2 ^ w)
    (output : List Symbol) :
    (scanOutputBits false (fixedBits w n).reverse output).2 =
      n.bits.map canonicalBitSymbol ++ output := by
  rw [scanOutputBits_false, trimHighZeros_fixedBits_reverse h]

theorem output_bits_run {N : Nat} (state : WrapperState N)
    (seen : Bool) (bits : List Bool) (rest : List SparseSymbol)
    (output : List Symbol)
    (base : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    let result := scanOutputBits seen bits output
    ((fun x => x.bind (TM2.step
      (liftCoreProgram (fun _ : Empty => .halt)
        (outputAdapterProgram (N := N) (L := Empty)))))^[3 * bits.length])
      (some (outputAdapterCfg (L := Empty) .scan
        {state with heldSparse := none, flag := seen}
        (outputAdapterStacks (bits.map SparseSymbol.bit ++ rest) output base))) =
    some (outputAdapterCfg (L := Empty) .scan
      {state with heldSparse := none, flag := result.1}
      (outputAdapterStacks rest result.2 base)) := by
  induction bits generalizing state seen output with
  | nil =>
      simp [scanOutputBits, outputAdapterStacks]
  | cons bit bits ih =>
      simp only [List.length_cons, List.map_cons, List.cons_append]
      rw [show 3 * (bits.length + 1) = 3 * bits.length + 3 by omega,
        Function.iterate_add_apply]
      simp only [Function.iterate_succ_apply, Function.iterate_zero_apply,
        Option.bind_some]
      rw [outputAdapterStacks_cons]
      rw [output_scan_step]
      rw [update_coreOutput_same]
      simp only [Option.bind_some]
      rw [output_decide_bit_step (state := {state with flag := seen})]
      simp only [Option.bind_some]
      cases bit with
      | false =>
          cases seen with
          | false =>
              rw [output_bit_false_unseen_step
                (state := {state with flag := false}) rfl]
              simpa [scanOutputBits, outputAdapterStacks] using
                ih state false output
          | true =>
              rw [output_bit_false_seen_step
                (state := {state with flag := true}) rfl]
              simpa [scanOutputBits, outputAdapterStacks] using
                ih state true (.zero :: output)
      | true =>
          cases seen with
          | false =>
              rw [output_bit_true_step (state := {state with flag := false})]
              simpa [scanOutputBits, outputAdapterStacks] using
                ih state true (.one :: output)
          | true =>
              rw [output_bit_true_step (state := {state with flag := true})]
              simpa [scanOutputBits, outputAdapterStacks] using
                ih state true (.one :: output)
      all_goals exact Symbol

theorem output_delimiter_run {N : Nat} (state : WrapperState N)
    (active : Bool) (rest : List SparseSymbol) (output : List Symbol)
    (base : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    ((fun x => x.bind (TM2.step
      (liftCoreProgram (fun _ : Empty => .halt)
        (outputAdapterProgram (N := N) (L := Empty)))))^[3])
      (some (outputAdapterCfg (L := Empty) .scan
        {state with heldSparse := none, active := active}
        (outputAdapterStacks (.wordEnd :: rest) output base))) =
    some (outputAdapterCfg (L := Empty) .scan
      {state with heldSparse := none, flag := false, active := true}
      (outputAdapterStacks rest
        (if active then .separator :: output else output) base)) := by
  simp only [show 3 = Nat.succ (Nat.succ (Nat.succ 0)) by rfl,
    Function.iterate_succ_apply, Function.iterate_zero_apply,
    Option.bind_some]
  rw [outputAdapterStacks_cons]
  rw [output_scan_step]
  rw [update_coreOutput_same]
  simp [outputAdapterCfg, liftCoreProgram, outputAdapterProgram,
    outputAdapterStacks, TM2.step]
  cases active <;> rfl
  all_goals exact Symbol

theorem output_word_run {N w n : Nat} (h : n < 2 ^ w)
    (state : WrapperState N) (rest : List SparseSymbol)
    (output : List Symbol)
    (base : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    ((fun x => x.bind (TM2.step
      (liftCoreProgram (fun _ : Empty => .halt)
        (outputAdapterProgram (N := N) (L := Empty)))))^[3 * w + 3])
      (some (outputAdapterCfg (L := Empty) .scan
        {state with heldSparse := none, flag := false, active := true}
        (outputAdapterStacks
          ((fixedBits w n).reverse.map SparseSymbol.bit ++ .wordEnd :: rest)
          output base))) =
    some (outputAdapterCfg (L := Empty) .scan
      {state with heldSparse := none, flag := false, active := true}
      (outputAdapterStacks rest (encodeNat n ++ output) base)) := by
  have hbits := output_bits_run {state with active := true} false (fixedBits w n).reverse
    (.wordEnd :: rest) output base
  have hscan := scanOutputBits_fixedBits h output
  let middleState : WrapperState N := {state with heldSparse := none, flag := (scanOutputBits false (fixedBits w n).reverse output).1, active := true}
  have hdelimiter := output_delimiter_run middleState true rest
    (scanOutputBits false (fixedBits w n).reverse output).2 base
  have hchain := chain_iterations
    (fun x : Option (TM2.Cfg WrapperAlphabet (Sum Empty OutputAdapterLabel)
      (WrapperState N)) => x.bind (TM2.step
        (liftCoreProgram (fun _ : Empty => .halt)
          (outputAdapterProgram (N := N) (L := Empty))))) hbits hdelimiter
  rw [show 3 * w + 3 = 3 * (fixedBits w n).reverse.length + 3 by simp]
  simpa [middleState, hscan, encodeNat, canonicalBitSymbol,
    List.map_map, Function.comp_def, List.append_assoc] using hchain

theorem output_finish_run {N : Nat} (state : WrapperState N)
    (active : Bool) (output : List Symbol)
    (base : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    ((fun x => x.bind (TM2.step
      (liftCoreProgram (fun _ : Empty => .halt)
        (outputAdapterProgram (N := N) (L := Empty)))))^[3])
      (some (outputAdapterCfg (L := Empty) .scan
        {state with heldSparse := none, active := active}
        (outputAdapterStacks [.outputEnd] output base))) =
    some (outputAdapterCfg (L := Empty) (.cleanupPeek .input)
      {state with heldSparse := some .outputEnd, active := active}
      (outputAdapterStacks []
        (if active then .separator :: output else output) base)) := by
  simp only [show 3 = Nat.succ (Nat.succ (Nat.succ 0)) by rfl,
    Function.iterate_succ_apply, Function.iterate_zero_apply,
    Option.bind_some]
  rw [outputAdapterStacks_cons]
  rw [output_scan_step]
  rw [update_coreOutput_same]
  simp [outputAdapterCfg, liftCoreProgram, outputAdapterProgram,
    outputAdapterStacks, TM2.step]
  cases active <;> rfl
  all_goals exact Symbol

theorem output_final_word_run {N w n : Nat} (h : n < 2 ^ w)
    (state : WrapperState N) (output : List Symbol)
    (base : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    ((fun x => x.bind (TM2.step
      (liftCoreProgram (fun _ : Empty => .halt)
        (outputAdapterProgram (N := N) (L := Empty)))))^[3 * w + 3])
      (some (outputAdapterCfg (L := Empty) .scan
        {state with heldSparse := none, flag := false, active := true}
        (outputAdapterStacks
          ((fixedBits w n).reverse.map SparseSymbol.bit ++ [.outputEnd])
          output base))) =
    some (outputAdapterCfg (L := Empty) (.cleanupPeek .input)
      {state with heldSparse := some .outputEnd, flag := (scanOutputBits false (fixedBits w n).reverse output).1, active := true}
      (outputAdapterStacks [] (encodeNat n ++ output) base)) := by
  have hbits := output_bits_run {state with active := true} false (fixedBits w n).reverse
    [.outputEnd] output base
  let middleState : WrapperState N := {state with heldSparse := none, flag := (scanOutputBits false (fixedBits w n).reverse output).1, active := true}
  have hfinish := output_finish_run middleState true
    (scanOutputBits false (fixedBits w n).reverse output).2 base
  have hchain := chain_iterations
    (fun x : Option (TM2.Cfg WrapperAlphabet (Sum Empty OutputAdapterLabel)
      (WrapperState N)) => x.bind (TM2.step
        (liftCoreProgram (fun _ : Empty => .halt)
          (outputAdapterProgram (N := N) (L := Empty))))) hbits hfinish
  have hscan := scanOutputBits_fixedBits h output
  rw [show 3 * w + 3 = 3 * (fixedBits w n).reverse.length + 3 by simp]
  simpa [middleState, hscan, encodeNat, canonicalBitSymbol,
    List.map_map, Function.comp_def, List.append_assoc] using hchain

def cleanupSuccessor (stack : CleanupStack) : OutputAdapterLabel :=
  match nextCleanupStack stack with
  | some next => .cleanupPeek next
  | none => .halt

theorem cleanup_stack_run {N : Nat} (stack : CleanupStack)
    (state : WrapperState N) (xs : List (WrapperAlphabet (cleanupStack stack)))
    (base : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    ((fun x => x.bind (TM2.step
      (liftCoreProgram (fun _ : Empty => .halt)
        (outputAdapterProgram (N := N) (L := Empty)))))^[2 * xs.length + 1])
      (some (outputAdapterCfg (L := Empty) (.cleanupPeek stack) state
        (Function.update base (cleanupStack stack) xs))) =
    some (outputAdapterCfg (L := Empty) (cleanupSuccessor stack)
      {state with flag := false}
      (Function.update base (cleanupStack stack) [])) := by
  induction xs generalizing state with
  | nil =>
      simp [outputAdapterCfg, liftCoreProgram, outputAdapterProgram,
        cleanupSuccessor, TM2.step]
      cases h : nextCleanupStack stack <;> simp [h]
  | cons x xs ih =>
      have hpeek :
          ((fun z => z.bind (TM2.step
            (liftCoreProgram (fun _ : Empty => .halt)
              (outputAdapterProgram (N := N) (L := Empty)))))^[1])
            (some (outputAdapterCfg (L := Empty) (.cleanupPeek stack) state
              (Function.update base (cleanupStack stack) (x :: xs)))) =
          some (outputAdapterCfg (L := Empty) (.cleanupPop stack)
            {state with flag := true}
            (Function.update base (cleanupStack stack) (x :: xs))) := by
        simp [outputAdapterCfg, liftCoreProgram, outputAdapterProgram, TM2.step]
      have hpop :
          ((fun z => z.bind (TM2.step
            (liftCoreProgram (fun _ : Empty => .halt)
              (outputAdapterProgram (N := N) (L := Empty)))))^[1])
            (some (outputAdapterCfg (L := Empty) (.cleanupPop stack)
              {state with flag := true}
              (Function.update base (cleanupStack stack) (x :: xs)))) =
          some (outputAdapterCfg (L := Empty) (.cleanupPeek stack)
            {state with flag := true}
            (Function.update base (cleanupStack stack) xs)) := by
        simp [outputAdapterCfg, liftCoreProgram, outputAdapterProgram, TM2.step]
      have htwo := chain_iterations
        (fun z : Option (TM2.Cfg WrapperAlphabet
          (Sum Empty OutputAdapterLabel) (WrapperState N)) =>
          z.bind (TM2.step (liftCoreProgram (fun _ : Empty => .halt)
            (outputAdapterProgram (N := N) (L := Empty))))) hpeek hpop
      have hall := chain_iterations _ htwo (ih {state with flag := true})
      have hcost : 2 + (2 * xs.length + 1) = 2 * (xs.length + 1) + 1 := by
        omega
      simpa only [List.length_cons, hcost] using hall

def outputScanPayload (w : Nat) : List Nat -> List SparseSymbol
  | [] => [.outputEnd]
  | n :: ns =>
      (fixedBits w n).reverse.map SparseSymbol.bit ++
        match ns with
        | [] => [.outputEnd]
        | _ :: _ => .wordEnd :: outputScanPayload w ns

theorem encodeOutputStack_eq_payload (w : Nat) : ∀ ys : List Nat,
    encodeOutputStack w ys =
      match ys.reverse with
      | [] => [.outputEnd]
      | _ :: _ => .wordEnd :: outputScanPayload w ys.reverse := by
  intro ys
  induction ys using List.reverseRecOn with
  | nil => rfl
  | append_singleton ys y ih =>
      simp [encodeOutputStack, encodeWordList, encodeFixedWord,
        outputScanPayload, List.map_reverse, List.append_assoc]
      simpa [encodeWordList] using ih

theorem output_words_run {N w : Nat} (state : WrapperState N)
    (words : List Nat) (hne : words ≠ [])
    (hfit : ∀ n ∈ words, n < 2 ^ w)
    (output : List Symbol)
    (base : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    ((fun x => x.bind (TM2.step
      (liftCoreProgram (fun _ : Empty => .halt)
        (outputAdapterProgram (N := N) (L := Empty)))))^[
          words.length * (3 * w + 3)])
      (some (outputAdapterCfg (L := Empty) .scan
        {state with heldSparse := none, flag := false, active := true}
        (outputAdapterStacks (outputScanPayload w words) output base))) =
    some (outputAdapterCfg (L := Empty) (.cleanupPeek .input)
      { core := state.core, heldInput := state.heldInput,
        heldSparse := some SparseSymbol.outputEnd,
        flag := outputFinalSeen w words,
        active := true}
      (outputAdapterStacks [] (encode words.reverse ++ output) base)) := by
  induction words generalizing output state with
  | nil => contradiction
  | cons n words ih =>
      cases words with
      | nil =>
          have hfinal := output_final_word_run (N := N)
            (hfit n (by simp)) state output base
          have hflag := scanOutputBits_fst false (fixedBits w n).reverse output []
          simpa [outputScanPayload, outputFinalSeen, hflag] using hfinal
      | cons m words =>
          have hn : n < 2 ^ w := hfit n (by simp)
          have htail : ∀ a ∈ m :: words, a < 2 ^ w := by
            intro a ha
            exact hfit a (by simp [ha])
          have hfirst := output_word_run hn state
            (outputScanPayload w (m :: words)) output base
          have hrest := ih
            {state with heldSparse := none, flag := false, active := true}
            (by simp) htail (encodeNat n ++ output)
          have hchain := chain_iterations
            (fun x : Option (TM2.Cfg WrapperAlphabet
              (Sum Empty OutputAdapterLabel) (WrapperState N)) =>
              x.bind (TM2.step
                (liftCoreProgram (fun _ : Empty => .halt)
                  (outputAdapterProgram (N := N) (L := Empty))))) hfirst hrest
          have hcost : (n :: m :: words).length * (3 * w + 3) =
              (3 * w + 3) + (m :: words).length * (3 * w + 3) := by
            simp
            ring
          rw [hcost]
          simpa [outputScanPayload, encode, List.append_assoc] using hchain

theorem output_initialize_step {N : Nat} (state : WrapperState N)
    (tapes : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    TM2.step (liftCoreProgram (fun _ : Empty => .halt)
      (outputAdapterProgram (N := N) (L := Empty)))
      (outputAdapterCfg (L := Empty) .initialize state tapes) =
    some (outputAdapterCfg (L := Empty) .scan
      {state with heldSparse := none, flag := false, active := false} tapes) := by
  simp [outputAdapterCfg, liftCoreProgram, outputAdapterProgram, TM2.step]

theorem output_decode_run {N w : Nat} (state : WrapperState N)
    (ys : List Nat) (hfit : ∀ n ∈ ys, n < 2 ^ w)
    (base : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    ∃ finalState,
      ((fun x => x.bind (TM2.step
        (liftCoreProgram (fun _ : Empty => .halt)
          (outputAdapterProgram (N := N) (L := Empty)))))^[
            4 + ys.length * (3 * w + 3)])
        (some (outputAdapterCfg (L := Empty) .initialize state
          (outputAdapterStacks (encodeOutputStack w ys) [] base))) =
      some (outputAdapterCfg (L := Empty) (.cleanupPeek .input) finalState
        (outputAdapterStacks [] (encode ys) base)) := by
  have hinit :
      ((fun x => x.bind (TM2.step
        (liftCoreProgram (fun _ : Empty => .halt)
          (outputAdapterProgram (N := N) (L := Empty)))))^[1])
        (some (outputAdapterCfg (L := Empty) .initialize state
          (outputAdapterStacks (encodeOutputStack w ys) [] base))) =
      some (outputAdapterCfg (L := Empty) .scan
        {state with heldSparse := none, flag := false, active := false}
        (outputAdapterStacks (encodeOutputStack w ys) [] base)) := by
    simpa using output_initialize_step state
      (outputAdapterStacks (encodeOutputStack w ys) [] base)
  cases ys with
  | nil =>
      have hfinish := output_finish_run
        {state with heldSparse := none, flag := false, active := false}
        false [] base
      let finalState : WrapperState N :=
        {state with heldSparse := some SparseSymbol.outputEnd, flag := false, active := false}
      refine ⟨finalState, ?_⟩
      have hchain := chain_iterations
        (fun x : Option (TM2.Cfg WrapperAlphabet
          (Sum Empty OutputAdapterLabel) (WrapperState N)) =>
          x.bind (TM2.step
            (liftCoreProgram (fun _ : Empty => .halt)
              (outputAdapterProgram (N := N) (L := Empty))))) hinit hfinish
      simpa [encodeOutputStack, encode, outputAdapterStacks] using hchain
  | cons y ys =>
      let words := (y :: ys).reverse
      have hwordsNe : words ≠ [] := by simp [words]
      have hwordsFit : ∀ n ∈ words, n < 2 ^ w := by
        intro n hn
        exact hfit n (by simpa [words, or_comm] using hn)
      have hdelimiter := output_delimiter_run
        {state with heldSparse := none, flag := false, active := false}
        false (outputScanPayload w words) [] base
      have hstack : encodeOutputStack w (y :: ys) =
          SparseSymbol.wordEnd :: outputScanPayload w words := by
        rw [encodeOutputStack_eq_payload]
        split <;> simp_all [words]
      have hinit' := hinit
      rw [hstack] at hinit'
      have hwords := output_words_run
        {state with heldSparse := none, flag := false, active := true}
        words hwordsNe hwordsFit [] base
      let finalState : WrapperState N :=
        { core := state.core, heldInput := state.heldInput,
          heldSparse := some SparseSymbol.outputEnd,
          flag := outputFinalSeen w words, active := true}
      refine ⟨finalState, ?_⟩
      have hchain₁ := chain_iterations
        (fun x : Option (TM2.Cfg WrapperAlphabet
          (Sum Empty OutputAdapterLabel) (WrapperState N)) =>
          x.bind (TM2.step
            (liftCoreProgram (fun _ : Empty => .halt)
              (outputAdapterProgram (N := N) (L := Empty))))) hinit' hdelimiter
      have hchain₂ := chain_iterations
        (fun x : Option (TM2.Cfg WrapperAlphabet
          (Sum Empty OutputAdapterLabel) (WrapperState N)) =>
          x.bind (TM2.step
            (liftCoreProgram (fun _ : Empty => .halt)
              (outputAdapterProgram (N := N) (L := Empty))))) hchain₁ hwords
      rw [hstack]
      simpa [finalState, words, List.length_reverse,
        List.append_assoc] using hchain₂

/-- The exact cost of the final sanitation pass.  The public output stack is
left alone; every other stack is traversed and emptied. -/
def cleanupTotalCost
    (tapes : (k : WrapperStack) -> List (WrapperAlphabet k)) : Nat :=
  2 * (tapes .input).length + 1 +
  2 * (tapes (.core .accumulator)).length + 1 +
  2 * (tapes (.core .memory)).length + 1 +
  2 * (tapes (.core .input)).length + 1 +
  2 * (tapes (.core .output)).length + 1 +
  2 * (tapes (.core .work0)).length + 1 +
  2 * (tapes (.core .work1)).length + 1 +
  2 * (tapes (.core .work2)).length + 1 +
  2 * (tapes (.core .work3)).length + 1 +
  2 * (tapes (.core .work4)).length + 1 +
  2 * (tapes (.core .work5)).length + 1 +
  2 * (tapes (.core .work6)).length + 1 +
  2 * (tapes (.core .work7)).length + 1

def cleanedStacks
    (tapes : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    (k : WrapperStack) -> List (WrapperAlphabet k)
  | .output => tapes .output
  | _ => []

theorem update_same_value {α : Type} {β : α → Type} [DecidableEq α]
    (f : (a : α) → β a) (i : α) :
    Function.update f i (f i) = f := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Function.update, h]

theorem output_halt_step {N : Nat} (state : WrapperState N)
    (tapes : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    TM2.step (liftCoreProgram (fun _ : Empty => .halt)
      (outputAdapterProgram (N := N) (L := Empty)))
      (outputAdapterCfg (L := Empty) .halt state tapes) =
    some ⟨none, default, tapes⟩ := by
  simp [outputAdapterCfg, liftCoreProgram, outputAdapterProgram, TM2.step]

/-- Starting at the first cleanup label, the adapter empties every private
stack and then takes its halting step.  The public output stack is unchanged. -/
theorem output_cleanup_run {N : Nat} (state : WrapperState N)
    (tapes : (k : WrapperStack) -> List (WrapperAlphabet k)) :
    ((fun x => x.bind (TM2.step
      (liftCoreProgram (fun _ : Empty => .halt)
        (outputAdapterProgram (N := N) (L := Empty)))))^[
          cleanupTotalCost tapes + 1])
      (some (outputAdapterCfg (L := Empty) (.cleanupPeek .input) state tapes)) =
    some ⟨none, default, cleanedStacks tapes⟩ := by
  let s1 := Function.update tapes .input []
  let s2 := Function.update s1 (.core .accumulator) []
  let s3 := Function.update s2 (.core .memory) []
  let s4 := Function.update s3 (.core .input) []
  let s5 := Function.update s4 (.core .output) []
  let s6 := Function.update s5 (.core .work0) []
  let s7 := Function.update s6 (.core .work1) []
  let s8 := Function.update s7 (.core .work2) []
  let s9 := Function.update s8 (.core .work3) []
  let s10 := Function.update s9 (.core .work4) []
  let s11 := Function.update s10 (.core .work5) []
  let s12 := Function.update s11 (.core .work6) []
  let s13 := Function.update s12 (.core .work7) []
  have h1 := cleanup_stack_run (N := N) .input state (tapes .input) tapes
  have h2 := cleanup_stack_run (N := N) (.core .accumulator)
    {state with flag := false} (s1 (.core .accumulator)) s1
  have h3 := cleanup_stack_run (N := N) (.core .memory)
    {state with flag := false} (s2 (.core .memory)) s2
  have h4 := cleanup_stack_run (N := N) (.core .input)
    {state with flag := false} (s3 (.core .input)) s3
  have h5 := cleanup_stack_run (N := N) (.core .output)
    {state with flag := false} (s4 (.core .output)) s4
  have h6 := cleanup_stack_run (N := N) (.core .work0)
    {state with flag := false} (s5 (.core .work0)) s5
  have h7 := cleanup_stack_run (N := N) (.core .work1)
    {state with flag := false} (s6 (.core .work1)) s6
  have h8 := cleanup_stack_run (N := N) (.core .work2)
    {state with flag := false} (s7 (.core .work2)) s7
  have h9 := cleanup_stack_run (N := N) (.core .work3)
    {state with flag := false} (s8 (.core .work3)) s8
  have h10 := cleanup_stack_run (N := N) (.core .work4)
    {state with flag := false} (s9 (.core .work4)) s9
  have h11 := cleanup_stack_run (N := N) (.core .work5)
    {state with flag := false} (s10 (.core .work5)) s10
  have h12 := cleanup_stack_run (N := N) (.core .work6)
    {state with flag := false} (s11 (.core .work6)) s11
  have h13 := cleanup_stack_run (N := N) (.core .work7)
    {state with flag := false} (s12 (.core .work7)) s12
  simp only [cleanupStack] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  rw [update_same_value] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp only [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13]
    at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  have hall := chain_iterations
    (fun x : Option (TM2.Cfg WrapperAlphabet (Sum Empty OutputAdapterLabel)
      (WrapperState N)) => x.bind (TM2.step
        (liftCoreProgram (fun _ : Empty => .halt)
          (outputAdapterProgram (N := N) (L := Empty))))) h1 h2
  have hall := chain_iterations _ hall h3
  have hall := chain_iterations _ hall h4
  have hall := chain_iterations _ hall h5
  have hall := chain_iterations _ hall h6
  have hall := chain_iterations _ hall h7
  have hall := chain_iterations _ hall h8
  have hall := chain_iterations _ hall h9
  have hall := chain_iterations _ hall h10
  have hall := chain_iterations _ hall h11
  have hall := chain_iterations _ hall h12
  have hall := chain_iterations _ hall h13
  have hhalt :
      ((fun x => x.bind (TM2.step
        (liftCoreProgram (fun _ : Empty => .halt)
          (outputAdapterProgram (N := N) (L := Empty)))))^[1])
        (some (outputAdapterCfg (L := Empty) .halt
          {state with flag := false} s13)) =
      some ⟨none, default, s13⟩ := by
    simpa using output_halt_step (N := N) {state with flag := false} s13
  have hall := chain_iterations _ hall hhalt
  have hs13 : s13 = cleanedStacks tapes := by
    funext k
    cases k with
    | input | output => simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10,
        s11, s12, s13, cleanedStacks, Function.update]
    | core k =>
        cases k <;> simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10,
          s11, s12, s13, cleanedStacks, Function.update]
  rw [hs13] at hall
  simpa [cleanupTotalCost, cleanupSuccessor, nextCleanupStack, s1, s2, s3,
    s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, cleanedStacks,
    Function.update_self, Function.update_of_ne, Nat.add_assoc] using hall

end

end Lax20Proofs.RamToTM
