import Lax51Proofs.Computability.SparseRamBasic

namespace Lax51Proofs.Computability

open Lax51Proofs.Microcode Lax51Proofs.RamToTM

set_option maxHeartbeats 2000000

theorem effect_w_primrec : Primrec fun q : ℕ × SparseState => q.1 :=
  Primrec.fst

theorem effect_pc_primrec : Primrec fun q : ℕ × SparseState => q.2.pc :=
  sparseState_pc_primrec.comp Primrec.snd

theorem effect_pcSucc_primrec :
    Primrec fun q : ℕ × SparseState => q.2.pc + 1 :=
  Primrec.succ.comp effect_pc_primrec

theorem effect_acc_primrec : Primrec fun q : ℕ × SparseState => q.2.acc :=
  sparseState_acc_primrec.comp Primrec.snd

theorem effect_mem_primrec : Primrec fun q : ℕ × SparseState => q.2.mem :=
  sparseState_mem_primrec.comp Primrec.snd

theorem effect_inp_primrec : Primrec fun q : ℕ × SparseState => q.2.inp :=
  sparseState_inp_primrec.comp Primrec.snd

theorem effect_out_primrec : Primrec fun q : ℕ × SparseState => q.2.out :=
  sparseState_out_primrec.comp Primrec.snd

theorem effect_pow_primrec : Primrec fun q : ℕ × SparseState => 2 ^ q.1 :=
  powTwo_primrec.comp effect_w_primrec

theorem effect_write_primrec
    (address value : (ℕ × SparseState) → ℕ)
    (haddress : Primrec address) (hvalue : Primrec value) :
    Primrec fun q : ℕ × SparseState =>
      q.2.mem.write q.1 (address q) (value q) := by
  have hdata : Primrec fun q : ℕ × SparseState =>
      (q.1, (q.2.mem, (address q, value q))) :=
    Primrec.pair effect_w_primrec
      (Primrec.pair effect_mem_primrec
        (Primrec.pair haddress hvalue))
  exact (sparseMemory_write_primrec.comp hdata).of_eq fun _ => rfl

theorem effect_value_primrec (o : Op) :
    Primrec fun q : ℕ × SparseState => sparseValue q.1 o q.2.mem :=
  (sparseValue_primrec o).comp
    (Primrec.pair effect_w_primrec effect_mem_primrec)

theorem effect_normalized_primrec (o : Op) :
    Primrec fun q : ℕ × SparseState =>
      sparseValue q.1 o q.2.mem % 2 ^ q.1 :=
  Primrec.nat_mod.comp (effect_value_primrec o) effect_pow_primrec

theorem effect_with_acc_primrec {value : (ℕ × SparseState) → ℕ}
    (hvalue : Primrec value) :
    Primrec fun q : ℕ × SparseState => some
      (SparseState.mk (q.2.pc + 1) (value q) q.2.mem q.2.inp q.2.out) :=
  Primrec.option_some.comp
    (sparseState_mk_primrec effect_pcSucc_primrec hvalue
      effect_mem_primrec effect_inp_primrec effect_out_primrec)

theorem effect_with_mem_primrec {memory : (ℕ × SparseState) → SparseMemory}
    (hmemory : Primrec memory) :
    Primrec fun q : ℕ × SparseState => some
      (SparseState.mk (q.2.pc + 1) q.2.acc (memory q) q.2.inp q.2.out) :=
  Primrec.option_some.comp
    (sparseState_mk_primrec effect_pcSucc_primrec effect_acc_primrec
      hmemory effect_inp_primrec effect_out_primrec)

theorem sparseEffect_read_primrec (a : ℕ) :
    Primrec fun q : ℕ × SparseState => sparseEffect q.1 (.read a) q.2 := by
  have hhead : Primrec fun q : ℕ × SparseState => q.2.inp.head? :=
    Primrec.list_head?.comp effect_inp_primrec
  have htail : Primrec fun q : ℕ × SparseState => q.2.inp.tail :=
    Primrec.list_tail.comp effect_inp_primrec
  have hnext : Primrec₂ fun (q : ℕ × SparseState) (v : ℕ) =>
      SparseState.mk (q.2.pc + 1) q.2.acc
        (q.2.mem.write q.1 a v) q.2.inp.tail q.2.out := by
    apply sparseState_mk_primrec
    · exact effect_pcSucc_primrec.comp Primrec.fst
    · exact effect_acc_primrec.comp Primrec.fst
    · exact sparseMemory_write_primrec.comp
        (Primrec.pair (effect_w_primrec.comp Primrec.fst)
          (Primrec.pair (effect_mem_primrec.comp Primrec.fst)
            (Primrec.pair (Primrec.const a) Primrec.snd)))
    · exact htail.comp Primrec.fst
    · exact effect_out_primrec.comp Primrec.fst
  exact (Primrec.option_map hhead hnext).of_eq fun q => by simp [sparseEffect]

theorem sparseEffect_write_primrec (o : Op) :
    Primrec fun q : ℕ × SparseState => sparseEffect q.1 (.write o) q.2 := by
  apply Primrec.option_some.comp
  apply sparseState_mk_primrec effect_pcSucc_primrec
    effect_acc_primrec effect_mem_primrec effect_inp_primrec
  exact Primrec.list_concat.comp effect_out_primrec
    (effect_normalized_primrec o)

theorem sparseEffect_store_primrec (a : ℕ) :
    Primrec fun q : ℕ × SparseState => sparseEffect q.1 (.store a) q.2 :=
  effect_with_mem_primrec
    (effect_write_primrec (fun _ => a) (fun q => q.2.acc)
      (Primrec.const a) effect_acc_primrec)

theorem sparseEffect_storeInd_primrec (a : ℕ) :
    Primrec fun q : ℕ × SparseState => sparseEffect q.1 (.storeInd a) q.2 := by
  have ha : Primrec fun q : ℕ × SparseState => a % 2 ^ q.1 :=
    Primrec.nat_mod.comp (Primrec.const a) effect_pow_primrec
  have haddress : Primrec fun q : ℕ × SparseState =>
      SparseMemory.read q.2.mem (a % 2 ^ q.1) :=
    sparseMemory_read_primrec₂.comp effect_mem_primrec ha
  exact effect_with_mem_primrec
    (effect_write_primrec _ _ haddress effect_acc_primrec)

theorem normalized_binary_primrec (o : Op) (operation : ℕ → ℕ → ℕ)
    (hoperation : Primrec₂ operation) :
    Primrec fun q : ℕ × SparseState =>
      operation q.2.acc (sparseValue q.1 o q.2.mem) % 2 ^ q.1 :=
  Primrec.nat_mod.comp
    (hoperation.comp effect_acc_primrec (effect_value_primrec o))
    effect_pow_primrec

theorem sparseEffect_primrec (i : Instr) :
    Primrec fun q : ℕ × SparseState => sparseEffect q.1 i q.2 := by
  cases i with
  | read a => exact sparseEffect_read_primrec a
  | write o => exact sparseEffect_write_primrec o
  | load o => exact effect_with_acc_primrec (effect_normalized_primrec o)
  | store a => exact sparseEffect_store_primrec a
  | storeInd a => exact sparseEffect_storeInd_primrec a
  | add o =>
      apply effect_with_acc_primrec
      exact normalized_binary_primrec o (fun a b => a + b) Primrec.nat_add
  | sub o =>
      apply effect_with_acc_primrec
      exact normalized_binary_primrec o (fun a b => a - b) Primrec.nat_sub
  | mul o =>
      apply effect_with_acc_primrec
      exact normalized_binary_primrec o (fun a b => a * b) Primrec.nat_mul
  | div o =>
      apply effect_with_acc_primrec
      exact normalized_binary_primrec o (fun a b => a / b) Primrec.nat_div
  | and o =>
      apply effect_with_acc_primrec
      exact normalized_binary_primrec o Nat.land nat_land_primrec₂
  | or o =>
      apply effect_with_acc_primrec
      exact normalized_binary_primrec o Nat.lor nat_lor_primrec₂
  | xor o =>
      apply effect_with_acc_primrec
      exact normalized_binary_primrec o Nat.xor nat_xor_primrec₂
  | shiftl o =>
      have hpow : Primrec₂ fun (_ : ℕ) b => 2 ^ b :=
        nat_pow_primrec₂.comp₂ (Primrec₂.const 2) Primrec₂.right
      exact effect_with_acc_primrec
        (normalized_binary_primrec o (fun a b => a * 2 ^ b)
          (Primrec.nat_mul.comp₂ Primrec₂.left hpow))
  | compl _ =>
      apply effect_with_acc_primrec
      exact Primrec.nat_mod.comp
        (Primrec.nat_sub.comp
          (Primrec.nat_sub.comp effect_pow_primrec (Primrec.const 1))
          (Primrec.nat_mod.comp effect_acc_primrec effect_pow_primrec))
        effect_pow_primrec
  | shiftr o =>
      have hpow : Primrec₂ fun (_ : ℕ) b => 2 ^ b :=
        nat_pow_primrec₂.comp₂ (Primrec₂.const 2) Primrec₂.right
      exact effect_with_acc_primrec
        (normalized_binary_primrec o (fun a b => a / 2 ^ b)
          (Primrec.nat_div.comp₂ Primrec₂.left hpow))
  | jump l =>
      exact Primrec.option_some.comp
        (sparseState_mk_primrec (Primrec.const l) effect_acc_primrec
          effect_mem_primrec effect_inp_primrec effect_out_primrec)
  | jzero l =>
      have hjump : Primrec fun q : ℕ × SparseState =>
          if q.2.acc = 0 then l else q.2.pc + 1 :=
        Primrec.ite
          (Primrec.eq.comp effect_acc_primrec (Primrec.const 0))
          (Primrec.const l) effect_pcSucc_primrec
      exact Primrec.option_some.comp
        (sparseState_mk_primrec hjump effect_acc_primrec
          effect_mem_primrec effect_inp_primrec effect_out_primrec)
  | jgtz l =>
      have hjump : Primrec fun q : ℕ × SparseState =>
          if 0 < q.2.acc then l else q.2.pc + 1 :=
        Primrec.ite
          (Primrec.nat_lt.comp (Primrec.const 0) effect_acc_primrec)
          (Primrec.const l) effect_pcSucc_primrec
      exact Primrec.option_some.comp
        (sparseState_mk_primrec hjump effect_acc_primrec
          effect_mem_primrec effect_inp_primrec effect_out_primrec)
  | halt => exact Primrec.const none

theorem sparseEffect_computable (i : Instr) :
    Computable fun q : ℕ × SparseState => sparseEffect q.1 i q.2 :=
  (sparseEffect_primrec i).to_comp

/-- Execute the instruction at an explicitly supplied program counter.  Keeping
the counter separate from the state makes computability for a fixed finite
program a direct induction on that program. -/
def sparseExecAt (p : Program) (w pc : ℕ) (s : SparseState) : Option SparseState :=
  p[pc]?.bind fun i => sparseEffect w i s

theorem sparseExecAt_primrec (p : Program) :
    Primrec fun q : (ℕ × ℕ) × SparseState =>
      sparseExecAt p q.1.1 q.1.2 q.2 := by
  induction p with
  | nil => exact Primrec.const none
  | cons i p ih =>
      have hpc : Primrec fun q : (ℕ × ℕ) × SparseState => q.1.2 :=
        Primrec.snd.comp Primrec.fst
      have hzero : Primrec fun q : (ℕ × ℕ) × SparseState =>
          sparseEffect q.1.1 i q.2 :=
        (sparseEffect_primrec i).comp
          (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
      have hsucc : Primrec₂ fun (q : (ℕ × ℕ) × SparseState) (pc : ℕ) =>
          sparseExecAt p q.1.1 pc q.2 := by
        change Primrec fun z : ((ℕ × ℕ) × SparseState) × ℕ =>
          sparseExecAt p z.1.1.1 z.2 z.1.2
        exact ih.comp
          (Primrec.pair
            (Primrec.pair
              (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
              Primrec.snd)
            (Primrec.snd.comp Primrec.fst))
      exact (Primrec.nat_casesOn hpc hzero hsucc).of_eq fun q => by
        cases q.1.2 <;> rfl

theorem sparseStep_primrec (p : Program) :
    Primrec fun q : ℕ × SparseState => sparseStep q.1 p q.2 := by
  have hdata : Primrec fun q : ℕ × SparseState =>
      ((q.1, q.2.pc), q.2) :=
    Primrec.pair
      (Primrec.pair Primrec.fst effect_pc_primrec)
      Primrec.snd
  exact ((sparseExecAt_primrec p).comp hdata).of_eq fun _ => rfl

theorem sparseInitState_primrec : Primrec sparseInitState := by
  apply sparseState_mk_primrec
  · exact Primrec.const 0
  · exact Primrec.const 0
  · exact Primrec.const []
  · exact Primrec.id
  · exact Primrec.const []

def sparseStepOption (w : ℕ) (p : Program) :
    Option SparseState → Option SparseState :=
  fun os => os.bind (sparseStep w p)

theorem sparseStepOption_primrec (p : Program) :
    Primrec₂ fun w os => sparseStepOption w p os := by
  change Primrec fun q : ℕ × Option SparseState =>
    q.2.bind (sparseStep q.1 p)
  have hnext : Primrec₂ fun (q : ℕ × Option SparseState) (s : SparseState) =>
      sparseStep q.1 p s := by
    change Primrec fun z : (ℕ × Option SparseState) × SparseState =>
      sparseStep z.1.1 p z.2
    exact (sparseStep_primrec p).comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact Primrec.option_bind Primrec.snd hnext

def sparseIter (w : ℕ) (p : Program) (t : ℕ) (s : SparseState) :
    Option SparseState :=
  (sparseStepOption w p)^[t] (some s)

theorem sparseStepOption_iterate_none (w : ℕ) (p : Program) (t : ℕ) :
    (sparseStepOption w p)^[t] none = none := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply]
      simpa [sparseStepOption] using ih

theorem sparseIter_primrec (p : Program) :
    Primrec fun q : (ℕ × ℕ) × SparseState =>
      sparseIter q.1.1 p q.1.2 q.2 := by
  have hfuel : Primrec fun q : (ℕ × ℕ) × SparseState => q.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hstart : Primrec fun q : (ℕ × ℕ) × SparseState => some q.2 :=
    Primrec.option_some.comp Primrec.snd
  have hstep : Primrec₂ fun (q : (ℕ × ℕ) × SparseState)
      (os : Option SparseState) => sparseStepOption q.1.1 p os := by
    change Primrec fun z : (((ℕ × ℕ) × SparseState) × Option SparseState) =>
      sparseStepOption z.1.1.1 p z.2
    exact (sparseStepOption_primrec p).comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
  exact Primrec.nat_iterate hfuel hstart hstep

theorem sparseIter_eq_sparseRun (w : ℕ) (p : Program) (t : ℕ) (s : SparseState) :
    sparseIter w p t s = sparseRun w p t s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
      rw [sparseIter, Function.iterate_succ_apply]
      simp only [sparseStepOption]
      cases hs : sparseStep w p s with
      | none =>
          rw [sparseRun]
          simp only [Option.bind_some, hs, Option.bind_none]
          exact sparseStepOption_iterate_none w p t
      | some s' =>
          rw [sparseRun]
          simp only [Option.bind_some, hs]
          change sparseIter w p t s' = sparseRun w p t s'
          exact ih s'

theorem sparseRun_primrec (p : Program) :
    Primrec fun q : (ℕ × ℕ) × SparseState =>
      sparseRun q.1.1 p q.1.2 q.2 :=
  (sparseIter_primrec p).of_eq fun q =>
    sparseIter_eq_sparseRun q.1.1 p q.1.2 q.2

end Lax51Proofs.Computability
