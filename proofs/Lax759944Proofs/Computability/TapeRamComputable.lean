import Lax759944Proofs.Computability.TapeRam

namespace Lax759944Proofs.Computability.TapeRam

open Lax808846.Ram
open Lax759944Proofs.RamToTM (SparseMemory)

set_option maxHeartbeats 2000000

abbrev ConfigData := ℕ × (SparseMemory × (List ℕ × (List ℕ × List ℕ)))

def configEquiv : Config ≃ ConfigData where
  toFun s := (s.pc, (s.mem, (s.input, (s.inp, s.out))))
  invFun d := ⟨d.1, d.2.1, d.2.2.1, d.2.2.2.1, d.2.2.2.2⟩
  left_inv s := by cases s; rfl
  right_inv d := by rcases d with ⟨pc, mem, input, inp, out⟩; rfl

instance configPrimcodable : Primcodable Config :=
  Primcodable.ofEquiv ConfigData configEquiv

private theorem configEquiv_primrec : Primrec configEquiv := Primrec.of_equiv
private theorem configEquiv_symm_primrec : Primrec configEquiv.symm := Primrec.of_equiv_symm

private theorem config_pc_primrec : Primrec Config.pc :=
  (Primrec.fst.comp configEquiv_primrec).of_eq fun _ => rfl

private theorem config_mem_primrec : Primrec Config.mem :=
  (Primrec.fst.comp (Primrec.snd.comp configEquiv_primrec)).of_eq fun _ => rfl

private theorem config_input_primrec : Primrec Config.input :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp configEquiv_primrec))).of_eq fun _ => rfl

private theorem config_inp_primrec : Primrec Config.inp :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp configEquiv_primrec)))).of_eq fun _ => rfl

private theorem config_out_primrec : Primrec Config.out :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp configEquiv_primrec)))).of_eq fun _ => rfl

private theorem config_mk_primrec {α : Type*} [Primcodable α]
    {pc : α → ℕ} {mem : α → SparseMemory} {input inp out : α → List ℕ}
    (hpc : Primrec pc) (hmem : Primrec mem) (hinput : Primrec input)
    (hinp : Primrec inp) (hout : Primrec out) :
    Primrec fun a => Config.mk (pc a) (mem a) (input a) (inp a) (out a) :=
  configEquiv_symm_primrec.comp
    (Primrec.pair hpc (Primrec.pair hmem
      (Primrec.pair hinput (Primrec.pair hinp hout))))

private theorem eW : Primrec fun q : ℕ × Config => q.1 := Primrec.fst
private theorem ePC : Primrec fun q : ℕ × Config => q.2.pc :=
  config_pc_primrec.comp Primrec.snd
private theorem eMem : Primrec fun q : ℕ × Config => q.2.mem :=
  config_mem_primrec.comp Primrec.snd
private theorem eInput : Primrec fun q : ℕ × Config => q.2.input :=
  config_input_primrec.comp Primrec.snd
private theorem eInp : Primrec fun q : ℕ × Config => q.2.inp :=
  config_inp_primrec.comp Primrec.snd
private theorem eOut : Primrec fun q : ℕ × Config => q.2.out :=
  config_out_primrec.comp Primrec.snd
private theorem eNextPC : Primrec fun q : ℕ × Config => q.2.pc + 1 :=
  Primrec.succ.comp ePC
private theorem ePow : Primrec fun q : ℕ × Config => 2 ^ q.1 :=
  powTwo_primrec.comp eW

private theorem eRead (a : ℕ) :
    Primrec fun q : ℕ × Config => q.2.mem.read (a % 2 ^ q.1) :=
  sparseMemory_read_primrec₂.comp eMem
    (Primrec.nat_mod.comp (Primrec.const a) ePow)

private theorem eStore {address value : (ℕ × Config) → ℕ}
    (haddress : Primrec address) (hvalue : Primrec value) :
    Primrec fun q : ℕ × Config => q.2.mem.write q.1 (address q) (value q) :=
  sparseMemory_write_primrec.comp
    (Primrec.pair eW (Primrec.pair eMem (Primrec.pair haddress hvalue)))

private theorem eWithMem {memory : (ℕ × Config) → SparseMemory}
    (hmemory : Primrec memory) :
    Primrec fun q : ℕ × Config => some
      (Config.mk (q.2.pc + 1) (memory q) q.2.input q.2.inp q.2.out) :=
  Primrec.option_some.comp
    (config_mk_primrec eNextPC hmemory eInput eInp eOut)

private theorem eWithPC {pc : (ℕ × Config) → ℕ} (hpc : Primrec pc) :
    Primrec fun q : ℕ × Config => some
      (Config.mk (pc q) q.2.mem q.2.input q.2.inp q.2.out) :=
  Primrec.option_some.comp
    (config_mk_primrec hpc eMem eInput eInp eOut)

private theorem effect_read_primrec (a : ℕ) :
    Primrec fun q : ℕ × Config => effect q.1 (.read a) q.2 := by
  have hhead := Primrec.list_head?.comp eInp
  have htail := Primrec.list_tail.comp eInp
  have hnext : Primrec₂ fun (q : ℕ × Config) (v : ℕ) =>
      Config.mk (q.2.pc + 1) (q.2.mem.write q.1 a v)
        q.2.input q.2.inp.tail q.2.out := by
    apply config_mk_primrec
    · exact eNextPC.comp Primrec.fst
    · exact sparseMemory_write_primrec.comp
        (Primrec.pair (eW.comp Primrec.fst)
          (Primrec.pair (eMem.comp Primrec.fst)
            (Primrec.pair (Primrec.const a) Primrec.snd)))
    · exact eInput.comp Primrec.fst
    · exact htail.comp Primrec.fst
    · exact eOut.comp Primrec.fst
  exact (Primrec.option_map hhead hnext).of_eq fun q => rfl

/-- Each current RAM instruction is primitive recursive on finite states. -/
theorem effect_primrec (i : Instr) :
    Primrec fun q : ℕ × Config => effect q.1 i q.2 := by
  cases i with
  | set a n => exact eWithMem (eStore (Primrec.const a) (Primrec.const n))
  | load a b =>
      exact eWithMem (eStore (Primrec.const a)
        (sparseMemory_read_primrec₂.comp eMem
          (Primrec.nat_mod.comp (eRead b) ePow)))
  | store a b => exact eWithMem (eStore (eRead a) (eRead b))
  | add a b c =>
      exact eWithMem (eStore (Primrec.const a) (Primrec.nat_add.comp (eRead b) (eRead c)))
  | sub a b c =>
      exact eWithMem (eStore (Primrec.const a) (Primrec.nat_sub.comp (eRead b) (eRead c)))
  | mul a b c =>
      exact eWithMem (eStore (Primrec.const a) (Primrec.nat_mul.comp (eRead b) (eRead c)))
  | div a b c =>
      exact eWithMem (eStore (Primrec.const a) (Primrec.nat_div.comp (eRead b) (eRead c)))
  | and a b c =>
      exact eWithMem (eStore (Primrec.const a) (nat_land_primrec₂.comp (eRead b) (eRead c)))
  | shiftl a b c =>
      exact eWithMem (eStore (Primrec.const a)
        (Primrec.nat_mul.comp (eRead b) (powTwo_primrec.comp (eRead c))))
  | not a b =>
      exact eWithMem (eStore (Primrec.const a)
        (Primrec.nat_sub.comp (Primrec.nat_sub.comp ePow (Primrec.const 1)) (eRead b)))
  | jump l => exact eWithPC (Primrec.const l)
  | jzero a l =>
      exact eWithPC (Primrec.ite
        (Primrec.eq.comp (eRead a) (Primrec.const 0)) (Primrec.const l) eNextPC)
  | jeof l =>
      have hpc : Primrec fun q : ℕ × Config =>
          if q.2.inp = [] then l else q.2.pc + 1 :=
        Primrec.ite (Primrec.eq.comp eInp (Primrec.const []))
          (Primrec.const l) eNextPC
      exact (eWithPC hpc).of_eq fun q => by
        cases hinp : q.2.inp <;> simp [effect, hinp]
  | inputLength a =>
      exact eWithMem (eStore (Primrec.const a) (Primrec.list_length.comp eInput))
  | inputLoad a b =>
      exact eWithMem (eStore (Primrec.const a)
        (Primrec.option_getD.comp
          (Primrec.list_getElem?.comp eInput (Primrec.nat_mod.comp (eRead b) ePow))
          (Primrec.const 0)))
  | halt => exact Primrec.const none
  | read a => exact effect_read_primrec a
  | write a =>
      exact Primrec.option_some.comp
        (config_mk_primrec eNextPC eMem eInput eInp
          (Primrec.list_concat.comp eOut (Primrec.nat_mod.comp (eRead a) ePow)))

private def execAt (p : Program) (w pc : ℕ) (s : Config) : Option Config :=
  p[pc]?.bind fun i => effect w i s

private theorem execAt_primrec (p : Program) :
    Primrec fun q : (ℕ × ℕ) × Config => execAt p q.1.1 q.1.2 q.2 := by
  induction p with
  | nil => exact Primrec.const none
  | cons i p ih =>
      have hpc : Primrec fun q : (ℕ × ℕ) × Config => q.1.2 :=
        Primrec.snd.comp Primrec.fst
      have hzero : Primrec fun q : (ℕ × ℕ) × Config => effect q.1.1 i q.2 :=
        (effect_primrec i).comp
          (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
      have hsucc : Primrec₂ fun (q : (ℕ × ℕ) × Config) (pc : ℕ) =>
          execAt p q.1.1 pc q.2 := by
        change Primrec fun z : ((ℕ × ℕ) × Config) × ℕ => execAt p z.1.1.1 z.2 z.1.2
        exact ih.comp
          (Primrec.pair
            (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
            (Primrec.snd.comp Primrec.fst))
      exact (Primrec.nat_casesOn hpc hzero hsucc).of_eq fun q => by
        cases q.1.2 <;> rfl

theorem next_primrec (p : Program) :
    Primrec fun q : ℕ × Config => next q.1 p q.2 :=
  ((execAt_primrec p).comp
    (Primrec.pair (Primrec.pair Primrec.fst ePC) Primrec.snd)).of_eq fun _ => rfl

private theorem initial_primrec : Primrec initial :=
  config_mk_primrec (Primrec.const 0) (Primrec.const [])
    Primrec.id Primrec.id (Primrec.const [])

private def nextOption (w : ℕ) (p : Program) (os : Option Config) : Option Config :=
  os.bind (next w p)

private theorem nextOption_primrec (p : Program) :
    Primrec₂ fun w os => nextOption w p os := by
  change Primrec fun q : ℕ × Option Config => q.2.bind (next q.1 p)
  have hnext : Primrec₂ fun (q : ℕ × Option Config) (s : Config) => next q.1 p s := by
    change Primrec fun z : (ℕ × Option Config) × Config => next z.1.1 p z.2
    exact (next_primrec p).comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact Primrec.option_bind Primrec.snd hnext

private def iterate (w : ℕ) (p : Program) (t : ℕ) (s : Config) : Option Config :=
  (nextOption w p)^[t] (some s)

private theorem iterate_none (w : ℕ) (p : Program) (t : ℕ) :
    (nextOption w p)^[t] none = none := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply]
      simpa [nextOption] using ih

private theorem iterate_primrec (p : Program) :
    Primrec fun q : (ℕ × ℕ) × Config => iterate q.1.1 p q.1.2 q.2 := by
  have hfuel : Primrec fun q : (ℕ × ℕ) × Config => q.1.2 := Primrec.snd.comp Primrec.fst
  have hstart : Primrec fun q : (ℕ × ℕ) × Config => some q.2 :=
    Primrec.option_some.comp Primrec.snd
  have hstep : Primrec₂ fun (q : (ℕ × ℕ) × Config) (os : Option Config) =>
      nextOption q.1.1 p os := by
    change Primrec fun z : (((ℕ × ℕ) × Config) × Option Config) =>
      nextOption z.1.1.1 p z.2
    exact (nextOption_primrec p).comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
  exact Primrec.nat_iterate hfuel hstart hstep

private theorem iterate_eq_execute (w : ℕ) (p : Program) (t : ℕ) (s : Config) :
    iterate w p t s = execute w p t s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
      rw [iterate, Function.iterate_succ_apply]
      simp only [nextOption]
      cases hs : next w p s with
      | none =>
          rw [execute]
          simp only [Option.bind_some, hs, Option.bind_none]
          exact iterate_none w p t
      | some s' =>
          rw [execute]
          simp only [Option.bind_some, hs]
          change iterate w p t s' = execute w p t s'
          exact ih s'

theorem execute_primrec (p : Program) :
    Primrec fun q : (ℕ × ℕ) × Config => execute q.1.1 p q.1.2 q.2 :=
  (iterate_primrec p).of_eq fun q => iterate_eq_execute q.1.1 p q.1.2 q.2

private theorem haltOutput_primrec (p : Program) :
    Primrec fun q : ℕ × Config => haltOutput p q.1 q.2 := by
  have h := Primrec.option_casesOn (next_primrec p)
    (Primrec.option_some.comp eOut)
    ((Primrec.const none).to₂ : Primrec₂ fun (_ : ℕ × Config)
      (_ : Config) => (none : Option (List ℕ)))
  exact h.of_eq fun q => by
    simp only [haltOutput]
    cases next q.1 p q.2 <;> rfl

theorem candidateAt_primrec (p : Program) :
    Primrec fun q : (ℕ × List ℕ) × ℕ => candidateAt p q.1.1 q.1.2 q.2 := by
  have hw : Primrec fun q : (ℕ × List ℕ) × ℕ => q.1.1 := Primrec.fst.comp Primrec.fst
  have hx : Primrec fun q : (ℕ × List ℕ) × ℕ => q.1.2 := Primrec.snd.comp Primrec.fst
  have hphysical : Primrec fun q : (ℕ × List ℕ) × ℕ => q.1.2.length :: q.1.2 :=
    Primrec.list_cons.comp (Primrec.list_length.comp hx) hx
  have hinit : Primrec fun q : (ℕ × List ℕ) × ℕ => initial (q.1.2.length :: q.1.2) :=
    initial_primrec.comp hphysical
  have hrun : Primrec fun q : (ℕ × List ℕ) × ℕ =>
      execute q.1.1 p q.2 (initial (q.1.2.length :: q.1.2)) :=
    (execute_primrec p).comp (Primrec.pair (Primrec.pair hw Primrec.snd) hinit)
  have hfinish : Primrec₂ fun (q : (ℕ × List ℕ) × ℕ) (s : Config) =>
      haltOutput p q.1.1 s := by
    change Primrec fun z : (((ℕ × List ℕ) × ℕ) × Config) => haltOutput p z.1.1.1 z.2
    exact (haltOutput_primrec p).comp
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
  exact (Primrec.option_bind hrun hfinish).of_eq fun _ => rfl

/-- Every function computable by the full current RAM is Turing-computable.
The width is selected by its supplied computable threshold, and an unbounded
search finds a halting finite simulation. -/
theorem ramComputable_to_computable {f : List ℕ → List ℕ}
    (hf : Lax759944.TuringRamEquivalence.RamComputable f) : Computable f := by
  obtain ⟨p, threshold, hthreshold, hram⟩ := hf
  let candidate := fun x t => candidateAt p (threshold x) x t
  have hcand : Computable₂ candidate :=
    (candidateAt_primrec p).to_comp.comp
      (Computable.pair
        (Computable.pair (hthreshold.comp Computable.fst) Computable.fst)
        Computable.snd)
  have hsearch : Partrec fun x : List ℕ => Nat.rfindOpt (candidate x) :=
    Partrec.rfindOpt hcand
  apply hsearch.of_eq_tot
  intro x
  obtain ⟨t, ht⟩ := hram x (threshold x) le_rfl
  obtain ⟨k, hk⟩ := candidate_exists_of_runsTo ht
  have hdom : (Nat.rfindOpt (candidate x)).Dom :=
    Nat.rfindOpt_dom.2 ⟨k, f x, by simpa [candidate] using hk⟩
  refine ⟨hdom, ?_⟩
  obtain ⟨j, hj⟩ := Nat.rfindOpt_spec (Part.get_mem hdom)
  rw [Option.mem_def] at hj
  obtain ⟨u, hu⟩ := runsTo_of_candidate hj
  exact runsTo_output_unique hu ht

end Lax759944Proofs.Computability.TapeRam
