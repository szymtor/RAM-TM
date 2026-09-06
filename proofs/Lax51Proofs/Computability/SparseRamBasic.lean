import Lax51Proofs.Computability.Bitwise

namespace Lax51Proofs.Computability

open Lax51Proofs.Microcode Lax51Proofs.RamToTM

instance sparseMemoryPrimcodable : Primcodable SparseMemory :=
  show Primcodable (List (ℕ × ℕ)) from inferInstance

set_option maxHeartbeats 2000000

abbrev SparseStateData := (ℕ × ℕ) × (SparseMemory × (List ℕ × List ℕ))

def sparseStateEquiv : SparseState ≃ SparseStateData where
  toFun s := ((s.pc, s.acc), (s.mem, (s.inp, s.out)))
  invFun d :=
    { pc := d.1.1, acc := d.1.2, mem := d.2.1,
      inp := d.2.2.1, out := d.2.2.2 }
  left_inv s := by cases s; rfl
  right_inv d := by rcases d with ⟨⟨pc, acc⟩, mem, inp, out⟩; rfl

instance sparseStatePrimcodable : Primcodable SparseState :=
  Primcodable.ofEquiv SparseStateData sparseStateEquiv

theorem sparseStateEquiv_primrec : Primrec sparseStateEquiv :=
  Primrec.of_equiv

theorem sparseStateEquiv_symm_primrec : Primrec sparseStateEquiv.symm :=
  Primrec.of_equiv_symm

theorem sparseState_pc_primrec : Primrec SparseState.pc :=
  (Primrec.fst.comp (Primrec.fst.comp sparseStateEquiv_primrec)).of_eq fun _ => rfl

theorem sparseState_acc_primrec : Primrec SparseState.acc :=
  (Primrec.snd.comp (Primrec.fst.comp sparseStateEquiv_primrec)).of_eq fun _ => rfl

theorem sparseState_mem_primrec : Primrec SparseState.mem :=
  (Primrec.fst.comp (Primrec.snd.comp sparseStateEquiv_primrec)).of_eq fun _ => rfl

theorem sparseState_inp_primrec : Primrec SparseState.inp :=
  (Primrec.fst.comp (Primrec.snd.comp
    (Primrec.snd.comp sparseStateEquiv_primrec))).of_eq fun _ => rfl

theorem sparseState_out_primrec : Primrec SparseState.out :=
  (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp sparseStateEquiv_primrec))).of_eq fun _ => rfl

theorem sparseState_mk_primrec {α : Type*} [Primcodable α]
    {pc acc : α → ℕ} {mem : α → SparseMemory}
    {inp out : α → List ℕ}
    (hpc : Primrec pc) (hacc : Primrec acc) (hmem : Primrec mem)
    (hinp : Primrec inp) (hout : Primrec out) :
    Primrec fun a =>
      ({ pc := pc a, acc := acc a, mem := mem a,
         inp := inp a, out := out a } : SparseState) := by
  exact sparseStateEquiv_symm_primrec.comp
    (Primrec.pair (Primrec.pair hpc hacc)
      (Primrec.pair hmem (Primrec.pair hinp hout)))

theorem sparseState_mk_computable {α : Type*} [Primcodable α]
    {pc acc : α → ℕ} {mem : α → SparseMemory}
    {inp out : α → List ℕ}
    (hpc : Computable pc) (hacc : Computable acc) (hmem : Computable mem)
    (hinp : Computable inp) (hout : Computable out) :
    Computable fun a =>
      ({ pc := pc a, acc := acc a, mem := mem a,
         inp := inp a, out := out a } : SparseState) := by
  have hdata : Computable fun a =>
      ((pc a, acc a), (mem a, (inp a, out a))) :=
    (Computable.pair (Computable.pair hpc hacc)
      (Computable.pair hmem (Computable.pair hinp hout)))
  exact (sparseStateEquiv_symm_primrec.to_comp.comp hdata).of_eq fun _ => rfl

def sparseReadFold (m : SparseMemory) (a : ℕ) : ℕ :=
  m.foldr (fun cell value => if a = cell.1 then cell.2 else value) 0

theorem sparseReadFold_eq (m : SparseMemory) (a : ℕ) :
    sparseReadFold m a = m.read a := by
  induction m with
  | nil => rfl
  | cons cell m ih =>
      rcases cell with ⟨b, v⟩
      change (if a = b then v else sparseReadFold m a) =
        if a = b then v else SparseMemory.read m a
      rw [ih]

theorem sparseReadFold_primrec₂ : Primrec₂ sparseReadFold := by
  change Primrec fun p : SparseMemory × ℕ => sparseReadFold p.1 p.2
  have hstep : Primrec₂ fun (p : SparseMemory × ℕ) (cv : (ℕ × ℕ) × ℕ) =>
      if p.2 = cv.1.1 then cv.1.2 else cv.2 := by
    apply Primrec.ite
    · exact Primrec.eq.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    · exact Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
    · exact Primrec.snd.comp Primrec.snd
  exact Primrec.list_foldr Primrec.fst (Primrec.const 0) hstep

theorem sparseMemory_read_computable₂ : Computable₂ SparseMemory.read := by
  change Computable fun p : SparseMemory × ℕ => p.1.read p.2
  exact Computable.of_eq sparseReadFold_primrec₂.to_comp fun p =>
    sparseReadFold_eq p.1 p.2

theorem sparseMemory_read_primrec₂ : Primrec₂ SparseMemory.read := by
  change Primrec fun p : SparseMemory × ℕ => p.1.read p.2
  exact Primrec.of_eq sparseReadFold_primrec₂ fun p =>
    sparseReadFold_eq p.1 p.2

theorem nat_pow_primrec₂ : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem powTwo_primrec : Primrec fun w : ℕ => 2 ^ w :=
  nat_pow_primrec₂.comp (Primrec.const 2) Primrec.id

theorem sparseMemory_write_primrec :
    Primrec fun q : ℕ × SparseMemory × ℕ × ℕ =>
      q.2.1.write q.1 q.2.2.1 q.2.2.2 := by
  simp only [SparseMemory.write]
  exact Primrec.list_cons.comp
    (Primrec.pair
      (Primrec.nat_mod.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (powTwo_primrec.comp Primrec.fst))
      (Primrec.nat_mod.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        (powTwo_primrec.comp Primrec.fst)))
    (Primrec.fst.comp Primrec.snd)

theorem sparseValue_computable (o : Op) :
    Computable fun q : ℕ × SparseMemory => sparseValue q.1 o q.2 := by
  cases o with
  | lit n => exact Computable.const n
  | mem a =>
      have haddr : Computable fun q : ℕ × SparseMemory => a % 2 ^ q.1 :=
        (Primrec.nat_mod.comp (Primrec.const a)
          (powTwo_primrec.comp Primrec.fst)).to_comp
      exact sparseMemory_read_computable₂.comp
        Computable.snd haddr
  | ind a =>
      have haddr : Computable fun q : ℕ × SparseMemory => a % 2 ^ q.1 :=
        (Primrec.nat_mod.comp (Primrec.const a)
          (powTwo_primrec.comp Primrec.fst)).to_comp
      have hfirst : Computable fun q : ℕ × SparseMemory =>
          SparseMemory.read q.2 (a % 2 ^ q.1) :=
        sparseMemory_read_computable₂.comp Computable.snd haddr
      have hnormalized : Computable fun q : ℕ × SparseMemory =>
          SparseMemory.read q.2 (a % 2 ^ q.1) % 2 ^ q.1 :=
        Primrec.nat_mod.to_comp.comp hfirst (powTwo_primrec.to_comp.comp Computable.fst)
      exact sparseMemory_read_computable₂.comp Computable.snd
        hnormalized

theorem sparseValue_primrec (o : Op) :
    Primrec fun q : ℕ × SparseMemory => sparseValue q.1 o q.2 := by
  cases o with
  | lit n => exact Primrec.const n
  | mem a =>
      have haddr : Primrec fun q : ℕ × SparseMemory => a % 2 ^ q.1 :=
        Primrec.nat_mod.comp (Primrec.const a)
          (powTwo_primrec.comp Primrec.fst)
      exact sparseMemory_read_primrec₂.comp Primrec.snd haddr
  | ind a =>
      have haddr : Primrec fun q : ℕ × SparseMemory => a % 2 ^ q.1 :=
        Primrec.nat_mod.comp (Primrec.const a)
          (powTwo_primrec.comp Primrec.fst)
      have hfirst : Primrec fun q : ℕ × SparseMemory =>
          SparseMemory.read q.2 (a % 2 ^ q.1) :=
        sparseMemory_read_primrec₂.comp Primrec.snd haddr
      have hnormalized : Primrec fun q : ℕ × SparseMemory =>
          SparseMemory.read q.2 (a % 2 ^ q.1) % 2 ^ q.1 :=
        Primrec.nat_mod.comp hfirst (powTwo_primrec.comp Primrec.fst)
      exact sparseMemory_read_primrec₂.comp Primrec.snd hnormalized

theorem effect_w_computable : Computable fun q : ℕ × SparseState => q.1 :=
  Computable.fst


end Lax51Proofs.Computability
