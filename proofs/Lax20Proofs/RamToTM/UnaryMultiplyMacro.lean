import Lax20Proofs.RamToTM.InputAdapter

namespace Lax20Proofs.RamToTM

open Turing TM2

inductive UnaryMulStack | source | multiplier | destination | backup
  deriving DecidableEq, Fintype, Inhabited

inductive UnaryMulLabel | outer | copy | restore | done
  deriving DecidableEq, Fintype, Inhabited

def unaryMulProgram : UnaryMulLabel →
    TM2.Stmt (fun _ : UnaryMulStack => SparseSymbol)
      UnaryMulLabel SymbolMoveControl
  | .outer =>
      .pop .source (fun _ a => ⟨a⟩) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .done)
        (.load (fun _ => default) <| .goto fun _ => .copy)
  | .copy =>
      .pop .multiplier (fun _ a => ⟨a⟩) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .restore)
        (.push .destination (fun s => s.held.getD default) <|
          .push .backup (fun s => s.held.getD default) <|
          .load (fun _ => default) <| .goto fun _ => .copy)
  | .restore =>
      .pop .backup (fun _ a => ⟨a⟩) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .outer)
        (.push .multiplier (fun s => s.held.getD default) <|
          .load (fun _ => default) <| .goto fun _ => .restore)
  | .done => .halt

def unaryMulStacks (source multiplier destination backup : List SparseSymbol) :
    UnaryMulStack → List SparseSymbol
  | .source => source
  | .multiplier => multiplier
  | .destination => destination
  | .backup => backup

def unaryMulCfg (label : UnaryMulLabel)
    (source multiplier destination backup : List SparseSymbol) :
    TM2.Cfg (fun _ : UnaryMulStack => SparseSymbol)
      UnaryMulLabel SymbolMoveControl :=
  ⟨some label, default, unaryMulStacks source multiplier destination backup⟩

@[simp] theorem unaryMul_outer_cons (a : SparseSymbol) (as bs out : List SparseSymbol) :
    TM2.step unaryMulProgram (unaryMulCfg .outer (a :: as) bs out []) =
      some (unaryMulCfg .copy as bs out []) := by
  simp [unaryMulProgram, unaryMulCfg, unaryMulStacks, TM2.step]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem unaryMul_outer_nil (bs out : List SparseSymbol) :
    TM2.step unaryMulProgram (unaryMulCfg .outer [] bs out []) =
      some (unaryMulCfg .done [] bs out []) := by
  simp [unaryMulProgram, unaryMulCfg, unaryMulStacks, TM2.step]

@[simp] theorem unaryMul_copy_cons (a : SparseSymbol) (as bs out backup : List SparseSymbol) :
    TM2.step unaryMulProgram (unaryMulCfg .copy as (a :: bs) out backup) =
      some (unaryMulCfg .copy as bs (a :: out) (a :: backup)) := by
  simp [unaryMulProgram, unaryMulCfg, unaryMulStacks, TM2.step, Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem unaryMul_copy_nil (as out backup : List SparseSymbol) :
    TM2.step unaryMulProgram (unaryMulCfg .copy as [] out backup) =
      some (unaryMulCfg .restore as [] out backup) := by
  simp [unaryMulProgram, unaryMulCfg, unaryMulStacks, TM2.step]

@[simp] theorem unaryMul_restore_cons (a : SparseSymbol)
    (as bs out backup : List SparseSymbol) :
    TM2.step unaryMulProgram (unaryMulCfg .restore as bs out (a :: backup)) =
      some (unaryMulCfg .restore as (a :: bs) out backup) := by
  simp [unaryMulProgram, unaryMulCfg, unaryMulStacks, TM2.step, Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem unaryMul_restore_nil (as bs out : List SparseSymbol) :
    TM2.step unaryMulProgram (unaryMulCfg .restore as bs out []) =
      some (unaryMulCfg .outer as bs out []) := by
  simp [unaryMulProgram, unaryMulCfg, unaryMulStacks, TM2.step]

theorem unaryMul_copy_iterate (as bs out backup : List SparseSymbol) :
    ((fun o => o.bind (TM2.step unaryMulProgram))^[bs.length])
      (some (unaryMulCfg .copy as bs out backup)) =
    some (unaryMulCfg .copy as [] (bs.reverse ++ out)
      (bs.reverse ++ backup)) := by
  induction bs generalizing out backup with
  | nil => rfl
  | cons a bs ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, unaryMul_copy_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem unaryMul_restore_iterate (as bs out backup : List SparseSymbol) :
    ((fun o => o.bind (TM2.step unaryMulProgram))^[backup.length])
      (some (unaryMulCfg .restore as bs out backup)) =
    some (unaryMulCfg .restore as (backup.reverse ++ bs) out []) := by
  induction backup generalizing bs with
  | nil => rfl
  | cons a backup ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, unaryMul_restore_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem unaryMul_copy_restore (as bs out : List SparseSymbol) :
    ((fun o => o.bind (TM2.step unaryMulProgram))^[2 * bs.length + 2])
      (some (unaryMulCfg .copy as bs out [])) =
    some (unaryMulCfg .outer as bs (bs.reverse ++ out) []) := by
  have h₀ := unaryMul_copy_iterate as bs out []
  simp only [List.append_nil] at h₀
  have h₁ : ((fun o => o.bind (TM2.step unaryMulProgram))^[1])
      (some (unaryMulCfg .copy as [] (bs.reverse ++ out) bs.reverse)) =
      some (unaryMulCfg .restore as [] (bs.reverse ++ out) bs.reverse) := by
    simpa using unaryMul_copy_nil as (bs.reverse ++ out) bs.reverse
  have h₂ := unaryMul_restore_iterate as [] (bs.reverse ++ out) bs.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h₂
  have h₃ : ((fun o => o.bind (TM2.step unaryMulProgram))^[1])
      (some (unaryMulCfg .restore as bs (bs.reverse ++ out) [])) =
      some (unaryMulCfg .outer as bs (bs.reverse ++ out) []) := by
    simpa using unaryMul_restore_nil as bs (bs.reverse ++ out)
  have h := chain_iterations _ (chain_iterations _
    (chain_iterations _ h₀ h₁) h₂) h₃
  have ht : 2 * bs.length + 2 = bs.length + 1 + bs.length + 1 := by omega
  rw [ht]
  exact h

def unaryMarkers (n : Nat) : List SparseSymbol :=
  List.replicate n .wordEnd

@[simp] theorem unaryMarkers_length (n : Nat) : (unaryMarkers n).length = n := by
  simp [unaryMarkers]

theorem unaryMul_one_round (a b : Nat) (out : List SparseSymbol) :
    ((fun o => o.bind (TM2.step unaryMulProgram))^[2 * b + 3])
      (some (unaryMulCfg .outer
        (.wordEnd :: unaryMarkers a) (unaryMarkers b) out [])) =
    some (unaryMulCfg .outer (unaryMarkers a) (unaryMarkers b)
      (unaryMarkers b ++ out) []) := by
  have houter : ((fun o => o.bind (TM2.step unaryMulProgram))^[1])
      (some (unaryMulCfg .outer (.wordEnd :: unaryMarkers a)
        (unaryMarkers b) out [])) =
      some (unaryMulCfg .copy (unaryMarkers a) (unaryMarkers b) out []) := by
    simpa using unaryMul_outer_cons .wordEnd (unaryMarkers a)
      (unaryMarkers b) out
  have hcopy := unaryMul_copy_restore (unaryMarkers a) (unaryMarkers b) out
  have h := chain_iterations _ houter hcopy
  rw [show 2 * b + 3 = 1 + (2 * b + 2) by omega]
  simpa [unaryMarkers, List.reverse_replicate] using h

theorem unaryMul_iterate (a b : Nat) (out : List SparseSymbol) :
    ((fun o => o.bind (TM2.step unaryMulProgram))^[a * (2 * b + 3)])
      (some (unaryMulCfg .outer (unaryMarkers a) (unaryMarkers b) out [])) =
    some (unaryMulCfg .outer [] (unaryMarkers b)
      (unaryMarkers (a * b) ++ out) []) := by
  induction a generalizing out with
  | zero => simp [unaryMarkers]
  | succ a ih =>
      have hs : unaryMarkers (a + 1) = .wordEnd :: unaryMarkers a := by
        rw [show a + 1 = Nat.succ a by omega]
        rfl
      rw [hs]
      have hround := unaryMul_one_round a b out
      have hrest := ih (unaryMarkers b ++ out)
      have h := chain_iterations _ hround hrest
      have hcost : (a + 1) * (2 * b + 3) =
          (2 * b + 3) + a * (2 * b + 3) := by ring
      rw [hcost]
      have hout : unaryMarkers (a * b) ++ (unaryMarkers b ++ out) =
          unaryMarkers ((a + 1) * b) ++ out := by
        have hp : (a + 1) * b = a * b + b := by ring
        rw [hp]
        simp only [unaryMarkers, List.replicate_add, List.append_assoc]
      rw [← hout]
      exact h

theorem unaryMul_correct (a b : Nat) :
    ((fun o => o.bind (TM2.step unaryMulProgram))^[a * (2 * b + 3) + 1])
      (some (unaryMulCfg .outer (unaryMarkers a) (unaryMarkers b) [] [])) =
    some (unaryMulCfg .done [] (unaryMarkers b)
      (unaryMarkers (a * b)) []) := by
  have hrun := unaryMul_iterate a b []
  have hdone : ((fun o => o.bind (TM2.step unaryMulProgram))^[1])
      (some (unaryMulCfg .outer [] (unaryMarkers b)
        (unaryMarkers (a * b) ++ []) [])) =
      some (unaryMulCfg .done [] (unaryMarkers b)
        (unaryMarkers (a * b) ++ []) []) := by
    simpa using unaryMul_outer_nil (unaryMarkers b)
      (unaryMarkers (a * b) ++ [])
  simpa using chain_iterations _ hrun hdone

def unaryMulCoreRenaming : StackRenaming UnaryMulStack CoreStack where
  encode
    | .source => .work3
    | .multiplier => .work1
    | .destination => .work4
    | .backup => .work5
  decode
    | .work3 => some .source
    | .work1 => some .multiplier
    | .work4 => some .destination
    | .work5 => some .backup
    | _ => none
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k <;> cases k' <;> simp_all

theorem unaryMul_core_correct {N : Nat} {R : Type}
    (a b : Nat) (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum UnaryMulLabel R) (FullInterpreterState N))
    (ambientState : FullInterpreterState N)
    (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (lensSpliceProgram unaryMulCoreRenaming
      FullInterpreterState.moveLens unaryMulProgram .done returnLabel right)))^[
        a * (2 * b + 3) + 2])
      (some (lensRenamedCfg unaryMulCoreRenaming
        FullInterpreterState.moveLens
        (unaryMulCfg .outer (unaryMarkers a) (unaryMarkers b) [] [])
        ambientState ambientStacks)) =
    some (lensReturnCfg unaryMulCoreRenaming FullInterpreterState.moveLens
      returnLabel
      (unaryMulCfg .done [] (unaryMarkers b) (unaryMarkers (a * b)) [])
      ambientState ambientStacks) := by
  convert transport_lensHaltingMacro_and_return unaryMulCoreRenaming
    FullInterpreterState.moveLens unaryMulProgram .done (by rfl)
    returnLabel right (unaryMul_correct a b) rfl ambientState ambientStacks
    using 1 <;> omega

end Lax20Proofs.RamToTM
