import Lax20Proofs.RamToTM.WriteInstruction

namespace Lax20Proofs.RamToTM

open Turing TM2

inductive CopyStack | source | destination | backup
  deriving DecidableEq, Fintype, Inhabited

inductive CopyLabel | scan | restore | done
  deriving DecidableEq, Fintype, Inhabited

def copyProgram : CopyLabel ->
    TM2.Stmt (fun _ : CopyStack => SparseSymbol) CopyLabel SymbolMoveControl
  | .scan =>
      .pop .source (fun s a => { s with held := a }) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .restore)
        (.push .destination (fun s => s.held.getD default) <|
          .push .backup (fun s => s.held.getD default) <|
          .load (fun _ => default) <| .goto fun _ => .scan)
  | .restore =>
      .pop .backup (fun s a => { s with held := a }) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .done)
        (.push .source (fun s => s.held.getD default) <|
          .load (fun _ => default) <| .goto fun _ => .restore)
  | .done => .halt

def copyStacks (source destination backup : List SparseSymbol) :
    CopyStack -> List SparseSymbol
  | .source => source
  | .destination => destination
  | .backup => backup

def copyCfgState (label : CopyLabel) (state : SymbolMoveControl)
    (source destination backup : List SparseSymbol) :
    TM2.Cfg (fun _ : CopyStack => SparseSymbol) CopyLabel SymbolMoveControl where
  l := some label
  var := state
  stk := copyStacks source destination backup

def copyCfg (label : CopyLabel)
    (source destination backup : List SparseSymbol) :=
  copyCfgState label default source destination backup

@[simp] theorem copy_step_scan_cons (a : SparseSymbol) (xs ys bs : List SparseSymbol) :
    TM2.step copyProgram (copyCfg .scan (a :: xs) ys bs) =
      some (copyCfg .scan xs (a :: ys) (a :: bs)) := by
  simp [copyProgram, copyCfg, copyCfgState, copyStacks, Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem copy_step_scan_nil (ys bs : List SparseSymbol) :
    TM2.step copyProgram (copyCfg .scan [] ys bs) =
      some (copyCfg .restore [] ys bs) := by
  simp [copyProgram, copyCfg, copyCfgState, copyStacks]

@[simp] theorem copy_step_restore_cons (a : SparseSymbol) (xs ys bs : List SparseSymbol) :
    TM2.step copyProgram (copyCfg .restore xs ys (a :: bs)) =
      some (copyCfg .restore (a :: xs) ys bs) := by
  simp [copyProgram, copyCfg, copyCfgState, copyStacks, Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem copy_step_restore_nil (xs ys : List SparseSymbol) :
    TM2.step copyProgram (copyCfg .restore xs ys []) =
      some (copyCfg .done xs ys []) := by
  simp [copyProgram, copyCfg, copyCfgState, copyStacks]

private theorem chain_copy {X : Type} (step : X -> X)
    {a b c : X} {m n : Nat} (h1 : (step^[m]) a = b)
    (h2 : (step^[n]) b = c) : (step^[m + n]) a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, h1, h2]

theorem copy_scan_iterate (xs : List SparseSymbol) (ys bs : List SparseSymbol) :
    ((fun o => o.bind (TM2.step copyProgram))^[xs.length])
      (some (copyCfg .scan xs ys bs)) =
    some (copyCfg .scan [] (xs.reverse ++ ys) (xs.reverse ++ bs)) := by
  induction xs generalizing ys bs with
  | nil => rfl
  | cons a xs ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, copy_step_scan_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem copy_restore_iterate (xs ys bs : List SparseSymbol) :
    ((fun o => o.bind (TM2.step copyProgram))^[bs.length])
      (some (copyCfg .restore xs ys bs)) =
    some (copyCfg .restore (bs.reverse ++ xs) ys []) := by
  induction bs generalizing xs with
  | nil => rfl
  | cons a bs ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, copy_step_restore_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem copy_correct (xs ys : List SparseSymbol) :
    ((fun o => o.bind (TM2.step copyProgram))^[2 * xs.length + 2])
      (some (copyCfg .scan xs ys [])) =
    some (copyCfg .done xs (xs.reverse ++ ys) []) := by
  have h0 := copy_scan_iterate xs ys []
  simp only [List.append_nil] at h0
  have h1 : ((fun o => o.bind (TM2.step copyProgram))^[1])
      (some (copyCfg .scan [] (xs.reverse ++ ys) xs.reverse)) =
      some (copyCfg .restore [] (xs.reverse ++ ys) xs.reverse) := by
    simpa using copy_step_scan_nil (xs.reverse ++ ys) xs.reverse
  have h2 := copy_restore_iterate [] (xs.reverse ++ ys) xs.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h2
  have h3 : ((fun o => o.bind (TM2.step copyProgram))^[1])
      (some (copyCfg .restore xs (xs.reverse ++ ys) [])) =
      some (copyCfg .done xs (xs.reverse ++ ys) []) := by
    simpa using copy_step_restore_nil xs (xs.reverse ++ ys)
  have h := chain_copy _ (chain_copy _ (chain_copy _ h0 h1) h2) h3
  have ht : 2 * xs.length + 2 = xs.length + 1 + xs.length + 1 := by omega
  rw [ht]
  exact h

def copyCoreRenaming (source destination backup : CoreStack)
    (hsd : source ≠ destination) (hsb : source ≠ backup)
    (hdb : destination ≠ backup) : StackRenaming CopyStack CoreStack where
  encode
    | .source => source
    | .destination => destination
    | .backup => backup
  decode := fun k => if k = source then some .source
    else if k = destination then some .destination
    else if k = backup then some .backup else none
  decode_encode := by
    intro k
    cases k <;> simp [hsd, hsb, hdb, Ne.symm hsd, Ne.symm hsb, Ne.symm hdb]
  encode_decode := by
    intro k' k h
    cases k <;> simp only at h ⊢
    all_goals
      split at h <;> simp_all
    all_goals
      split at h <;> simp_all
    all_goals
      split at h <;> simp_all

end Lax20Proofs.RamToTM
