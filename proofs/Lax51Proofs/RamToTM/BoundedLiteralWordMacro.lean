import Lax51Proofs.RamToTM.LiteralWordMacro

namespace Lax51Proofs.RamToTM

open Turing TM2

structure BoundedLiteralControl (N : ℕ) where
  held : Option SparseSymbol
  remaining : Fin (N + 1)
  deriving DecidableEq, Fintype

instance (N : ℕ) : Inhabited (BoundedLiteralControl N) :=
  ⟨⟨none, 0⟩⟩

def BoundedLiteralControl.initial {N n : ℕ} (hn : n ≤ N) :
    BoundedLiteralControl N :=
  ⟨none, ⟨n, by omega⟩⟩

def BoundedLiteralControl.advance {N : ℕ}
    (s : BoundedLiteralControl N) : BoundedLiteralControl N :=
  ⟨none, ⟨s.remaining.val.div2,
    lt_of_le_of_lt (Nat.div_le_self _ _) s.remaining.isLt⟩⟩

def boundedLiteralWordProgram (N : ℕ) : LiteralWordLabel →
    TM2.Stmt (fun _ : LiteralWordStack => SparseSymbol)
      LiteralWordLabel (BoundedLiteralControl N)
  | .emit =>
      .pop .query (fun s a => { s with held := a }) <|
        .branch (fun s => s.held.isNone)
          (.load (fun s => { s with held := none }) <| .goto fun _ => .restore)
          (.push .backup (fun s => s.held.getD (.bit false)) <|
            .push .result (fun s => .bit s.remaining.val.bodd) <|
              .load BoundedLiteralControl.advance <| .goto fun _ => .emit)
  | .restore =>
      .pop .backup (fun s a => { s with held := a }) <|
        .branch (fun s => s.held.isNone)
          (.load (fun s => { s with held := none }) <| .goto fun _ => .done)
          (.push .query (fun s => s.held.getD (.bit false)) <|
            .load (fun s => { s with held := none }) <| .goto fun _ => .restore)
  | .done => .halt

def boundedLiteralWordCfg (N : ℕ) (label : LiteralWordLabel)
    (remaining : Fin (N + 1)) (query backup result : List SparseSymbol) :
    TM2.Cfg (fun _ : LiteralWordStack => SparseSymbol)
      LiteralWordLabel (BoundedLiteralControl N) where
  l := some label
  var := ⟨none, remaining⟩
  stk := literalWordStacks query backup result

@[simp] theorem boundedLiteralWord_step_emit_nil (N : ℕ)
    (remaining : Fin (N + 1)) (backup result : List SparseSymbol) :
    TM2.step (boundedLiteralWordProgram N)
      (boundedLiteralWordCfg N .emit remaining [] backup result) =
    some (boundedLiteralWordCfg N .restore remaining [] backup result) := by
  simp [boundedLiteralWordProgram, boundedLiteralWordCfg, literalWordStacks]

@[simp] theorem boundedLiteralWord_step_emit_cons (N : ℕ)
    (remaining : Fin (N + 1)) (a : SparseSymbol)
    (query backup result : List SparseSymbol) :
    TM2.step (boundedLiteralWordProgram N)
      (boundedLiteralWordCfg N .emit remaining (a :: query) backup result) =
    some (boundedLiteralWordCfg N .emit
      ⟨remaining.val.div2,
        lt_of_le_of_lt (Nat.div_le_self _ _) remaining.isLt⟩
      query (a :: backup) (.bit remaining.val.bodd :: result)) := by
  simp [boundedLiteralWordProgram, BoundedLiteralControl.advance,
    boundedLiteralWordCfg, literalWordStacks, Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem boundedLiteralWord_step_restore_nil (N : ℕ)
    (remaining : Fin (N + 1)) (query result : List SparseSymbol) :
    TM2.step (boundedLiteralWordProgram N)
      (boundedLiteralWordCfg N .restore remaining query [] result) =
    some (boundedLiteralWordCfg N .done remaining query [] result) := by
  simp [boundedLiteralWordProgram, boundedLiteralWordCfg, literalWordStacks]

@[simp] theorem boundedLiteralWord_step_restore_cons (N : ℕ)
    (remaining : Fin (N + 1)) (a : SparseSymbol)
    (query backup result : List SparseSymbol) :
    TM2.step (boundedLiteralWordProgram N)
      (boundedLiteralWordCfg N .restore remaining query (a :: backup) result) =
    some (boundedLiteralWordCfg N .restore remaining
      (a :: query) backup result) := by
  simp [boundedLiteralWordProgram, boundedLiteralWordCfg,
    literalWordStacks, Function.update]
  congr 2
  funext k
  cases k <;> rfl

theorem boundedLiteralWord_emit_iterate (N : ℕ)
    (remaining : Fin (N + 1)) (query backup result : List SparseSymbol) :
    ((fun o : Option (TM2.Cfg (fun _ : LiteralWordStack => SparseSymbol)
      LiteralWordLabel (BoundedLiteralControl N)) =>
        o.bind (TM2.step (boundedLiteralWordProgram N)))^[query.length])
      (some (boundedLiteralWordCfg N .emit remaining query backup result)) =
    some (boundedLiteralWordCfg N .emit
      ⟨remaining.val / 2 ^ query.length,
        lt_of_le_of_lt (Nat.div_le_self _ _) remaining.isLt⟩
      [] (query.reverse ++ backup)
      ((fixedBits query.length remaining.val).reverse.map SparseSymbol.bit ++
        result)) := by
  induction query generalizing remaining backup result with
  | nil => simp [boundedLiteralWordCfg, fixedBits]
  | cons a query ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, boundedLiteralWord_step_emit_cons]
      rw [ih]
      congr 2
      · apply Fin.ext
        simp only [Nat.div2_val, Nat.div_div_eq_div_mul, pow_succ]
        rw [Nat.mul_comm]
      · simp [List.reverse_cons, List.append_assoc]
      · simp [fixedBits, List.map_reverse, List.append_assoc]

theorem boundedLiteralWord_restore_iterate (N : ℕ)
    (remaining : Fin (N + 1)) (query backup result : List SparseSymbol) :
    ((fun o : Option (TM2.Cfg (fun _ : LiteralWordStack => SparseSymbol)
      LiteralWordLabel (BoundedLiteralControl N)) =>
        o.bind (TM2.step (boundedLiteralWordProgram N)))^[backup.length])
      (some (boundedLiteralWordCfg N .restore remaining query backup result)) =
    some (boundedLiteralWordCfg N .restore remaining
      (backup.reverse ++ query) [] result) := by
  induction backup generalizing query with
  | nil => rfl
  | cons a backup ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, boundedLiteralWord_step_restore_cons]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem boundedLiteralWord_correct_exact (N n : ℕ) (hn : n ≤ N)
    (query result : List SparseSymbol) :
    ((fun o : Option (TM2.Cfg (fun _ : LiteralWordStack => SparseSymbol)
      LiteralWordLabel (BoundedLiteralControl N)) =>
        o.bind (TM2.step (boundedLiteralWordProgram N)))^[
          2 * query.length + 2])
      (some (boundedLiteralWordCfg N .emit ⟨n, by omega⟩ query [] result)) =
    some (boundedLiteralWordCfg N .done
      ⟨n / 2 ^ query.length, by
        exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩
      query []
      ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result)) := by
  let stepO := fun o : Option
      (TM2.Cfg (fun _ : LiteralWordStack => SparseSymbol)
        LiteralWordLabel (BoundedLiteralControl N)) =>
    o.bind (TM2.step (boundedLiteralWordProgram N))
  let initial : Fin (N + 1) := ⟨n, by omega⟩
  let remaining : Fin (N + 1) :=
    ⟨n / 2 ^ query.length,
      lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩
  have h0 := boundedLiteralWord_emit_iterate N initial query [] result
  have h1raw := boundedLiteralWord_step_emit_nil N remaining query.reverse
    ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result)
  have h1 : (stepO^[1])
      (some (boundedLiteralWordCfg N .emit remaining [] query.reverse
        ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result))) =
    some (boundedLiteralWordCfg N .restore remaining [] query.reverse
      ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result)) := by
    simpa [stepO] using h1raw
  have h2 := boundedLiteralWord_restore_iterate N remaining [] query.reverse
    ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result)
  have h2' := h2
  simp only [List.reverse_reverse, List.append_nil] at h2'
  have h3raw := boundedLiteralWord_step_restore_nil N remaining query
    ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result)
  have h3 : (stepO^[1])
      (some (boundedLiteralWordCfg N .restore remaining query []
        ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result))) =
    some (boundedLiteralWordCfg N .done remaining query []
      ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result)) := by
    simpa [stepO] using h3raw
  have chain {r s : ℕ}
      {x y z : Option (TM2.Cfg (fun _ : LiteralWordStack => SparseSymbol)
        LiteralWordLabel (BoundedLiteralControl N))}
      (hr : (stepO^[r]) x = y) (hs : (stepO^[s]) y = z) :
      (stepO^[s + r]) x = z := by
    rw [Function.iterate_add_apply, hr, hs]
  have h0' := h0
  simp only [List.append_nil] at h0'
  have hrun := chain (chain (chain h0' h1) h2') h3
  simp only [List.length_reverse] at hrun
  have hexp : 1 + (query.length + (1 + query.length)) =
      2 * query.length + 2 := by omega
  rw [hexp] at hrun
  simpa [stepO, initial, remaining] using hrun

end Lax51Proofs.RamToTM
