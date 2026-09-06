import Lax51Proofs.RamToTM.ReadInstruction
import Lax51Proofs.RamToTM.ShiftInstruction

namespace Lax51Proofs.RamToTM

open Lax51Proofs.Microcode

/-- The only unbounded data occurring in a fixed RAM instruction which must
be emitted by the TM interpreter's finite control. -/
def instrArgument : Instr -> Nat
  | .read a | .store a | .storeInd a => a
  | .write o | .load o | .add o | .sub o | .mul o | .div o
  | .and o | .or o | .xor o | .compl o | .shiftl o | .shiftr o => operandArgument o
  | .jump _ | .jzero _ | .jgtz _ | .halt => 0

/-- A uniform finite bound for every literal/address embedded in `p`. -/
def programArgumentBound (p : Program) : Nat :=
  (p.map instrArgument).foldr max 0

theorem instrArgument_le_programArgumentBound {p : Program} {pc : Nat}
    {i : Instr} (hfetch : p[pc]? = some i) :
    instrArgument i <= programArgumentBound p := by
  have hpc : pc < p.length := fetch_some_pc_lt hfetch
  have hi : p[pc] = i := by
    simpa [List.getElem?_eq_getElem hpc] using hfetch
  have himem : i ∈ p := by
    rw [← hi]
    exact List.getElem_mem hpc
  apply List.le_max_of_le' 0 (List.mem_map.mpr ⟨i, himem, rfl⟩)
  exact le_rfl

/-- Finite syntax for an operand whose numeric parameter is at most `N`. -/
inductive BoundedOp (N : Nat)
  | lit (argument : Fin (N + 1))
  | mem (argument : Fin (N + 1))
  | ind (argument : Fin (N + 1))
  deriving DecidableEq, Fintype, Inhabited

def BoundedOp.toOp {N : Nat} : BoundedOp N -> Op
  | .lit n => .lit n
  | .mem n => .mem n
  | .ind n => .ind n

@[simp] theorem BoundedOp.operandArgument_toOp {N : Nat} (o : BoundedOp N) :
    operandArgument o.toOp <= N := by
  cases o <;> simp [BoundedOp.toOp, operandArgument] <;> omega

def BoundedOp.ofOp {N : Nat} (o : Op) (h : operandArgument o <= N) :
    BoundedOp N :=
  match o with
  | .lit n => .lit ⟨n, by simpa [operandArgument] using Nat.lt_succ_of_le h⟩
  | .mem n => .mem ⟨n, by simpa [operandArgument] using Nat.lt_succ_of_le h⟩
  | .ind n => .ind ⟨n, by simpa [operandArgument] using Nat.lt_succ_of_le h⟩

@[simp] theorem BoundedOp.toOp_ofOp {N : Nat} (o : Op)
    (h : operandArgument o <= N) : (BoundedOp.ofOp o h).toOp = o := by
  cases o <;> rfl

theorem operandArgument_le_programArgumentBound {p : Program} {pc : Nat}
    {o : Op} {i : Instr} (hfetch : p[pc]? = some i)
    (hi : instrArgument i = operandArgument o) :
    operandArgument o <= programArgumentBound p := by
  rw [← hi]
  exact instrArgument_le_programArgumentBound hfetch

def operandEvalStartLabel {R : Type} (o : Op) : OperandEvalLabel o R := by
  cases o <;> exact Sum.inl LiteralWordLabel.emit

@[simp] theorem operandEvalStartCfg_label {N : Nat} {R : Type} (o : Op)
    (hN : operandArgument o <= N) (w accumulator : Nat)
    (m : SparseMemory) (state : FullInterpreterState N)
    (base : CoreStack -> List SparseSymbol) :
    (operandEvalStartCfg (R := R) o hN w accumulator m state base).l =
      some (operandEvalStartLabel o) := by
  cases o <;> rfl

theorem operandEvalStartCfg_coreStacks {N : Nat} {R : Type} (o : Op)
    (hN : operandArgument o <= N) (w : Nat) (s : SparseState)
    (state : FullInterpreterState N) :
    operandEvalStartCfg (R := R) o hN w s.acc s.mem state (coreStacks w s) =
      ⟨some (operandEvalStartLabel o),
        FullInterpreterState.literalLens.put state
          (BoundedLiteralControl.initial hN),
        coreStacks w s⟩ := by
  cases o <;>
    simp [operandEvalStartCfg, operandEvalStartLabel, literalOperandStartCfg,
      lensRenamedCfg, boundedLiteralWordCfg, literalWordStacks,
      renamedStacks, literalWordCoreRenaming, literalWordCoreDecode,
      literalQueryCoreRenaming, literalQueryCoreDecode,
      operandBoundaryBase_coreStacks, BoundedLiteralControl.initial]
  all_goals
    congr 2
    funext k
    cases k <;> simp [renamedStacks, literalWordCoreRenaming,
      literalWordCoreDecode, literalQueryCoreRenaming,
      literalQueryCoreDecode, operandBoundaryBase_coreStacks,
      operandBoundaryBase, coreStacks, literalWordStacks,
      encodeAccumulator]

end Lax51Proofs.RamToTM
