import Lax51Proofs.RamToTM.DispatcherControl

namespace Lax51Proofs.RamToTM

open Lax51Proofs.Microcode

/-! Canonical stacks at instruction boundaries.  Work stacks are empty there;
individual verified macros may use them between dispatcher labels. -/

inductive CoreStack
  | accumulator | memory | input | output
  | work0 | work1 | work2 | work3 | work4 | work5 | work6 | work7
  deriving DecidableEq, Fintype, Inhabited

def encodeAccumulator (w a : ℕ) : List SparseSymbol :=
  (fixedBits w a).map SparseSymbol.bit

def encodeInputStack (w : ℕ) (input : List ℕ) : List SparseSymbol :=
  encodeWordList w input ++ [.inputEnd]

/-- The output is reversed so appending one RAM word becomes pushing one
reversed encoded word at the top of the stack. -/
def encodeOutputStack (w : ℕ) (output : List ℕ) : List SparseSymbol :=
  (encodeWordList w output).reverse ++ [.outputEnd]

def encodeMemoryStack (w : ℕ) (memory : SparseMemory) : List SparseSymbol :=
  encodeSparseMemory w memory ++ [.memoryEnd]

def coreStacks (w : ℕ) (s : SparseState) : CoreStack → List SparseSymbol
  | .accumulator => encodeAccumulator w s.acc
  | .memory => encodeMemoryStack w s.mem
  | .input => encodeInputStack w s.inp
  | .output => encodeOutputStack w s.out
  | .work0 | .work1 | .work2 | .work3 | .work4 | .work5 | .work6 | .work7 => []

@[simp] theorem coreStacks_set_pc (w pc : ℕ) (s : SparseState) :
    coreStacks w { s with pc := pc } = coreStacks w s := by
  funext k
  cases k <;> rfl

@[simp] theorem encodeAccumulator_length (w a : ℕ) :
    (encodeAccumulator w a).length = w := by
  simp [encodeAccumulator]

@[simp] theorem encodeMemoryStack_length (w : ℕ) (m : SparseMemory) :
    (encodeMemoryStack w m).length = m.length * (2 * w + 3) + 1 := by
  simp [encodeMemoryStack]

@[simp] theorem encodeInputStack_length (w : ℕ) (input : List ℕ) :
    (encodeInputStack w input).length = input.length * (w + 1) + 1 := by
  simp [encodeInputStack]

@[simp] theorem encodeOutputStack_length (w : ℕ) (output : List ℕ) :
    (encodeOutputStack w output).length = output.length * (w + 1) + 1 := by
  simp [encodeOutputStack]

def coreSize (w : ℕ) (s : SparseState) : ℕ :=
  (coreStacks w s .accumulator).length +
    (coreStacks w s .memory).length +
    (coreStacks w s .input).length +
    (coreStacks w s .output).length

theorem coreSize_eq (w : ℕ) (s : SparseState) :
    coreSize w s = w + s.mem.length * (2 * w + 3) +
      s.inp.length * (w + 1) + s.out.length * (w + 1) + 3 := by
  simp [coreSize, coreStacks]
  omega

/-- Boundary representation used in the one-step simulation theorem. -/
structure RepresentsSparseState (p : Program) (w : ℕ)
    (label : DispatchLabel p) (tapes : CoreStack → List SparseSymbol)
    (s : SparseState) : Prop where
  label_eq : label = stateDispatchLabel p s
  stacks_eq : tapes = coreStacks w s

theorem RepresentsSparseState.initial (p : Program) (w : ℕ) (input : List ℕ) :
    RepresentsSparseState p w (initialDispatchLabel p)
      (coreStacks w (sparseInitState input)) (sparseInitState input) := by
  constructor
  · apply congrArg DispatchLabel.fetch
    apply Fin.ext
    simp [initialDispatchLabel, stateDispatchLabel, sparseInitState]
  · rfl

theorem coreSize_le_of_run {p : Program} {w t : ℕ} {input : List ℕ}
    {s : SparseState} (hrun : sparseRun w p t (sparseInitState input) = some s) :
    coreSize w s ≤ w + t * (2 * w + 3) +
      input.length * (w + 1) + t * (w + 1) + 3 := by
  rw [coreSize_eq]
  have hm := sparseRun_init_mem_length_le hrun
  have hi := sparseRun_init_inp_length_le hrun
  have ho := sparseRun_init_out_length_le hrun
  nlinarith

end Lax51Proofs.RamToTM
