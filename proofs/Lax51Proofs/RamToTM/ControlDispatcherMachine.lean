import Lax51Proofs.RamToTM.InterpreterState

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax13.Ram

structure DispatchControl where
  held : Option SparseSymbol
  anyTrue : Bool
  deriving DecidableEq, Fintype, Inhabited

def DispatchControl.observe (s : DispatchControl) (a : Option SparseSymbol) :
    DispatchControl :=
  { s with
    held := a,
    anyTrue := s.anyTrue || match a with | some (.bit true) => true | _ => false }

def DispatchControl.clearHeld (s : DispatchControl) : DispatchControl :=
  { s with held := none }

inductive ControlDispatchLabel (p : Program)
  | fetch (pc : BoundedPC p)
  | scanAccumulator (pc target : BoundedPC p) (jumpOnZero : Bool)
  | restoreAccumulator (pc target : BoundedPC p) (jumpOnZero : Bool)
  | data (pc : BoundedPC p) (kind : InstrClass)
  | stopped
  deriving DecidableEq, Fintype, Inhabited

def controlFetchLabel (p : Program) (pc : ℕ) : ControlDispatchLabel p :=
  .fetch (boundPC p pc)

def controlDispatchMachine (p : Program) : Turing.FinTM2 where
  K := CoreStack
  k₀ := .input
  k₁ := .output
  Γ _ := SparseSymbol
  Λ := ControlDispatchLabel p
  main := .fetch (boundPC p 0)
  σ := DispatchControl
  initialState := default
  m
    | .fetch pc =>
        match pc.fetch with
        | none | some .halt => .goto fun _ => .stopped
        | some (.jump target) => .goto fun _ => .fetch (jumpPC p target)
        | some (.jzero target) =>
            .load (fun _ => default) <|
              .goto fun _ => .scanAccumulator pc (jumpPC p target) true
        | some (.jgtz target) =>
            .load (fun _ => default) <|
              .goto fun _ => .scanAccumulator pc (jumpPC p target) false
        | some i => .goto fun _ => .data pc (instrClass i)
    | .scanAccumulator pc target jumpOnZero =>
        .pop .accumulator DispatchControl.observe <|
          .branch (fun s => s.held.isNone)
            (.load DispatchControl.clearHeld <|
              .goto fun _ => .restoreAccumulator pc target jumpOnZero)
            (.push .work0 (fun s => s.held.getD default) <|
              .load DispatchControl.clearHeld <|
                .goto fun _ => .scanAccumulator pc target jumpOnZero)
    | .restoreAccumulator pc target jumpOnZero =>
        .pop .work0 (fun s a => { s with held := a }) <|
          .branch (fun s => s.held.isNone)
            (.load DispatchControl.clearHeld <|
              .branch (fun s => s.anyTrue == !jumpOnZero)
                (.load (fun _ => default) <| .goto fun _ => .fetch target)
                (.load (fun _ => default) <| .goto fun _ => .fetch (nextPC p pc)))
            (.push .accumulator (fun s => s.held.getD default) <|
              .load DispatchControl.clearHeld <|
                .goto fun _ => .restoreAccumulator pc target jumpOnZero)
    | .data _ _ => .halt
    | .stopped => .halt

def controlDispatchCfg (p : Program) (label : ControlDispatchLabel p)
    (state : DispatchControl) (tapes : CoreStack → List SparseSymbol) :
    (controlDispatchMachine p).Cfg where
  l := some label
  var := state
  stk := tapes

def controlBoundaryCfg (p : Program) (pc : ℕ) (w : ℕ) (s : SparseState) :
    (controlDispatchMachine p).Cfg :=
  controlDispatchCfg p (.fetch (boundPC p pc)) default (coreStacks w s)

def controlWorkTapes (base : CoreStack → List SparseSymbol)
    (accumulator work : List SparseSymbol) : CoreStack → List SparseSymbol
  | .accumulator => accumulator
  | .work0 => work
  | k => base k

def controlScanCfg (p : Program) (pc target : BoundedPC p) (jumpOnZero any : Bool)
    (accumulator work : List SparseSymbol)
    (base : CoreStack → List SparseSymbol) : (controlDispatchMachine p).Cfg :=
  controlDispatchCfg p (.scanAccumulator pc target jumpOnZero)
    { held := none, anyTrue := any } (controlWorkTapes base accumulator work)

def controlRestoreCfg (p : Program) (pc target : BoundedPC p)
    (jumpOnZero any : Bool) (accumulator work : List SparseSymbol)
    (base : CoreStack → List SparseSymbol) : (controlDispatchMachine p).Cfg :=
  controlDispatchCfg p (.restoreAccumulator pc target jumpOnZero)
    { held := none, anyTrue := any } (controlWorkTapes base accumulator work)

@[simp] theorem control_step_scan_bit (p : Program) (pc target : BoundedPC p)
    (jumpOnZero any bit : Bool) (bits work : List SparseSymbol)
    (base : CoreStack → List SparseSymbol) :
    (controlDispatchMachine p).step
      (controlScanCfg p pc target jumpOnZero any (.bit bit :: bits) work base) =
      some (controlScanCfg p pc target jumpOnZero (any || bit) bits
        (.bit bit :: work) base) := by
  cases bit <;>
  simp [controlDispatchMachine, controlScanCfg, controlDispatchCfg, controlWorkTapes,
    DispatchControl.observe, DispatchControl.clearHeld, Function.update]
  all_goals
    congr 2
    funext k
    cases k <;> rfl

@[simp] theorem control_step_scan_nil (p : Program) (pc target : BoundedPC p)
    (jumpOnZero any : Bool) (work : List SparseSymbol)
    (base : CoreStack → List SparseSymbol) :
    (controlDispatchMachine p).step
      (controlScanCfg p pc target jumpOnZero any [] work base) =
      some (controlRestoreCfg p pc target jumpOnZero any [] work base) := by
  simp [controlDispatchMachine, controlScanCfg, controlRestoreCfg,
    controlDispatchCfg, controlWorkTapes, DispatchControl.observe,
    DispatchControl.clearHeld]
  congr 2
  funext k
  cases k <;> rfl

theorem control_scan_iterate (p : Program) (pc target : BoundedPC p)
    (jumpOnZero any : Bool) (bits : List Bool) (work : List SparseSymbol)
    (base : CoreStack → List SparseSymbol) :
    ((fun o : Option (controlDispatchMachine p).Cfg =>
      o.bind (controlDispatchMachine p).step)^[bits.length])
      (some (controlScanCfg p pc target jumpOnZero any
        (bits.map SparseSymbol.bit) work base)) =
      some (controlScanCfg p pc target jumpOnZero (any || containsTrue bits) []
        ((bits.reverse.map SparseSymbol.bit) ++ work) base) := by
  induction bits generalizing any work with
  | nil => simp [containsTrue]
  | cons bit bits ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [List.map_cons, Option.bind_some, control_step_scan_bit]
      rw [ih]
      simp [containsTrue, List.reverse_cons, List.append_assoc, Bool.or_assoc]

@[simp] theorem control_step_restore_bit (p : Program) (pc target : BoundedPC p)
    (jumpOnZero any bit : Bool) (accumulator : List SparseSymbol) (bits : List Bool)
    (base : CoreStack → List SparseSymbol) :
    (controlDispatchMachine p).step
      (controlRestoreCfg p pc target jumpOnZero any accumulator
        (.bit bit :: bits.map SparseSymbol.bit) base) =
      some (controlRestoreCfg p pc target jumpOnZero any
        (.bit bit :: accumulator) (bits.map SparseSymbol.bit) base) := by
  simp [controlDispatchMachine, controlRestoreCfg, controlDispatchCfg,
    controlWorkTapes, DispatchControl.clearHeld, Function.update]
  congr 2
  funext k
  cases k <;> rfl

theorem control_restore_iterate (p : Program) (pc target : BoundedPC p)
    (jumpOnZero any : Bool) (accumulator : List SparseSymbol) (bits : List Bool)
    (base : CoreStack → List SparseSymbol) :
    ((fun o : Option (controlDispatchMachine p).Cfg =>
      o.bind (controlDispatchMachine p).step)^[bits.length])
      (some (controlRestoreCfg p pc target jumpOnZero any accumulator
        (bits.map SparseSymbol.bit) base)) =
      some (controlRestoreCfg p pc target jumpOnZero any
        (bits.reverse.map SparseSymbol.bit ++ accumulator) [] base) := by
  induction bits generalizing accumulator with
  | nil => rfl
  | cons bit bits ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [List.map_cons, Option.bind_some, control_step_restore_bit]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

def conditionalDestination (p : Program) (pc target : BoundedPC p)
    (jumpOnZero any : Bool) : BoundedPC p :=
  if any == !jumpOnZero then target else nextPC p pc

@[simp] theorem control_step_restore_nil (p : Program) (pc target : BoundedPC p)
    (jumpOnZero any : Bool) (accumulator : List SparseSymbol)
    (base : CoreStack → List SparseSymbol) :
    (controlDispatchMachine p).step
      (controlRestoreCfg p pc target jumpOnZero any accumulator [] base) =
      some (controlDispatchCfg p
        (.fetch (conditionalDestination p pc target jumpOnZero any)) default
        (controlWorkTapes base accumulator [])) := by
  by_cases h : any == !jumpOnZero <;>
    simp [controlDispatchMachine, controlRestoreCfg, controlDispatchCfg,
      controlWorkTapes, DispatchControl.clearHeld, conditionalDestination, h]
  all_goals
    congr 2
    funext k
    cases k <;> rfl

@[simp] theorem controlWorkTapes_boundary (w : ℕ) (s : SparseState) :
    controlWorkTapes (coreStacks w s) (encodeAccumulator w s.acc) [] =
      coreStacks w s := by
  funext k
  cases k <;> rfl

theorem containsTrue_fixedBits (w a : ℕ) (ha : a < 2 ^ w) :
    containsTrue (fixedBits w a) = decide (0 < a) := by
  by_cases hp : 0 < a
  · cases hc : containsTrue (fixedBits w a) with
    | false =>
        have hz := containsTrue_false_bitsValue_zero hc
        rw [bitsValue_fixedBits_of_lt ha] at hz
        omega
    | true => simp [hp]
  · have hz : a = 0 := by omega
    subst a
    simp [fixedBits_zero]
    induction w with
    | zero => rfl
    | succ w ih => simpa [List.replicate_succ, containsTrue] using ih

@[simp] theorem control_step_jzero_fetch {p : Program} {pc target w : ℕ}
    {s : SparseState} (hfetch : p[pc]? = some (.jzero target)) :
    (controlDispatchMachine p).step (controlBoundaryCfg p pc w s) =
      some (controlScanCfg p (boundPC p pc) (jumpPC p target) true false
        (fixedBits w s.acc |>.map SparseSymbol.bit) [] (coreStacks w s)) := by
  simp [controlDispatchMachine, controlBoundaryCfg, controlScanCfg,
    controlDispatchCfg, controlWorkTapes, encodeAccumulator, fetch_boundPC, hfetch]
  congr 2
  funext k
  cases k <;> rfl

theorem control_jzero_correct {p : Program} {pc target w : ℕ} {s : SparseState}
    (hfetch : p[pc]? = some (.jzero target)) (hacc : s.acc < 2 ^ w) :
    let next := if s.acc = 0 then target else pc + 1
    ((fun o : Option (controlDispatchMachine p).Cfg =>
      o.bind (controlDispatchMachine p).step)^[2 * w + 3])
      (some (controlBoundaryCfg p pc w s)) =
      some (controlBoundaryCfg p next w { s with pc := next }) := by
  let stepO := fun o : Option (controlDispatchMachine p).Cfg =>
    o.bind fun a => (controlDispatchMachine p).step a
  let bits := fixedBits w s.acc
  let sourcePC := boundPC p pc
  let targetPC := jumpPC p target
  change (stepO^[2 * w + 3]) (some (controlBoundaryCfg p pc w s)) = _
  have hpc : pc < p.length := fetch_some_pc_lt hfetch
  have chain {m n : ℕ} {a b c : Option (controlDispatchMachine p).Cfg}
      (h₁ : (stepO^[m]) a = b) (h₂ : (stepO^[n]) b = c) :
      (stepO^[n + m]) a = c := by
    rw [Function.iterate_add_apply, h₁, h₂]
  have hf : (stepO^[1]) (some (controlBoundaryCfg p pc w s)) =
      some (controlScanCfg p sourcePC targetPC true false
        (bits.map SparseSymbol.bit) [] (coreStacks w s)) := by
    simpa [stepO, bits, sourcePC, targetPC] using
      control_step_jzero_fetch (w := w) (s := s) hfetch
  have hs := control_scan_iterate p sourcePC targetPC true false bits []
    (coreStacks w s)
  simp only [List.append_nil, Bool.false_or] at hs
  have hs0 : (stepO^[1])
      (some (controlScanCfg p sourcePC targetPC true (containsTrue bits) []
        (bits.reverse.map SparseSymbol.bit) (coreStacks w s))) =
      some (controlRestoreCfg p sourcePC targetPC true (containsTrue bits) []
        (bits.reverse.map SparseSymbol.bit) (coreStacks w s)) := by
    simpa [stepO] using control_step_scan_nil p sourcePC targetPC true
      (containsTrue bits) (bits.reverse.map SparseSymbol.bit) (coreStacks w s)
  have hr := control_restore_iterate p sourcePC targetPC true (containsTrue bits) []
    bits.reverse (coreStacks w s)
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  have hr0 := control_step_restore_nil p sourcePC targetPC true (containsTrue bits)
    (bits.map SparseSymbol.bit) (coreStacks w s)
  have h := chain (chain (chain (chain hf hs) hs0) hr)
    (show (stepO^[1]) _ = _ by simpa [stepO] using hr0)
  have htime : 1 + (bits.length + (1 + (bits.length + 1))) = 2 * w + 3 := by
    simp [bits]
    omega
  rw [htime] at h
  have htapes :
      controlWorkTapes (coreStacks w s) (bits.map SparseSymbol.bit) [] =
        coreStacks w s := by
    simpa [bits, encodeAccumulator] using controlWorkTapes_boundary w s
  rw [htapes] at h
  rw [containsTrue_fixedBits w s.acc hacc] at h
  by_cases hz : s.acc = 0
  · rw [← coreStacks_set_pc w target s] at h
    simpa [conditionalDestination, sourcePC, targetPC, jumpPC, hz,
      controlBoundaryCfg, bits, encodeAccumulator, controlWorkTapes_boundary,
      ] using h
  · have hp : 0 < s.acc := by omega
    rw [← coreStacks_set_pc w (pc + 1) s] at h
    simpa [conditionalDestination, sourcePC, targetPC, hz, hp,
      controlBoundaryCfg, bits, encodeAccumulator, controlWorkTapes_boundary,
      nextPC_boundPC_of_lt hpc] using h

@[simp] theorem control_step_jgtz_fetch {p : Program} {pc target w : ℕ}
    {s : SparseState} (hfetch : p[pc]? = some (.jgtz target)) :
    (controlDispatchMachine p).step (controlBoundaryCfg p pc w s) =
      some (controlScanCfg p (boundPC p pc) (jumpPC p target) false false
        (fixedBits w s.acc |>.map SparseSymbol.bit) [] (coreStacks w s)) := by
  simp [controlDispatchMachine, controlBoundaryCfg, controlScanCfg,
    controlDispatchCfg, controlWorkTapes, fetch_boundPC, hfetch]
  congr 2
  funext k
  cases k <;> rfl

theorem control_jgtz_correct {p : Program} {pc target w : ℕ} {s : SparseState}
    (hfetch : p[pc]? = some (.jgtz target)) (hacc : s.acc < 2 ^ w) :
    let next := if 0 < s.acc then target else pc + 1
    ((fun o : Option (controlDispatchMachine p).Cfg =>
      o.bind (controlDispatchMachine p).step)^[2 * w + 3])
      (some (controlBoundaryCfg p pc w s)) =
      some (controlBoundaryCfg p next w { s with pc := next }) := by
  let stepO := fun o : Option (controlDispatchMachine p).Cfg =>
    o.bind fun a => (controlDispatchMachine p).step a
  let bits := fixedBits w s.acc
  let sourcePC := boundPC p pc
  let targetPC := jumpPC p target
  change (stepO^[2 * w + 3]) (some (controlBoundaryCfg p pc w s)) = _
  have hpc : pc < p.length := fetch_some_pc_lt hfetch
  have chain {m n : ℕ} {a b c : Option (controlDispatchMachine p).Cfg}
      (h₁ : (stepO^[m]) a = b) (h₂ : (stepO^[n]) b = c) :
      (stepO^[n + m]) a = c := by
    rw [Function.iterate_add_apply, h₁, h₂]
  have hf : (stepO^[1]) (some (controlBoundaryCfg p pc w s)) =
      some (controlScanCfg p sourcePC targetPC false false
        (bits.map SparseSymbol.bit) [] (coreStacks w s)) := by
    simpa [stepO, bits, sourcePC, targetPC] using
      control_step_jgtz_fetch (w := w) (s := s) hfetch
  have hs := control_scan_iterate p sourcePC targetPC false false bits []
    (coreStacks w s)
  simp only [List.append_nil, Bool.false_or] at hs
  have hs0 : (stepO^[1])
      (some (controlScanCfg p sourcePC targetPC false (containsTrue bits) []
        (bits.reverse.map SparseSymbol.bit) (coreStacks w s))) =
      some (controlRestoreCfg p sourcePC targetPC false (containsTrue bits) []
        (bits.reverse.map SparseSymbol.bit) (coreStacks w s)) := by
    simpa [stepO] using control_step_scan_nil p sourcePC targetPC false
      (containsTrue bits) (bits.reverse.map SparseSymbol.bit) (coreStacks w s)
  have hr := control_restore_iterate p sourcePC targetPC false (containsTrue bits) []
    bits.reverse (coreStacks w s)
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  have hr0 := control_step_restore_nil p sourcePC targetPC false (containsTrue bits)
    (bits.map SparseSymbol.bit) (coreStacks w s)
  have h := chain (chain (chain (chain hf hs) hs0) hr)
    (show (stepO^[1]) _ = _ by simpa [stepO] using hr0)
  have htime : 1 + (bits.length + (1 + (bits.length + 1))) = 2 * w + 3 := by
    simp [bits]
    omega
  rw [htime] at h
  have htapes :
      controlWorkTapes (coreStacks w s) (bits.map SparseSymbol.bit) [] =
        coreStacks w s := by
    simpa [bits, encodeAccumulator] using controlWorkTapes_boundary w s
  rw [htapes] at h
  rw [containsTrue_fixedBits w s.acc hacc] at h
  by_cases hp : 0 < s.acc
  · rw [← coreStacks_set_pc w target s] at h
    simpa [conditionalDestination, sourcePC, targetPC, jumpPC, hp,
      controlBoundaryCfg, bits, encodeAccumulator, controlWorkTapes_boundary] using h
  · have hz : s.acc = 0 := by omega
    rw [← coreStacks_set_pc w (pc + 1) s] at h
    simpa [conditionalDestination, sourcePC, targetPC, hp, hz,
      controlBoundaryCfg, bits, encodeAccumulator, controlWorkTapes_boundary,
      nextPC_boundPC_of_lt hpc] using h

@[simp] theorem control_step_jump {p : Program} {pc target : ℕ}
    (hfetch : p[pc]? = some (.jump target))
    (state : DispatchControl) (tapes : CoreStack → List SparseSymbol) :
    (controlDispatchMachine p).step
        (controlDispatchCfg p (.fetch (boundPC p pc)) state tapes) =
      some (controlDispatchCfg p (.fetch (jumpPC p target)) state tapes) := by
  simp [controlDispatchMachine, controlDispatchCfg, fetch_boundPC, hfetch]
  rfl

theorem control_jump_correct {p : Program} {pc target w : ℕ} {s : SparseState}
    (hfetch : p[pc]? = some (.jump target)) :
    (controlDispatchMachine p).step (controlBoundaryCfg p pc w s) =
      some (controlBoundaryCfg p target w { s with pc := target }) := by
  unfold controlBoundaryCfg
  rw [coreStacks_set_pc]
  exact control_step_jump hfetch default (coreStacks w s)

@[simp] theorem control_step_halt_fetch {p : Program} {pc w : ℕ}
    {s : SparseState} (hfetch : p[pc]? = some .halt) :
    (controlDispatchMachine p).step (controlBoundaryCfg p pc w s) =
      some (controlDispatchCfg p .stopped default (coreStacks w s)) := by
  simp [controlDispatchMachine, controlBoundaryCfg, controlDispatchCfg,
    fetch_boundPC, hfetch]
  rfl

@[simp] theorem control_step_missing_fetch {p : Program} {pc w : ℕ}
    {s : SparseState} (hfetch : p[pc]? = none) :
    (controlDispatchMachine p).step (controlBoundaryCfg p pc w s) =
      some (controlDispatchCfg p .stopped default (coreStacks w s)) := by
  simp [controlDispatchMachine, controlBoundaryCfg, controlDispatchCfg,
    fetch_boundPC, hfetch]
  rfl

@[simp] theorem control_step_stopped (p : Program) (state : DispatchControl)
    (tapes : CoreStack → List SparseSymbol) :
    (controlDispatchMachine p).step
      (controlDispatchCfg p .stopped state tapes) =
      some { l := none, var := state, stk := tapes } := by
  rfl

end Lax51Proofs.RamToTM
