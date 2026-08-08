import Lax20Proofs.RamToTM.LengthPrefixAdapter

namespace Lax20Proofs.RamToTM

open Turing TM2
open Lax20.BinaryWordEncoding

structure PaddingControl where
  held : Option SparseSymbol := none
  more : Bool := false
  deriving DecidableEq, Fintype, Inhabited

inductive PaddingStack | raw | width | counter | backup | output
  deriving DecidableEq, Fintype, Inhabited

inductive PaddingLabel | start | copy | restore | scan | pad | finish | done
  deriving DecidableEq, Fintype, Inhabited

def paddingProgram : PaddingLabel →
    TM2.Stmt (fun _ : PaddingStack => SparseSymbol)
      PaddingLabel PaddingControl
  | .start =>
      .pop .raw (fun s a => {s with held := a}) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .done)
        (.load (fun _ => default) <| .goto fun _ => .copy)
  | .copy =>
      .pop .width (fun s a => {s with held := a}) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .restore)
        (.push .counter (fun s => s.held.getD default) <|
          .push .backup (fun s => s.held.getD default) <|
          .load (fun _ => default) <| .goto fun _ => .copy)
  | .restore =>
      .pop .backup (fun s a => {s with held := a}) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .scan)
        (.push .width (fun s => s.held.getD default) <|
          .load (fun _ => default) <| .goto fun _ => .restore)
  | .scan =>
      .pop .raw (fun s a => {s with held := a}) <|
      .branch (fun s => s.held.isNone)
        (.load (fun s => {s with more := false, held := none}) <|
          .goto fun _ => .pad) <|
      .branch (fun s => s.held = some .wordEnd)
        (.load (fun s => {s with more := true, held := none}) <|
          .goto fun _ => .pad) <|
      .pop .counter (fun s _ => s) <|
      .push .output (fun s => s.held.getD (.bit false)) <|
      .load (fun s => {s with held := none}) <|
      .goto fun _ => .scan
  | .pad =>
      .pop .counter (fun s a => {s with held := a}) <|
      .branch (fun s => s.held.isNone)
        (.load (fun s => {s with held := none}) <| .goto fun _ => .finish)
        (.push .output (fun _ => .bit false) <|
          .load (fun s => {s with held := none}) <| .goto fun _ => .pad)
  | .finish =>
      .push .output (fun _ => .wordEnd) <|
      .branch (fun s => s.more)
        (.load (fun _ => default) <| .goto fun _ => .copy)
        (.load (fun _ => default) <| .goto fun _ => .done)
  | .done => .halt

def paddingStacks (raw width counter backup output : List SparseSymbol) :
    PaddingStack → List SparseSymbol
  | .raw => raw
  | .width => width
  | .counter => counter
  | .backup => backup
  | .output => output

def paddingCfg (label : PaddingLabel) (control : PaddingControl)
    (raw width counter backup output : List SparseSymbol) :
    TM2.Cfg (fun _ : PaddingStack => SparseSymbol)
      PaddingLabel PaddingControl :=
  ⟨some label, control, paddingStacks raw width counter backup output⟩

theorem padding_copy_from (control : PaddingControl)
    (source raw counter backup output : List SparseSymbol) :
    ((fun o => o.bind (TM2.step paddingProgram))^[source.length + 1])
      (some (paddingCfg .copy control raw source counter backup output)) =
    some (paddingCfg .restore default raw []
      (source.reverse ++ counter) (source.reverse ++ backup) output) := by
  induction source generalizing control counter backup with
  | nil => simp [paddingProgram, paddingCfg, paddingStacks, TM2.step]
  | cons a source ih =>
      have hs : TM2.step paddingProgram
          (paddingCfg .copy control raw (a :: source) counter backup output) =
          some (paddingCfg .copy default raw source (a :: counter)
            (a :: backup) output) := by
        simp [paddingProgram, paddingCfg, paddingStacks, TM2.step,
          Function.update]
        funext k
        cases k <;> rfl
      have hs' : ((fun o => o.bind (TM2.step paddingProgram))^[1])
          (some (paddingCfg .copy control raw (a :: source) counter backup output)) =
          some (paddingCfg .copy default raw source (a :: counter)
            (a :: backup) output) := by simpa using hs
      have h := chain_iterations _ hs' (ih default (a :: counter) (a :: backup))
      rw [List.length_cons,
        show source.length + 1 + 1 = 1 + (source.length + 1) by omega]
      simpa [List.reverse_cons, List.append_assoc] using h

theorem padding_restore_from (source target raw counter output : List SparseSymbol) :
    ((fun o => o.bind (TM2.step paddingProgram))^[source.length + 1])
      (some (paddingCfg .restore default raw target counter source output)) =
    some (paddingCfg .scan default raw (source.reverse ++ target)
      counter [] output) := by
  induction source generalizing target with
  | nil => simp [paddingProgram, paddingCfg, paddingStacks, TM2.step]
  | cons a source ih =>
      have hs : TM2.step paddingProgram
          (paddingCfg .restore default raw target counter (a :: source) output) =
          some (paddingCfg .restore default raw (a :: target) counter source output) := by
        simp [paddingProgram, paddingCfg, paddingStacks, TM2.step,
          Function.update]
        funext k
        cases k <;> rfl
      have hs' : ((fun o => o.bind (TM2.step paddingProgram))^[1])
          (some (paddingCfg .restore default raw target counter (a :: source) output)) =
          some (paddingCfg .restore default raw (a :: target) counter source output) := by
        simpa using hs
      have h := chain_iterations _ hs' (ih (a :: target))
      rw [List.length_cons,
        show source.length + 1 + 1 = 1 + (source.length + 1) by omega]
      simpa [List.reverse_cons, List.append_assoc] using h

theorem padding_copy_width (w : Nat) (control : PaddingControl)
    (raw output : List SparseSymbol) :
    ((fun o => o.bind (TM2.step paddingProgram))^[2 * w + 2])
      (some (paddingCfg .copy control raw (unaryMarkers w) [] [] output)) =
    some (paddingCfg .scan default raw (unaryMarkers w)
      (unaryMarkers w) [] output) := by
  have hc := padding_copy_from control (unaryMarkers w) raw [] [] output
  have hr := padding_restore_from (unaryMarkers w).reverse [] raw
    (unaryMarkers w) output
  simp only [unaryMarkers, List.reverse_replicate, List.append_nil,
    List.length_replicate, List.reverse_reverse] at hc hr
  have h := chain_iterations _ hc hr
  rw [show (w + 1) + (w + 1) = 2 * w + 2 by omega] at h
  simpa [unaryMarkers] using h

theorem padding_scan_bits_from (bits : List Bool) (rest width : List SparseSymbol)
    (remaining : Nat) (hlen : bits.length ≤ remaining)
    (output : List SparseSymbol) :
    ((fun o => o.bind (TM2.step paddingProgram))^[bits.length])
      (some (paddingCfg .scan default
        (bits.map SparseSymbol.bit ++ rest) width
        (unaryMarkers remaining) [] output)) =
    some (paddingCfg .scan default rest width
      (unaryMarkers (remaining - bits.length)) []
      (bits.reverse.map SparseSymbol.bit ++ output)) := by
  induction bits generalizing remaining output with
  | nil => simp
  | cons bit bits ih =>
      simp only [List.length_cons] at hlen
      cases remaining with
      | zero => omega
      | succ remaining =>
          have ht : bits.length ≤ remaining := by omega
          have hs : TM2.step paddingProgram
              (paddingCfg .scan default
                (.bit bit :: bits.map SparseSymbol.bit ++ rest)
                width (unaryMarkers (remaining + 1)) [] output) =
              some (paddingCfg .scan default
                (bits.map SparseSymbol.bit ++ rest) width
                (unaryMarkers remaining) [] (.bit bit :: output)) := by
            simp [unaryMarkers, List.replicate_succ, paddingProgram,
              paddingCfg, paddingStacks, TM2.step, Function.update]
            constructor
            · rfl
            · funext k
              cases k <;> rfl
          have hs' : ((fun o => o.bind (TM2.step paddingProgram))^[1])
              (some (paddingCfg .scan default
                (.bit bit :: bits.map SparseSymbol.bit ++ rest)
                width (unaryMarkers (remaining + 1)) [] output)) =
              some (paddingCfg .scan default
                (bits.map SparseSymbol.bit ++ rest) width
                (unaryMarkers remaining) [] (.bit bit :: output)) := by simpa using hs
          have hr := ih remaining ht (.bit bit :: output)
          have h := chain_iterations _ hs' hr
          rw [List.length_cons,
            show bits.length + 1 = 1 + bits.length by omega]
          rw [show remaining + 1 - (1 + bits.length) =
            remaining - bits.length by omega]
          simpa [List.reverse_cons, List.append_assoc] using h

theorem padding_scan_bits (bits : List Bool) (rest : List SparseSymbol)
    (w : Nat) (hlen : bits.length ≤ w) (output : List SparseSymbol) :
    ((fun o => o.bind (TM2.step paddingProgram))^[bits.length])
      (some (paddingCfg .scan default
        (bits.map SparseSymbol.bit ++ rest) (unaryMarkers w)
        (unaryMarkers w) [] output)) =
    some (paddingCfg .scan default rest (unaryMarkers w)
      (unaryMarkers (w - bits.length)) []
      (bits.reverse.map SparseSymbol.bit ++ output)) :=
  padding_scan_bits_from bits rest (unaryMarkers w) w hlen output

theorem padding_pad (remaining : Nat) (more : Bool)
    (raw width output : List SparseSymbol) :
    ((fun o => o.bind (TM2.step paddingProgram))^[remaining + 1])
      (some (paddingCfg .pad ⟨none, more⟩ raw width
        (unaryMarkers remaining) [] output)) =
    some (paddingCfg .finish ⟨none, more⟩ raw width [] []
      (List.replicate remaining (.bit false) ++ output)) := by
  induction remaining generalizing output with
  | zero => simp [unaryMarkers, paddingProgram, paddingCfg, paddingStacks,
      TM2.step]
  | succ remaining ih =>
      have hs : TM2.step paddingProgram
          (paddingCfg .pad ⟨none, more⟩ raw width
            (unaryMarkers (remaining + 1)) [] output) =
          some (paddingCfg .pad ⟨none, more⟩ raw width
            (unaryMarkers remaining) [] (.bit false :: output)) := by
        simp [unaryMarkers, List.replicate_succ, paddingProgram, paddingCfg,
          paddingStacks, TM2.step, Function.update]
        funext k
        cases k <;> rfl
      have hs' : ((fun o => o.bind (TM2.step paddingProgram))^[1])
          (some (paddingCfg .pad ⟨none, more⟩ raw width
            (unaryMarkers (remaining + 1)) [] output)) =
          some (paddingCfg .pad ⟨none, more⟩ raw width
            (unaryMarkers remaining) [] (.bit false :: output)) := by
        simpa using hs
      have h := chain_iterations _ hs' (ih (.bit false :: output))
      rw [show remaining + 1 + 1 = 1 + (remaining + 1) by omega]
      rw [show List.replicate remaining (.bit false) ++ .bit false :: output =
          List.replicate (remaining + 1) (.bit false) ++ output by
        simp [List.replicate_add, List.append_assoc]] at h
      exact h

theorem padding_boundary_more (raw width counter output : List SparseSymbol) :
    TM2.step paddingProgram
      (paddingCfg .scan default (.wordEnd :: raw) width counter [] output) =
    some (paddingCfg .pad ⟨none, true⟩ raw width counter [] output) := by
  simp [paddingProgram, paddingCfg, paddingStacks, TM2.step, Function.update]
  funext k
  cases k <;> rfl

theorem padding_boundary_end (width counter output : List SparseSymbol) :
    TM2.step paddingProgram
      (paddingCfg .scan default [] width counter [] output) =
    some (paddingCfg .pad ⟨none, false⟩ [] width counter [] output) := by
  simp [paddingProgram, paddingCfg, paddingStacks, TM2.step]

theorem padding_finish_more (raw width output : List SparseSymbol) :
    TM2.step paddingProgram
      (paddingCfg .finish ⟨none, true⟩ raw width [] [] output) =
    some (paddingCfg .copy default raw width [] [] (.wordEnd :: output)) := by
  simp [paddingProgram, paddingCfg, paddingStacks, TM2.step, Function.update]
  funext k
  cases k <;> rfl

theorem padding_finish_end (width output : List SparseSymbol) :
    TM2.step paddingProgram
      (paddingCfg .finish ⟨none, false⟩ [] width [] [] output) =
    some (paddingCfg .done default [] width [] [] (.wordEnd :: output)) := by
  simp [paddingProgram, paddingCfg, paddingStacks, TM2.step, Function.update]
  funext k
  cases k <;> rfl

theorem padding_word_more (w : Nat) (bits : List Bool)
    (hlen : bits.length ≤ w) (rest output : List SparseSymbol) :
    ((fun o => o.bind (TM2.step paddingProgram))^[3 * w + 5])
      (some (paddingCfg .copy default
        (bits.map SparseSymbol.bit ++ .wordEnd :: rest)
        (unaryMarkers w) [] [] output)) =
    some (paddingCfg .copy default rest (unaryMarkers w) [] []
      (.wordEnd :: List.replicate (w - bits.length) (.bit false) ++
        bits.reverse.map SparseSymbol.bit ++ output)) := by
  have hc := padding_copy_width w default
    (bits.map SparseSymbol.bit ++ .wordEnd :: rest) output
  have hs := padding_scan_bits bits (.wordEnd :: rest) w hlen output
  have hb :
      ((fun o => o.bind (TM2.step paddingProgram))^[1])
        (some (paddingCfg .scan default (.wordEnd :: rest) (unaryMarkers w)
          (unaryMarkers (w - bits.length)) []
          (bits.reverse.map SparseSymbol.bit ++ output))) =
      some (paddingCfg .pad ⟨none, true⟩ rest (unaryMarkers w)
        (unaryMarkers (w - bits.length)) []
        (bits.reverse.map SparseSymbol.bit ++ output)) := by
    simpa using padding_boundary_more rest (unaryMarkers w)
      (unaryMarkers (w - bits.length))
      (bits.reverse.map SparseSymbol.bit ++ output)
  have hp := padding_pad (w - bits.length) true rest (unaryMarkers w)
    (bits.reverse.map SparseSymbol.bit ++ output)
  have hf :
      ((fun o => o.bind (TM2.step paddingProgram))^[1])
        (some (paddingCfg .finish ⟨none, true⟩ rest (unaryMarkers w)
          [] [] (List.replicate (w - bits.length) (.bit false) ++
            (bits.reverse.map SparseSymbol.bit ++ output)))) =
      some (paddingCfg .copy default rest (unaryMarkers w) [] []
        (.wordEnd :: (List.replicate (w - bits.length) (.bit false) ++
          (bits.reverse.map SparseSymbol.bit ++ output)))) := by
    simpa using padding_finish_more rest (unaryMarkers w)
      (List.replicate (w - bits.length) (.bit false) ++
        (bits.reverse.map SparseSymbol.bit ++ output))
  have h := chain_iterations _ (chain_iterations _
    (chain_iterations _ (chain_iterations _ hc hs) hb) hp) hf
  have htime : 3 * w + 5 =
      (2 * w + 2) + bits.length + 1 + (w - bits.length + 1) + 1 := by omega
  rw [htime]
  simpa [List.append_assoc] using h

theorem padding_word_end (w : Nat) (bits : List Bool)
    (hlen : bits.length ≤ w) (output : List SparseSymbol) :
    ((fun o => o.bind (TM2.step paddingProgram))^[3 * w + 5])
      (some (paddingCfg .copy default (bits.map SparseSymbol.bit)
        (unaryMarkers w) [] [] output)) =
    some (paddingCfg .done default [] (unaryMarkers w) [] []
      (.wordEnd :: List.replicate (w - bits.length) (.bit false) ++
        bits.reverse.map SparseSymbol.bit ++ output)) := by
  have hc := padding_copy_width w default (bits.map SparseSymbol.bit) output
  have hs := padding_scan_bits bits [] w hlen output
  simp only [List.append_nil] at hs
  have hb :
      ((fun o => o.bind (TM2.step paddingProgram))^[1])
        (some (paddingCfg .scan default [] (unaryMarkers w)
          (unaryMarkers (w - bits.length)) []
          (bits.reverse.map SparseSymbol.bit ++ output))) =
      some (paddingCfg .pad ⟨none, false⟩ [] (unaryMarkers w)
        (unaryMarkers (w - bits.length)) []
        (bits.reverse.map SparseSymbol.bit ++ output)) := by
    simpa using padding_boundary_end (unaryMarkers w)
      (unaryMarkers (w - bits.length))
      (bits.reverse.map SparseSymbol.bit ++ output)
  have hp := padding_pad (w - bits.length) false [] (unaryMarkers w)
    (bits.reverse.map SparseSymbol.bit ++ output)
  have hf :
      ((fun o => o.bind (TM2.step paddingProgram))^[1])
        (some (paddingCfg .finish ⟨none, false⟩ [] (unaryMarkers w)
          [] [] (List.replicate (w - bits.length) (.bit false) ++
            (bits.reverse.map SparseSymbol.bit ++ output)))) =
      some (paddingCfg .done default [] (unaryMarkers w) [] []
        (.wordEnd :: (List.replicate (w - bits.length) (.bit false) ++
          (bits.reverse.map SparseSymbol.bit ++ output)))) := by
    simpa using padding_finish_end (unaryMarkers w)
      (List.replicate (w - bits.length) (.bit false) ++
        (bits.reverse.map SparseSymbol.bit ++ output))
  have h := chain_iterations _ (chain_iterations _
    (chain_iterations _ (chain_iterations _ hc hs) hb) hp) hf
  have htime : 3 * w + 5 =
      (2 * w + 2) + bits.length + 1 + (w - bits.length + 1) + 1 := by omega
  rw [htime]
  simpa [List.append_assoc] using h

def canonicalPaddingRaw : List Nat → List SparseSymbol
  | [] => []
  | n :: ns => .wordEnd :: n.bits.map SparseSymbol.bit ++ canonicalPaddingRaw ns

theorem canonicalPaddingRaw_eq (x : List Nat) :
    canonicalPaddingRaw x = (encode x).map sparseOfInputSymbol := by
  induction x with
  | nil => rfl
  | cons n x ih =>
      simp [canonicalPaddingRaw, encode, encodeNat, sparseOfInputSymbol, ih,
        List.map_append, List.map_map, Function.comp_def]

theorem padding_words_run (w : Nat) (x : List Nat)
    (hfit : ∀ n ∈ x, n < 2 ^ w) (output : List SparseSymbol) :
    ((fun o => o.bind (TM2.step paddingProgram))^[x.length * (3 * w + 5)])
      (some (paddingCfg .copy default
        (match x with
          | [] => []
          | _ :: _ => (canonicalPaddingRaw x).tail)
        (unaryMarkers w) [] [] output)) =
    some (paddingCfg (if x = [] then .copy else .done) default []
      (unaryMarkers w) [] [] ((encodeWordList w x).reverse ++ output)) := by
  induction x generalizing output with
  | nil => simp [canonicalPaddingRaw, encodeWordList]
  | cons n x ih =>
      have hn := hfit n (by simp)
      have hlen : n.bits.length ≤ w := by
        have hlt : n.bits.length ≤ w := by
          rw [Nat.size_eq_bits_len]
          exact (Nat.size_le.mpr hn)
        exact hlt
      cases x with
      | nil =>
          simpa [canonicalPaddingRaw, encodeWordList, encodeFixedWord,
            fixedBits_eq_bits_append_replicate hn, List.reverse_append,
            List.map_append, List.map_reverse, List.append_assoc] using
            padding_word_end w n.bits hlen output
      | cons m x =>
          have hfirst := padding_word_more w n.bits hlen
            (m.bits.map SparseSymbol.bit ++ canonicalPaddingRaw x) output
          have hout :
              ((.wordEnd :: List.replicate (w - n.bits.length) (.bit false)) ++
                n.bits.reverse.map SparseSymbol.bit) ++ output =
              (encodeFixedWord w n).reverse ++ output := by
            simp [encodeFixedWord, fixedBits_eq_bits_append_replicate hn,
              List.reverse_append, List.map_append, List.map_reverse,
              List.append_assoc]
          rw [hout] at hfirst
          have htail := ih (fun a ha => hfit a (by simp [ha]))
            ((encodeFixedWord w n).reverse ++ output)
          simp [canonicalPaddingRaw] at htail
          have h := chain_iterations _ hfirst htail
          rw [show (3 * w + 5) +
              (x.length + 1) * (3 * w + 5) =
              (x.length + 2) * (3 * w + 5) by ring] at h
          simpa [canonicalPaddingRaw, encodeWordList, encodeFixedWord,
            fixedBits_eq_bits_append_replicate hn, List.reverse_append,
            List.map_append, List.map_reverse, List.append_assoc, Nat.add_mul,
            Nat.add_assoc, two_mul]
            using h

theorem padding_all (w : Nat) (x : List Nat)
    (hfit : ∀ n ∈ x, n < 2 ^ w) :
    ((fun o => o.bind (TM2.step paddingProgram))^[1 + x.length * (3 * w + 5)])
      (some (paddingCfg .start default (canonicalPaddingRaw x)
        (unaryMarkers w) [] [] [])) =
    some (paddingCfg .done default [] (unaryMarkers w) [] []
      (encodeWordList w x).reverse) := by
  cases x with
  | nil =>
      simp [canonicalPaddingRaw, paddingProgram, paddingCfg, paddingStacks,
        TM2.step, encodeWordList]
  | cons n x =>
      have hstart :
          TM2.step paddingProgram
            (paddingCfg .start default (canonicalPaddingRaw (n :: x))
              (unaryMarkers w) [] [] []) =
          some (paddingCfg .copy default
            (n.bits.map SparseSymbol.bit ++ canonicalPaddingRaw x)
            (unaryMarkers w) [] [] []) := by
        simp [canonicalPaddingRaw, paddingProgram, paddingCfg, paddingStacks,
          TM2.step, Function.update]
        funext k
        cases k <;> rfl
      have hwords := padding_words_run w (n :: x) hfit []
      have hstart' : ((fun o => o.bind (TM2.step paddingProgram))^[1])
          (some (paddingCfg .start default (canonicalPaddingRaw (n :: x))
            (unaryMarkers w) [] [] [])) =
          some (paddingCfg .copy default
            (n.bits.map SparseSymbol.bit ++ canonicalPaddingRaw x)
            (unaryMarkers w) [] [] []) := by simpa using hstart
      simp [canonicalPaddingRaw] at hwords
      exact chain_iterations _ hstart' hwords

def physicalPaddingRaw (w : Nat) (x : List Nat) : List SparseSymbol :=
  .wordEnd :: (fixedBits w x.length).map SparseSymbol.bit ++
    canonicalPaddingRaw x

theorem padding_physical_input (w : Nat) (x : List Nat)
    (hlen : x.length < 2 ^ w) (hfit : ∀ n ∈ x, n < 2 ^ w) :
    ((fun o => o.bind (TM2.step paddingProgram))^[
        1 + (x.length + 1) * (3 * w + 5)])
      (some (paddingCfg .start default (physicalPaddingRaw w x)
        (unaryMarkers w) [] [] [])) =
    some (paddingCfg .done default [] (unaryMarkers w) [] []
      (encodeWordList w (x.length :: x)).reverse) := by
  have hstart :
      TM2.step paddingProgram
        (paddingCfg .start default (physicalPaddingRaw w x)
          (unaryMarkers w) [] [] []) =
      some (paddingCfg .copy default
        ((fixedBits w x.length).map SparseSymbol.bit ++ canonicalPaddingRaw x)
        (unaryMarkers w) [] [] []) := by
    simp [physicalPaddingRaw, paddingProgram, paddingCfg, paddingStacks,
      TM2.step, Function.update]
    funext k
    cases k <;> rfl
  have hstart' : ((fun o => o.bind (TM2.step paddingProgram))^[1])
      (some (paddingCfg .start default (physicalPaddingRaw w x)
        (unaryMarkers w) [] [] [])) =
      some (paddingCfg .copy default
        ((fixedBits w x.length).map SparseSymbol.bit ++ canonicalPaddingRaw x)
        (unaryMarkers w) [] [] []) := by simpa using hstart
  cases x with
  | nil =>
      have hword := padding_word_end w (fixedBits w 0) (by simp) []
      have hstartNil :
          ((fun o => o.bind (TM2.step paddingProgram))^[1])
            (some (paddingCfg .start default (physicalPaddingRaw w [])
              (unaryMarkers w) [] [] [])) =
          some (paddingCfg .copy default
            ((fixedBits w 0).map SparseSymbol.bit)
            (unaryMarkers w) [] [] []) := by
        simpa [canonicalPaddingRaw] using hstart'
      have h := chain_iterations _ hstartNil hword
      simpa [encodeWordList, encodeFixedWord, physicalPaddingRaw] using h
  | cons n x =>
      have hfirst := padding_word_more w (fixedBits w (n :: x).length)
        (by simp) (n.bits.map SparseSymbol.bit ++ canonicalPaddingRaw x) []
      have hout :
          ((.wordEnd ::
              List.replicate (w - (fixedBits w (n :: x).length).length)
                (.bit false)) ++
              (fixedBits w (n :: x).length).reverse.map SparseSymbol.bit) ++ [] =
            (encodeFixedWord w (n :: x).length).reverse := by
        simp [encodeFixedWord, List.reverse_append, List.map_reverse]
      rw [hout] at hfirst
      have htail := padding_words_run w (n :: x) hfit
        ((encodeFixedWord w (n :: x).length).reverse)
      simp [canonicalPaddingRaw] at htail
      have hwords := chain_iterations _ hfirst htail
      have h := chain_iterations _ hstart' hwords
      rw [show 1 + ((3 * w + 5) +
          (x.length + 1) * (3 * w + 5)) =
          1 + (x.length + 2) * (3 * w + 5) by ring] at h
      simpa [encodeWordList, encodeFixedWord, physicalPaddingRaw,
        canonicalPaddingRaw, List.reverse_append, List.append_assoc,
        Nat.add_mul, Nat.add_assoc, two_mul] using h

end Lax20Proofs.RamToTM
