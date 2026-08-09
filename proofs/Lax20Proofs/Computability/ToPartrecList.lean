import Mathlib.Computability.TuringMachine.ToPartrec

namespace Lax20Proofs.Computability

open Turing ToPartrec Encodable

@[simp] theorem encode_nat_list_nil : encode ([] : List ℕ) = 0 := rfl

@[simp] theorem encode_nat_list_cons (a : ℕ) (xs : List ℕ) :
    encode (a :: xs) = (Nat.pair a (encode xs)).succ := rfl

private def pairVector (v : List.Vector ℕ 2) : ℕ :=
  Nat.pair v.head v.tail.head

private theorem pairVector_primrec : Primrec pairVector := by
  exact Primrec₂.natPair.comp Primrec.vector_head
    (Primrec.vector_head.comp Primrec.vector_tail)

private theorem pairVector_partrec' : Nat.Partrec' (fun v => (pairVector v : Part ℕ)) :=
  Nat.Partrec'.of_prim pairVector_primrec

noncomputable def listPairCode : Code :=
  Classical.choose (Code.exists_code pairVector_partrec')

theorem listPairCode_eval (a b : ℕ) :
    listPairCode.eval [a, b] = pure [Nat.pair a b] := by
  have h := Classical.choose_spec (Code.exists_code pairVector_partrec')
    (⟨[a, b], by simp⟩ : List.Vector ℕ 2)
  simpa [listPairCode, pairVector] using h

private def unpairLeftVector (v : List.Vector ℕ 1) : ℕ :=
  (Nat.unpair v.head).1

private theorem unpairLeftVector_primrec : Primrec unpairLeftVector := by
  exact Primrec.fst.comp (Primrec.unpair.comp Primrec.vector_head)

private theorem unpairLeftVector_partrec' :
    Nat.Partrec' (fun v => (unpairLeftVector v : Part ℕ)) :=
  Nat.Partrec'.of_prim unpairLeftVector_primrec

noncomputable def listUnpairLeftCode : Code :=
  Classical.choose (Code.exists_code unpairLeftVector_partrec')

theorem listUnpairLeftCode_eval (n : ℕ) :
    listUnpairLeftCode.eval [n] = pure [(Nat.unpair n).1] := by
  have h := Classical.choose_spec (Code.exists_code unpairLeftVector_partrec')
    (⟨[n], by simp⟩ : List.Vector ℕ 1)
  simpa [listUnpairLeftCode, unpairLeftVector] using h

private def unpairRightVector (v : List.Vector ℕ 1) : ℕ :=
  (Nat.unpair v.head).2

private theorem unpairRightVector_primrec : Primrec unpairRightVector := by
  exact Primrec.snd.comp (Primrec.unpair.comp Primrec.vector_head)

private theorem unpairRightVector_partrec' :
    Nat.Partrec' (fun v => (unpairRightVector v : Part ℕ)) :=
  Nat.Partrec'.of_prim unpairRightVector_primrec

noncomputable def listUnpairRightCode : Code :=
  Classical.choose (Code.exists_code unpairRightVector_partrec')

theorem listUnpairRightCode_eval (n : ℕ) :
    listUnpairRightCode.eval [n] = pure [(Nat.unpair n).2] := by
  have h := Classical.choose_spec (Code.exists_code unpairRightVector_partrec')
    (⟨[n], by simp⟩ : List.Vector ℕ 1)
  simpa [listUnpairRightCode, unpairRightVector] using h

private def codeOne : Code := .comp .succ .zero

private def codeAtOne : Code := .comp .head .tail

private def codeAtTwo : Code := .comp .head (.comp .tail .tail)

private def codeTailThree : Code := .comp .tail (.comp .tail .tail)

/-- On `[n, acc, a, ...]`, compute `[Nat.pair a acc + 1]`. -/
private noncomputable def codeConsAccumulator : Code :=
  .comp .succ <| .comp listPairCode <|
    .cons codeAtTwo (.cons codeAtOne .nil)

/-- One body step for the length-controlled list encoder. -/
private noncomputable def encodeListBody : Code :=
  .case
    (.cons .zero (.cons .head .nil))
    (.cons codeOne <|
      .cons .head <|
        .cons codeConsAccumulator codeTailThree)

/-- Prepare `[n, x...]` as encoder state `[n, 0, x...]`. -/
private def encodeListInit : Code :=
  .cons .head (.cons .zero .tail)

/-- Encode the `n` following entries of `[n, x...]`, processing them from
left to right.  Consequently the result is the `Primcodable` encoding of
`x.reverse`. -/
noncomputable def encodeReversedListCode : Code :=
  .comp (.fix encodeListBody) encodeListInit

@[simp] theorem encodeListInit_eval (n : ℕ) (xs : List ℕ) :
    encodeListInit.eval (n :: xs) = pure (n :: 0 :: xs) := by
  simp [encodeListInit, Code.eval]

@[simp] theorem encodeListBody_zero_eval (acc : ℕ) (xs : List ℕ) :
    encodeListBody.eval (0 :: acc :: xs) = pure [0, acc] := by
  simp [encodeListBody, Code.eval]

@[simp] theorem encodeListBody_succ_eval (n acc a : ℕ) (xs : List ℕ) :
    encodeListBody.eval (n.succ :: acc :: a :: xs) =
      pure (1 :: n :: (Nat.pair a acc).succ :: xs) := by
  simp [encodeListBody, codeOne, codeConsAccumulator, codeAtOne,
    codeAtTwo, codeTailThree, Code.eval, listPairCode_eval]

private def consCode (a acc : ℕ) : ℕ := (Nat.pair a acc).succ

private theorem encodeListLoop_mem (xs : List ℕ) (acc : ℕ) :
    [xs.foldl (fun acc a => consCode a acc) acc] ∈
      PFun.fix (fun v => (encodeListBody.eval v).map fun v =>
        if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail)
        (xs.length :: acc :: xs) := by
  induction xs generalizing acc with
  | nil =>
      refine PFun.mem_fix_iff.2 (Or.inl ?_)
      simp [encodeListBody_zero_eval]
  | cons a xs ih =>
      refine PFun.mem_fix_iff.2 (Or.inr
        ⟨xs.length :: consCode a acc :: xs, ?_, ?_⟩)
      · simp [encodeListBody_succ_eval, consCode]
      · simpa [consCode] using ih (consCode a acc)

private theorem foldl_consCode_eq_encode (xs ys : List ℕ) :
    xs.foldl (fun acc a => consCode a acc) (encode ys) =
      encode (xs.reverse ++ ys) := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
      change xs.foldl (fun acc a => consCode a acc)
        (consCode a (encode ys)) = _
      rw [show consCode a (encode ys) = encode (a :: ys) by rfl]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem encodeReversedListCode_eval (xs : List ℕ) :
    encodeReversedListCode.eval (xs.length :: xs) =
      pure [encode xs.reverse] := by
  rw [encodeReversedListCode, Code.comp_eval]
  change encodeListInit.eval (xs.length :: xs) >>= _ = _
  rw [encodeListInit_eval]
  change (Part.some (xs.length :: 0 :: xs) >>= _) = _
  rw [Part.bind_eq_bind, Part.bind_some, Code.fix_eval]
  apply Part.eq_some_iff.2
  have h := encodeListLoop_mem xs 0
  rw [show 0 = encode ([] : List ℕ) by rfl,
    foldl_consCode_eq_encode] at h
  simpa using h

private noncomputable def codeUnpairLeftHead : Code :=
  .comp listUnpairLeftCode (.cons .head .nil)

private noncomputable def codeUnpairRightHead : Code :=
  .comp listUnpairRightCode (.cons .head .nil)

/-- One body step for decoding a natural list code into a reversed list. -/
private noncomputable def decodeListBody : Code :=
  .case .zero' <|
    .cons codeOne <|
      .cons codeUnpairRightHead <|
        .cons codeUnpairLeftHead .tail

/-- Decode the head natural as a `Primcodable` list, returning that list in
reverse order. -/
noncomputable def decodeReversedListCode : Code :=
  .fix decodeListBody

@[simp] theorem decodeListBody_zero_eval (acc : List ℕ) :
    decodeListBody.eval (0 :: acc) = pure (0 :: acc) := by
  simp [decodeListBody, Code.eval]

@[simp] theorem decodeListBody_succ_eval (a rest : ℕ) (acc : List ℕ) :
    decodeListBody.eval ((Nat.pair a rest).succ :: acc) =
      pure (1 :: rest :: a :: acc) := by
  simp [decodeListBody, codeOne, codeUnpairLeftHead,
    codeUnpairRightHead, Code.eval, listUnpairLeftCode_eval,
    listUnpairRightCode_eval]

private theorem decodeListLoop_mem (xs acc : List ℕ) :
    xs.reverse ++ acc ∈
      PFun.fix (fun v => (decodeListBody.eval v).map fun v =>
        if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail)
        (encode xs :: acc) := by
  induction xs generalizing acc with
  | nil =>
      refine PFun.mem_fix_iff.2 (Or.inl ?_)
      simp [decodeListBody_zero_eval]
  | cons a xs ih =>
      refine PFun.mem_fix_iff.2 (Or.inr ⟨encode xs :: a :: acc, ?_, ?_⟩)
      · simp [decodeListBody_succ_eval]
      · simpa [List.reverse_cons, List.append_assoc] using ih (a :: acc)

theorem decodeReversedListCode_eval (xs : List ℕ) :
    decodeReversedListCode.eval [encode xs] = pure xs.reverse := by
  rw [decodeReversedListCode, Code.fix_eval]
  apply Part.eq_some_iff.2
  simpa using decodeListLoop_mem xs []

/-- Conjugate a list function by `Primcodable` encoding.  The reversals match
the two tail-recursive adapters above. -/
private def listConjugate (f : List ℕ → List ℕ) (n : ℕ) : ℕ :=
  encode ((f ((decode (α := List ℕ) n).getD []).reverse).reverse)

private theorem listConjugate_computable (f : List ℕ → List ℕ)
    (hf : Computable f) : Computable (listConjugate f) := by
  have hdecode : Computable fun n : ℕ => decode (α := List ℕ) n :=
    Computable.decode
  have hlist : Computable fun n : ℕ => (decode (α := List ℕ) n).getD [] :=
    Computable.option_getD hdecode (Computable.const [])
  have hinput : Computable fun n : ℕ =>
      ((decode (α := List ℕ) n).getD []).reverse :=
    Computable.list_reverse.comp hlist
  have hout : Computable fun n : ℕ =>
      (f ((decode (α := List ℕ) n).getD []).reverse).reverse :=
    Computable.list_reverse.comp (hf.comp hinput)
  exact Computable.encode.comp hout

private theorem listConjugate_partrec' (f : List ℕ → List ℕ)
    (hf : Computable f) :
    Nat.Partrec' (fun v : List.Vector ℕ 1 =>
      (listConjugate f v.head : Part ℕ)) := by
  have hg : Partrec (fun n : ℕ => (listConjugate f n : Part ℕ)) :=
    listConjugate_computable f hf
  exact (Nat.Partrec'.part_iff₁
    (f := fun n : ℕ => (listConjugate f n : Part ℕ))).2 hg

noncomputable def listConjugateCode (f : List ℕ → List ℕ)
    (hf : Computable f) : Code :=
  Classical.choose (Code.exists_code (listConjugate_partrec' f hf))

theorem listConjugateCode_eval (f : List ℕ → List ℕ) (hf : Computable f)
    (xs : List ℕ) :
    (listConjugateCode f hf).eval [encode xs] =
      pure [encode ((f xs.reverse).reverse)] := by
  have h := Classical.choose_spec
    (Code.exists_code (listConjugate_partrec' f hf))
    (⟨[encode xs], by simp⟩ : List.Vector ℕ 1)
  have h' : (listConjugateCode f hf).eval [encode xs] =
      pure [listConjugate f (encode xs)] := by
    simpa [listConjugateCode] using h
  rw [h', listConjugate]
  simp

/-- A `ToPartrec.Code` computing an arbitrary computable list function from
the length-prefixed semantic input `xs.length :: xs`. -/
noncomputable def computableListCode (f : List ℕ → List ℕ)
    (hf : Computable f) : Code :=
  .comp decodeReversedListCode <|
    .comp (listConjugateCode f hf) encodeReversedListCode

theorem computableListCode_eval (f : List ℕ → List ℕ) (hf : Computable f)
    (xs : List ℕ) :
    (computableListCode f hf).eval (xs.length :: xs) = pure (f xs) := by
  simp [computableListCode, Code.eval, encodeReversedListCode_eval,
    listConjugateCode_eval, decodeReversedListCode_eval]

end Lax20Proofs.Computability
