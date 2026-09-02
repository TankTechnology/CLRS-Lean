import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B1_Steps

/-!
# Dev B2: the `reduce` dispatch and list assembly

The `reduce` label dispatch (pop a continuation frame and route to the matching emitter) and the reversed encodings of literals, clauses, and CNF lists.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

-- ============================================================
-- reduce dispatch: pop a continuation frame and route to the emitter
--
-- The `reduce` label pops the top frame of `frm` and dispatches to the
-- matching emission phase (or pushes the `₂` frame for a binary operator's
-- second child and returns to `rd`).  The pre-state is irrelevant: the pop
-- overwrites it.
-- ============================================================

/-- `reduce` with an empty `frm` stack (the root) routes to `emitTrue`. -/
lemma reduce_top_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.reduce, v, stk inp T c V [] S O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitTrue, St.emitTrue, stk inp T c V [] S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `reduce` with a `Frame.not` on top routes to `emitNot`. -/
lemma reduce_not_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.reduce, v, stk inp T c V (Frame.not :: F) S O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitNot, St.emitNot, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `reduce` with an `and₁` frame routes back to `rd` (with the second child's
`and₂` frame pushed). -/
lemma reduce_and₁_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.reduce, v, stk inp T c V (Frame.and₁ :: F) S O U⟩ : (mach).Cfg)
      = some (⟨some Label.rd, St.and₁Done, stk inp T c V (Frame.and₂ :: F) S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `reduce` with an `and₂` frame routes to `emitAnd`. -/
lemma reduce_and₂_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.reduce, v, stk inp T c V (Frame.and₂ :: F) S O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitAnd, St.emitAnd, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `reduce` with an `or₁` frame routes back to `rd` (with the second child's
`or₂` frame pushed). -/
lemma reduce_or₁_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.reduce, v, stk inp T c V (Frame.or₁ :: F) S O U⟩ : (mach).Cfg)
      = some (⟨some Label.rd, St.or₁Done, stk inp T c V (Frame.or₂ :: F) S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `reduce` with an `or₂` frame routes to `emitOr`. -/
lemma reduce_or₂_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.reduce, v, stk inp T c V (Frame.or₂ :: F) S O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitOr, St.emitOr, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `reduce` with an `iff₁` frame routes back to `rd` (with the second child's
`iff₂` frame pushed). -/
lemma reduce_iff₁_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.reduce, v, stk inp T c V (Frame.iff₁ :: F) S O U⟩ : (mach).Cfg)
      = some (⟨some Label.rd, St.iff₁Done, stk inp T c V (Frame.iff₂ :: F) S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `reduce` with an `iff₂` frame routes to `emitIff`. -/
lemma reduce_iff₂_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.reduce, v, stk inp T c V (Frame.iff₂ :: F) S O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitIff, St.emitIff, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

-- ============================================================
-- List assembly: reversed encodings of literals/clauses/CNF
--
-- The machine pushes output symbols onto `o` so that after emitting a
-- sequence of clauses the stack holds the *reversed* encoding of the CNF
-- (`copyOut` then transfers `o` to `out`, reversing it back).  These lemmas
-- express the assembled stacks in terms of `encLit`/`encClause`/`encCNF`.
-- ============================================================

/-- The reversed encoding of a literal is its unary index run followed by the
`varMark` and polarity marks. -/
lemma encLit_reverse (l : Literal) :
    (encLit l).reverse = List.replicate (litIndex l + 1) CNFSym.endMark ++
      [CNFSym.varMark, litSym l] := by
  cases l <;> simp [encLit, litSym, litIndex, List.reverse_cons, List.reverse_append,
    List.reverse_replicate]

/-- The reversed encoding of a two-literal clause splits at the `clauseMark`. -/
lemma encClause_two_reverse (l₁ l₂ : Literal) :
    (encClause [l₁, l₂]).reverse =
      (encLit l₂).reverse ++ (encLit l₁).reverse ++ [CNFSym.clauseMark] := by
  simp [encClause, List.flatMap, List.reverse_cons, List.reverse_append]

/-- The reversed encoding of the negated two-literal clause `[¬y, ¬y₁]`. -/
lemma encClause_neg_reverse (y y₁ : Nat) :
    (encClause [Literal.neg y, Literal.neg y₁]).reverse =
      List.replicate (y₁ + 1) CNFSym.endMark ++ [CNFSym.varMark, CNFSym.negMark] ++
      List.replicate (y + 1) CNFSym.endMark ++
        [CNFSym.varMark, CNFSym.negMark, CNFSym.clauseMark] := by
  rw [encClause_two_reverse]
  simp [encLit_reverse, encLit, litSym, litIndex]

/-- The reversed encoding of the positive two-literal clause `[y, y₁]`. -/
lemma encClause_pos_reverse (y y₁ : Nat) :
    (encClause [Literal.pos y, Literal.pos y₁]).reverse =
      List.replicate (y₁ + 1) CNFSym.endMark ++ [CNFSym.varMark, CNFSym.posMark] ++
      List.replicate (y + 1) CNFSym.endMark ++
        [CNFSym.varMark, CNFSym.posMark, CNFSym.clauseMark] := by
  rw [encClause_two_reverse]
  simp [encLit_reverse, encLit, litSym, litIndex]

/-- The reversed encoding of `notClauses y y₁` emits the two clauses in the
same order the machine pushes them (later clause first on the stack). -/
lemma encCNF_notClauses_reverse (y y₁ : Nat) :
    (encCNF (notClauses y y₁)).reverse =
      (encClause [Literal.pos y, Literal.pos y₁]).reverse ++
      (encClause [Literal.neg y, Literal.neg y₁]).reverse := by
  simp [encCNF, notClauses, List.reverse_append]

/-- The reversed encoding of a three-literal clause splits at the `clauseMark`. -/
lemma encClause_three_reverse (l₁ l₂ l₃ : Literal) :
    (encClause [l₁, l₂, l₃]).reverse =
      (encLit l₃).reverse ++ (encLit l₂).reverse ++ (encLit l₁).reverse ++
        [CNFSym.clauseMark] := by
  simp [encClause, List.flatMap, List.reverse_cons, List.reverse_append]

/-- The reversed encoding of `andClauses y y₁ y₂` emits the three clauses in
reverse output order (clause 3 `[¬y₁, ¬y₂, y]` first, then `[¬y, y₂]`, then
`[¬y, y₁]`). -/
lemma encCNF_andClauses_reverse (y y₁ y₂ : Nat) :
    (encCNF (andClauses y y₁ y₂)).reverse =
      (encClause [Literal.neg y₁, Literal.neg y₂, Literal.pos y]).reverse ++
      (encClause [Literal.neg y, Literal.pos y₂]).reverse ++
      (encClause [Literal.neg y, Literal.pos y₁]).reverse := by
  simp [encCNF, andClauses, List.reverse_append]

/-- The reversed encoding of `orClauses y y₁ y₂` emits the three clauses in
reverse output order (clause 3 `[y₁, y₂, ¬y]` first, then `[y, ¬y₂]`, then
`[y, ¬y₁]`). -/
lemma encCNF_orClauses_reverse (y y₁ y₂ : Nat) :
    (encCNF (orClauses y y₁ y₂)).reverse =
      (encClause [Literal.pos y₁, Literal.pos y₂, Literal.neg y]).reverse ++
      (encClause [Literal.pos y, Literal.neg y₂]).reverse ++
      (encClause [Literal.pos y, Literal.neg y₁]).reverse := by
  simp [encCNF, orClauses, List.reverse_append]

/-- The reversed encoding of `iffClauses y y₁ y₂` emits the four clauses in
reverse output order (clause 4 `[y, ¬y₁, ¬y₂]` first, then `[y, y₁, y₂]`, then
`[¬y, y₁, ¬y₂]`, then `[¬y, ¬y₁, y₂]`). -/
lemma encCNF_iffClauses_reverse (y y₁ y₂ : Nat) :
    (encCNF (iffClauses y y₁ y₂)).reverse =
      (encClause [Literal.pos y, Literal.neg y₁, Literal.neg y₂]).reverse ++
      (encClause [Literal.pos y, Literal.pos y₁, Literal.pos y₂]).reverse ++
      (encClause [Literal.neg y, Literal.pos y₁, Literal.neg y₂]).reverse ++
      (encClause [Literal.neg y, Literal.neg y₁, Literal.pos y₂]).reverse := by
  simp [encCNF, iffClauses, List.reverse_append]


end TM3CNF

end Turing

end Chapter34

end CLRS
