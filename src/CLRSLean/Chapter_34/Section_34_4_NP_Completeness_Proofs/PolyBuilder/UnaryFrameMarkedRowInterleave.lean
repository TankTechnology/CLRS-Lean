import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowDuplicate

/-!
# Type-safe interleaving of marked row families

This file defines the semantic target for a reusable same-input parallel TM2
combinator.  Two equally long `frameEnd`-free row families are interleaved one
row at a time.  Keeping alignment and delimiter safety in the input structure
lets the later machine proof reason only about physical stacks.
-/

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Total alternating row zipper.  It stops when either input is exhausted. -/
def interleaveUnaryFrameMarkedRows :
    List (List UnaryFrameSym) → List (List UnaryFrameSym) →
      List (List UnaryFrameSym)
  | left :: lefts, right :: rights =>
      left :: right :: interleaveUnaryFrameMarkedRows lefts rights
  | _, _ => []

/-- Two delimiter-safe row families with the same number of rows. -/
structure UnaryFrameAlignedMarkedRowPair where
  left : UnaryFrameMarkedRowFamily
  right : UnaryFrameMarkedRowFamily
  rowAligned : left.rows.length = right.rows.length

private theorem mem_interleaveUnaryFrameMarkedRows
    (left right : List (List UnaryFrameSym))
    (row : List UnaryFrameSym)
    (hrow : row ∈ interleaveUnaryFrameMarkedRows left right) :
    row ∈ left ∨ row ∈ right := by
  induction left generalizing right with
  | nil =>
      simp [interleaveUnaryFrameMarkedRows] at hrow
  | cons head tail ih =>
      cases right with
      | nil =>
          simp [interleaveUnaryFrameMarkedRows] at hrow
      | cons other rest =>
          simp only [interleaveUnaryFrameMarkedRows, List.mem_cons] at hrow
          rcases hrow with rfl | rfl | hrow
          · exact Or.inl (by simp)
          · exact Or.inr (by simp)
          · rcases ih rest hrow with hleft | hright
            · exact Or.inl (by simp [hleft])
            · exact Or.inr (by simp [hright])

/-- Interleave the two aligned families as `left₀/right₀/left₁/right₁/...`. -/
def UnaryFrameAlignedMarkedRowPair.interleaved
    (pair : UnaryFrameAlignedMarkedRowPair) : UnaryFrameMarkedRowFamily where
  rows := interleaveUnaryFrameMarkedRows pair.left.rows pair.right.rows
  frameEnd_free := by
    intro row hrow symbol hsymbol
    rcases mem_interleaveUnaryFrameMarkedRows _ _ row hrow with
      hleft | hright
    · exact pair.left.frameEnd_free row hleft symbol hsymbol
    · exact pair.right.frameEnd_free row hright symbol hsymbol

/-- Interleaving doubles the common row count. -/
theorem interleaveUnaryFrameMarkedRows_length_of_aligned
    (left right : List (List UnaryFrameSym))
    (haligned : left.length = right.length) :
    (interleaveUnaryFrameMarkedRows left right).length = 2 * left.length := by
  induction left generalizing right with
  | nil =>
      have hright : right = [] := List.eq_nil_of_length_eq_zero haligned.symm
      subst right
      rfl
  | cons left lefts ih =>
      cases right with
      | nil => simp at haligned
      | cons right rights =>
          simp only [List.length_cons] at haligned
          simp only [interleaveUnaryFrameMarkedRows, List.length_cons]
          rw [ih rights (by omega)]
          omega

@[simp] theorem UnaryFrameAlignedMarkedRowPair.interleaved_length
    (pair : UnaryFrameAlignedMarkedRowPair) :
    pair.interleaved.rows.length = 2 * pair.left.rows.length := by
  exact interleaveUnaryFrameMarkedRows_length_of_aligned _ _ pair.rowAligned

/-- Literal encoder equation used by the future physical output merger. -/
theorem UnaryFrameAlignedMarkedRowPair.encode_interleaved
    (pair : UnaryFrameAlignedMarkedRowPair) :
    encodeUnaryFrameMarkedRowFamily pair.interleaved =
      (interleaveUnaryFrameMarkedRows pair.left.rows
        pair.right.rows).flatMap fun row => row ++ [.frameEnd] := by
  rfl

/-- Interleaving commutes with adding one aligned row pair at the front. -/
theorem encodeUnaryFrameMarkedRowFamily_interleaved_cons
    (left right : List UnaryFrameSym)
    (hleft : ∀ symbol ∈ left, symbol ≠ UnaryFrameSym.frameEnd)
    (hright : ∀ symbol ∈ right, symbol ≠ UnaryFrameSym.frameEnd)
    (pair : UnaryFrameAlignedMarkedRowPair) :
    let next : UnaryFrameAlignedMarkedRowPair :=
      { left :=
          { rows := left :: pair.left.rows
            frameEnd_free := by
              intro row hrow symbol hsymbol
              simp only [List.mem_cons] at hrow
              rcases hrow with rfl | hrow
              · exact hleft symbol hsymbol
              · exact pair.left.frameEnd_free row hrow symbol hsymbol }
        right :=
          { rows := right :: pair.right.rows
            frameEnd_free := by
              intro row hrow symbol hsymbol
              simp only [List.mem_cons] at hrow
              rcases hrow with rfl | hrow
              · exact hright symbol hsymbol
              · exact pair.right.frameEnd_free row hrow symbol hsymbol }
        rowAligned := by simp [pair.rowAligned] }
    encodeUnaryFrameMarkedRowFamily next.interleaved =
      left ++ [.frameEnd] ++ right ++ [.frameEnd] ++
        encodeUnaryFrameMarkedRowFamily pair.interleaved := by
  simp [UnaryFrameAlignedMarkedRowPair.interleaved,
    encodeUnaryFrameMarkedRowFamily, interleaveUnaryFrameMarkedRows,
    List.append_assoc]

end CLRS.Chapter34.Turing.PolyBuilder
