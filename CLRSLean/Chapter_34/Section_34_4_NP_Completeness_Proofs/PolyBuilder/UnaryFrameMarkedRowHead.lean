import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameStatefulMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowDuplicate

/-!
# First payload of a marked unary-row family

This fixed streaming filter keeps the payload of the first `frameEnd`-marked
row and erases its boundary and every later row.  It is useful after the
verified row-order reverser when a dynamically located final accumulator must
be exposed as an ordinary unary frame.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Keep symbols until the first outer row boundary has been consumed. -/
def unaryFrameMarkedRowHeadSpec : UnaryFrameStatefulMapSpec Bool where
  initial := true
  action keep symbol :=
    if keep then
      match symbol with
      | .frameEnd => (none, false)
      | .tick => (some .tick, true)
      | .separator => (some .separator, true)
    else
      (none, false)

/-- Payload of the first row, or the empty stream for an empty family. -/
def unaryFrameMarkedRowHeadPayload
    (family : UnaryFrameMarkedRowFamily) : List UnaryFrameSym :=
  family.rows.headD []

private theorem markedRowHead_skip (input : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom unaryFrameMarkedRowHeadSpec false input =
      [] := by
  induction input with
  | nil => rfl
  | cons symbol rest ih =>
      cases symbol <;>
        simpa [rewriteUnaryFrameStatefulFrom,
          unaryFrameMarkedRowHeadSpec] using ih

private theorem markedRowHead_keep
    (row tail : List UnaryFrameSym)
    (hfree : ∀ symbol ∈ row, symbol ≠ UnaryFrameSym.frameEnd) :
    rewriteUnaryFrameStatefulFrom unaryFrameMarkedRowHeadSpec true
        (row ++ .frameEnd :: tail) = row := by
  induction row with
  | nil =>
      change rewriteUnaryFrameStatefulFrom
          unaryFrameMarkedRowHeadSpec false tail = []
      exact markedRowHead_skip tail
  | cons symbol rest ih =>
      have hsymbol := hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      cases symbol with
      | tick =>
          simp only [List.cons_append, rewriteUnaryFrameStatefulFrom,
            unaryFrameMarkedRowHeadSpec]
          exact congrArg (List.cons .tick) (ih hrest)
      | separator =>
          simp only [List.cons_append, rewriteUnaryFrameStatefulFrom,
            unaryFrameMarkedRowHeadSpec]
          exact congrArg (List.cons .separator) (ih hrest)
      | frameEnd => exact (hsymbol rfl).elim

/-- Exact action of the filter on a well-formed marked-row encoding. -/
theorem rewriteUnaryFrameMarkedRowHead_encode
    (family : UnaryFrameMarkedRowFamily) :
    rewriteUnaryFrameStateful unaryFrameMarkedRowHeadSpec
        (encodeUnaryFrameMarkedRowFamily family) =
      unaryFrameMarkedRowHeadPayload family := by
  unfold rewriteUnaryFrameStateful unaryFrameMarkedRowHeadPayload
    encodeUnaryFrameMarkedRowFamily
  cases hrows : family.rows with
  | nil =>
      rfl
  | cons row rows =>
      have hfree : ∀ symbol ∈ row,
          symbol ≠ UnaryFrameSym.frameEnd := by
        intro symbol hsymbol
        exact family.frameEnd_free row (by simp [hrows]) symbol hsymbol
      simp only [List.flatMap_cons, List.headD_cons]
      change rewriteUnaryFrameStatefulFrom unaryFrameMarkedRowHeadSpec true
          (row ++ [.frameEnd] ++
            rows.flatMap (fun rest => rest ++ [.frameEnd])) = row
      simpa [List.append_assoc] using
        markedRowHead_keep row
          (rows.flatMap (fun rest => rest ++ [.frameEnd])) hfree

/-- One fixed linear-time TM2 extracts the first marked-row payload. -/
noncomputable def unaryFrameMarkedRowHeadPayload_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameMarkedRowFamily id
      unaryFrameMarkedRowHeadPayload := by
  let raw := unaryFrameStatefulMap_computableInPolyTime
    unaryFrameMarkedRowHeadSpec
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun family => by
        have run := raw.outputsFun
          (encodeUnaryFrameMarkedRowFamily family)
        rw [rewriteUnaryFrameMarkedRowHead_encode family] at run
        simpa only [id_eq] using run }

end CLRS.Chapter34.Turing.PolyBuilder
