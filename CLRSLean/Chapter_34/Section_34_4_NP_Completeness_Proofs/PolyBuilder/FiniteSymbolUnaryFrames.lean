import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame

/-!
# Unary frames for finite-symbol codes

A fixed finite alphabet permits each symbol to carry a fixed natural-number
code in finite control.  The verified bounded-loop macro expands a raw input
word into one self-delimiting unary block per symbol.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Symbol-local expansion into one unary block. -/
def finiteSymbolUnaryFrameBody {Γ : Type} (code : Γ → Nat) :
    LoopBody Γ UnaryFrameSym where
  emit symbol := encodeUnaryFrameBlock (code symbol)
  cost symbol := code symbol + 1
  emit_length_le_cost symbol := by
    simp [encodeUnaryFrameBlock]

/-- Concatenated unary code blocks for a raw finite-alphabet word. -/
def finiteSymbolUnaryFrames {Γ : Type} (code : Γ → Nat)
    (input : List Γ) : List UnaryFrameSym :=
  input.flatMap (finiteSymbolUnaryFrameBody code).emit

/-- The bounded-loop target is precisely the ordinary unary encoding of the
pointwise code list. -/
theorem finiteSymbolUnaryFrames_eq_encodeUnaryFrame {Γ : Type}
    (code : Γ → Nat) (input : List Γ) :
    finiteSymbolUnaryFrames code input =
      encodeUnaryFrame (input.map code) := by
  unfold finiteSymbolUnaryFrames finiteSymbolUnaryFrameBody encodeUnaryFrame
  rw [List.flatMap_map]

/-- A fixed polynomial-time TM2 computes all symbol-code frames directly from
the raw word.  The finite code table contributes only a constant factor. -/
noncomputable def finiteSymbolUnaryFrames_computableInPolyTime
    {Γ : Type} [Fintype Γ] (code : Γ → Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (finiteSymbolUnaryFrames code) := by
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      input.flatMap (finiteSymbolUnaryFrameBody code).emit)
  exact boundedLoop_computableInPolyTime
    (finiteSymbolUnaryFrameBody code)

end CLRS.Chapter34.Turing.PolyBuilder
