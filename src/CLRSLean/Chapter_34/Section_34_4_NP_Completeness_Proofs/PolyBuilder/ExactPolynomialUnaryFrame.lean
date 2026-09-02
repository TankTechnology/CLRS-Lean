import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialClock
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame

/-!
# Exact polynomial unary frames

The exact polynomial clock produces a token list whose length is a fixed
polynomial in the raw input length.  This module compiles those tokens into
the delimiter-bearing unary representation consumed by the Cook--Levin
runtime controllers.  Every stage is a concrete compiled TM2.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Relabel a clock token as a unary tick and its unique sentinel as the
terminating separator. -/
def unaryFrameSymbolBody : LoopBody (Option Unit) UnaryFrameSym where
  emit
    | some _ => [.tick]
    | none => [.separator]
  cost := fun _ => 1
  emit_length_le_cost := by
    intro symbol
    cases symbol <;> simp

/-- Symbol-local conversion of a sentinel-terminated unit clock into unary
frame symbols. -/
def unaryFrameSymbols (input : List (Option Unit)) : List UnaryFrameSym :=
  input.flatMap unaryFrameSymbolBody.emit

/-- A sentinel-terminated unit clock becomes exactly one self-delimiting
unary block. -/
@[simp] theorem unaryFrameSymbols_sentinelInput (tokens : List Unit) :
    unaryFrameSymbols (sentinelInput tokens) =
      encodeUnaryFrameBlock tokens.length := by
  induction tokens with
  | nil => rfl
  | cons _ tokens ih =>
      change .tick :: unaryFrameSymbols (sentinelInput tokens) =
        List.replicate (tokens.length + 1) .tick ++ [.separator]
      rw [ih]
      simp [encodeUnaryFrameBlock, List.replicate_succ]

/-- The sentinel-to-frame relabeler is one concrete verified bounded-loop
machine. -/
noncomputable def unaryFrameSymbols_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id unaryFrameSymbols := by
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List (Option Unit) =>
      input.flatMap unaryFrameSymbolBody.emit)
  exact boundedLoop_computableInPolyTime unaryFrameSymbolBody

/-- Unary operand block whose value is a fixed polynomial evaluated at the
raw input length. -/
def exactPolynomialUnaryFrame {Γ : Type} (p : Polynomial Nat)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrameBlock (p.eval input.length)

/-- The concrete clock/sentinel/relabel pipeline has exactly the public unary
frame semantics. -/
theorem exactPolynomialUnaryFrame_eq {Γ : Type}
    (p : Polynomial Nat) (input : List Γ) :
    unaryFrameSymbols (sentinelInput (exactPolynomialClock p input)) =
      exactPolynomialUnaryFrame p input := by
  simp [exactPolynomialUnaryFrame]

/-- A fixed compiled TM2 maps the raw source word to the exact unary encoding
of any fixed polynomial in its length. -/
noncomputable def exactPolynomialUnaryFrame_computableInPolyTime
    {Γ : Type} [Fintype Γ] (p : Polynomial Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (@exactPolynomialUnaryFrame Γ p) := by
  let clockThenSentinel :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (exactPolynomialClock_computableInPolyTime (Γ := Γ) p)
      (sentinelInput_computableInPolyTime Unit)
  let full :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (Classical.choice clockThenSentinel)
      unaryFrameSymbols_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ => encodeUnaryFrameBlock (p.eval input.length))
  simpa [Function.comp_def] using Classical.choice full

end CLRS.Chapter34.Turing.PolyBuilder
