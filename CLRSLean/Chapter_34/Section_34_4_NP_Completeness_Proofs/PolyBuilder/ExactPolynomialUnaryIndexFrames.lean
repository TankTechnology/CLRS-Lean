import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialClock
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryIndex
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame

/-!
# Exact polynomial-sized unary index frames

Runtime-sized Cook--Levin families need more than a clock: each family member
must know its ordinal.  This module composes the exact natural-polynomial clock
with the verified unary-index streamer and relabels its Boolean presentation
into delimiter-bearing unary frames.

Main results:

- Theorem {lit}`exactPolynomialUnaryIndexFrames_eq_map` identifies the
  relabeled machine stream with the canonical encoding of
  `0, ..., p(input.length) - 1`.
- Definition {lit}`exactPolynomialUnaryIndexFrames_computableInPolyTime`
  supplies one concrete polynomial-time TM2 for that exact stream.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Relabel the unary-index stream's Boolean presentation into the runtime
frame alphabet. -/
def unaryIndexFrameSymbol : Bool → UnaryFrameSym
  | true => .tick
  | false => .separator

/-- Symbol-local relabeler used by the final verified bounded loop. -/
def unaryIndexFrameBody : LoopBody Bool UnaryFrameSym where
  emit symbol := [unaryIndexFrameSymbol symbol]
  cost _ := 1
  emit_length_le_cost _ := le_rfl

/-- Canonical delimiter-bearing unary encodings of every ordinal below the
exact polynomial value at the raw input length. -/
def exactPolynomialUnaryIndexFrames {Γ : Type}
    (p : Polynomial Nat) (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrame (List.range (p.eval input.length))

/-- Relabeling the verified Boolean index stream gives byte-for-byte the
canonical delimiter-bearing frame family. -/
theorem exactPolynomialUnaryIndexFrames_eq_map {Γ : Type}
    (p : Polynomial Nat) (input : List Γ) :
    exactPolynomialUnaryIndexFrames p input =
      (unaryIndexStream (p.eval input.length)).map unaryIndexFrameSymbol := by
  unfold exactPolynomialUnaryIndexFrames encodeUnaryFrame unaryIndexStream
  rw [List.map_flatMap]
  congr 1
  funext index
  simp [unaryIndexCode, encodeUnaryFrameBlock, unaryIndexFrameSymbol]

/-- A fixed compiled TM2 maps the raw source word to every unary ordinal below
the value of a fixed natural polynomial. -/
noncomputable def exactPolynomialUnaryIndexFrames_computableInPolyTime
    {Γ : Type} [Fintype Γ] (p : Polynomial Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (@exactPolynomialUnaryIndexFrames Γ p) := by
  let indexed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (exactPolynomialClock_computableInPolyTime (Γ := Γ) p)
      unaryIndexStream_computableInPolyTime
  let relabeled :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (Classical.choice indexed)
      (boundedLoop_computableInPolyTime unaryIndexFrameBody)
  have hsingleton (bits : List Bool) :
      bits.flatMap (fun symbol => [unaryIndexFrameSymbol symbol]) =
        bits.map unaryIndexFrameSymbol := by
    induction bits with
    | nil => rfl
    | cons symbol rest ih => simp [ih]
  have hfunction :
      (fun input : List Γ =>
        (unaryIndexStream (exactPolynomialClock p input).length).flatMap
          (fun symbol => [unaryIndexFrameSymbol symbol])) =
      @exactPolynomialUnaryIndexFrames Γ p := by
    funext input
    rw [hsingleton, exactPolynomialClock_length]
    exact (exactPolynomialUnaryIndexFrames_eq_map p input).symm
  rw [← hfunction]
  simpa [Function.comp_def, unaryIndexFrameBody] using
    Classical.choice relabeled

end CLRS.Chapter34.Turing.PolyBuilder
