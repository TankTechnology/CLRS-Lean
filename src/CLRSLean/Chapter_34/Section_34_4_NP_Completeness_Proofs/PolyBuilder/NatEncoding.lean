import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.Encoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryIndex

/-!
# Natural-number serializers for circuit builders

Circuit encodings use unary natural numbers.  This module connects the
counter-oriented builder layer to the actual `CircuitSym` alphabet: one
machine serializes the length of an arbitrary finite input, and a second
construction maps the verified stream of indices `0, ..., n - 1` to the
corresponding concatenation of `encNat` blocks.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-! ## Encoding one input length -/

/-- Finite control for the direct input-length serializer. -/
inductive LengthEncodingLabel
  | start
  | pop
  | push
  | halt
deriving DecidableEq, Fintype

/-- Emit `encNat input.length` directly in the circuit alphabet.  The
terminator is pushed first; every consumed input symbol then prepends one
argument mark. -/
def lengthEncodingProgram (Γ : Type) [Fintype Γ] : Program Γ CircuitSym where
  Label := LengthEncodingLabel
  main := .start
  op
    | .start => .pushOutput .endMark .pop
    | .pop => .popInput .halt (fun _ => .push)
    | .push => .pushOutput .argMark .pop
    | .halt => .halt

/-- Exact step count for direct length serialization. -/
def lengthEncodingSteps {Γ : Type} (input : List Γ) : Nat :=
  2 * input.length + 3

private def lengthEncodingCfg {Γ : Type} [Fintype Γ]
    (label : LengthEncodingLabel) (buffer : Option Γ) (input : List Γ)
    (output : List CircuitSym) : BuilderCfg (lengthEncodingProgram Γ) :=
  { initialCfg (lengthEncodingProgram Γ) input with
      label := some label
      buffer₁ := buffer
      output := output }

private theorem replicate_append_cons {α : Type} (value : α)
    (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

/-- Exact pop/push loop equation from an arbitrary output suffix. -/
private theorem lengthEncoding_popPush_eval {Γ : Type} [Fintype Γ]
    (buffer : Option Γ) (input : List Γ) (output : List CircuitSym) :
    (flip Option.bind (step (lengthEncodingProgram Γ)))^[
        2 * input.length + 1]
      (some (lengthEncodingCfg .pop buffer input output)) =
        some (lengthEncodingCfg .halt none []
          (List.replicate input.length .argMark ++ output)) := by
  induction input generalizing buffer output with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show 2 * (symbol :: rest).length + 1 =
          (2 * rest.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step (lengthEncodingProgram Γ)))^[
            2 * rest.length + 1]
          (some (lengthEncodingCfg .pop (some symbol) rest
            (.argMark :: output))) = _
      simpa only [List.length_cons, List.replicate_succ,
        replicate_append_cons, List.cons_append] using
        ih (some symbol) (.argMark :: output)

/-- Canonical exact run of the input-length serializer. -/
def lengthEncoding_run {Γ : Type} [Fintype Γ] (input : List Γ) :
    EvalsToInTime (step (lengthEncodingProgram Γ))
      (initialCfg (lengthEncodingProgram Γ) input)
      (some (haltCfg (lengthEncodingProgram Γ) (encNat input.length)))
      (lengthEncodingSteps input) := by
  have hstart : EvalsToInTime (step (lengthEncodingProgram Γ))
      (initialCfg (lengthEncodingProgram Γ) input)
      (some (lengthEncodingCfg .pop none input [.endMark])) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  have hloop : EvalsToInTime (step (lengthEncodingProgram Γ))
      (lengthEncodingCfg .pop none input [.endMark])
      (some (lengthEncodingCfg .halt none []
        (List.replicate input.length .argMark ++ [.endMark])))
      (2 * input.length + 1) := by
    exact ⟨⟨2 * input.length + 1,
      lengthEncoding_popPush_eval none input [.endMark]⟩, le_rfl⟩
  have hhalt : EvalsToInTime (step (lengthEncodingProgram Γ))
      (lengthEncodingCfg .halt none []
        (List.replicate input.length .argMark ++ [.endMark]))
      (some (haltCfg (lengthEncodingProgram Γ)
        (List.replicate input.length .argMark ++ [.endMark]))) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  let throughLoop := EvalsToInTime.trans (step (lengthEncodingProgram Γ))
    1 (2 * input.length + 1) _ _ _ hstart hloop
  let full := EvalsToInTime.trans (step (lengthEncodingProgram Γ))
    ((2 * input.length + 1) + 1) 1 _ _ _ throughLoop hhalt
  have hbound : 1 + ((2 * input.length + 1) + 1) =
      lengthEncodingSteps input := by
    simp [lengthEncodingSteps]
    omega
  rw [← hbound]
  simpa [encNat] using full

/-- Independent output contract for exact input-length serialization. -/
theorem lengthEncoding_builderOutputs {Γ : Type} [Fintype Γ] :
    BuilderOutputs (lengthEncodingProgram Γ)
      (fun input => encNat input.length) lengthEncodingSteps := by
  intro input
  exact ⟨lengthEncoding_run input⟩

/-- Compiled TM2 output contract for exact input-length serialization. -/
theorem lengthEncoding_outputs {Γ : Type} [Fintype Γ] :
    Outputs (lengthEncodingProgram Γ)
      (fun input => encNat input.length) lengthEncodingSteps :=
  Outputs.of_builder_run lengthEncoding_builderOutputs

/-- Linear runtime envelope for the direct serializer. -/
noncomputable def lengthEncoding_polyBound {Γ : Type} :
    PolyBound (@lengthEncodingSteps Γ) where
  polynomial := 2 * Polynomial.X + 3
  bound input := by
    simp [lengthEncodingSteps, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X]

/-- Concrete polynomial-time TM2 computing `encNat input.length`. -/
noncomputable def lengthEncoding_computableInPolyTime
    (Γ : Type) [Fintype Γ] :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Γ => encNat input.length) :=
  ComputableInPolyTime (lengthEncodingProgram Γ)
    (fun input => encNat input.length) lengthEncodingSteps
    lengthEncoding_outputs lengthEncoding_polyBound

/-! ## Encoding the complete index stream -/

/-- Interpret the Boolean counter presentation in the circuit alphabet. -/
def circuitIndexSymbol : Bool → CircuitSym
  | true => .argMark
  | false => .endMark

/-- Symbol-local Boolean-to-circuit mapping used by the verified bounded
loop. -/
def circuitIndexBody : LoopBody Bool CircuitSym where
  emit symbol := [circuitIndexSymbol symbol]
  cost _ := 1
  emit_length_le_cost _ := le_rfl

/-- Concatenated circuit encodings of `0, ..., count - 1`. -/
def circuitIndexStream (count : Nat) : List CircuitSym :=
  (List.range count).flatMap encNat

/-- Mapping the Boolean index stream gives exactly the canonical circuit
index stream. -/
theorem circuitIndexStream_eq_map (count : Nat) :
    circuitIndexStream count =
      (unaryIndexStream count).map circuitIndexSymbol := by
  symm
  rw [unaryIndexStream, List.map_flatMap]
  simp only [circuitIndexStream]
  congr 1
  funext index
  simp [unaryIndexCode, circuitIndexSymbol, encNat]

/-- The actual `CircuitSym` index stream is polynomial-time computable from a
unit clock. -/
noncomputable def circuitIndexStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Unit => circuitIndexStream input.length) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unaryIndexStream_computableInPolyTime
      (boundedLoop_computableInPolyTime circuitIndexBody)
  have hsingleton (bits : List Bool) :
      bits.flatMap (fun symbol => [circuitIndexSymbol symbol]) =
        bits.map circuitIndexSymbol := by
    induction bits with
    | nil => rfl
    | cons symbol rest ih => simp [ih]
  have hfun :
      (fun input : List Unit =>
        (unaryIndexStream input.length).flatMap
          (fun symbol => [circuitIndexSymbol symbol])) =
      (fun input : List Unit => circuitIndexStream input.length) := by
    funext input
    rw [hsingleton, circuitIndexStream_eq_map]
  simpa [Function.comp_def, circuitIndexBody, hfun] using
    Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
