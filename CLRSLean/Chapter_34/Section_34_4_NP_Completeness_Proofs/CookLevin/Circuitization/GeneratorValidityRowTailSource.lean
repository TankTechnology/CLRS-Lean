import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowTailOperands
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleMapSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineValidityTailSourceFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameDelimiterMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedPrefixSplice
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Fixed affine operands of the Cook--Levin validity tail

The compact tail invocation has two genuinely different parts.  Every fixed
machine stack contributes eight affine unary fields (including one zero
field that materializes an internal boundary), and the final conjunction has
four affine prefix values.  Its intervening one-hot frame family has runtime
height and is handled separately by the existing structured-row source.  This
module compiles the fixed part from the same raw `(height, start, rowBase)`
seed stream without placing any runtime value in finite control.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Height coefficient of the bit offset preceding one fixed stack. -/
noncomputable def cfgStackBitOffsetHeightCoeff
    (tm : _root_.Turing.FinTM2) (k : tm.K) : Nat := by
  letI : Fintype tm.K := tm.kFin
  let keyEquiv : tm.K ≃ Fin (Fintype.card tm.K) := Fintype.equivFin tm.K
  exact ∑ j : Fin (keyEquiv k),
    ((reachableAlphabet tm
      (keyEquiv.symm (Fin.castLE (keyEquiv k).isLt.le j))).card + 2)

/-- The dependent stack-bit prefix is affine in the runtime height. -/
theorem cfgStackBitOffset_eq_affine
    (tm : _root_.Turing.FinTM2) (H : Nat) (k : tm.K) :
    cfgStackBitOffset tm H k =
      arithmeticStackOrdinal tm k + cfgStackBitOffsetHeightCoeff tm k * H := by
  letI : Fintype tm.K := tm.kFin
  let keyEquiv : tm.K ≃ Fin (Fintype.card tm.K) := Fintype.equivFin tm.K
  unfold cfgStackBitOffset cfgStackBitOffsetHeightCoeff
    arithmeticStackOrdinal
  change (∑ j : Fin (keyEquiv k),
      cfgStackBitWidth tm H
        (keyEquiv.symm (Fin.castLE (keyEquiv k).isLt.le j))) = _
  calc
    (∑ j : Fin (keyEquiv k),
        cfgStackBitWidth tm H
          (keyEquiv.symm (Fin.castLE (keyEquiv k).isLt.le j))) =
        ∑ j : Fin (keyEquiv k),
          (1 + ((reachableAlphabet tm
            (keyEquiv.symm (Fin.castLE (keyEquiv k).isLt.le j))).card + 2) *
              H) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [cfgStackBitWidth]
      ring
    _ = (∑ _j : Fin (keyEquiv k), 1) +
          ∑ j : Fin (keyEquiv k),
            ((reachableAlphabet tm
              (keyEquiv.symm (Fin.castLE (keyEquiv k).isLt.le j))).card + 2) *
                H := Finset.sum_add_distrib
    _ = (keyEquiv k).val +
          (∑ j : Fin (keyEquiv k),
            ((reachableAlphabet tm
              (keyEquiv.symm (Fin.castLE (keyEquiv k).isLt.le j))).card + 2)) *
              H := by
      rw [← Finset.sum_mul]
      simp

/-- Constant part of the raw one-hot gate count. -/
def arithmeticRawOneHotGateCountConstant
    (tm : _root_.Turing.FinTM2) : Nat :=
  (3 * (labelCount tm + 1) + 4) + (3 * stateCount tm + 4) +
    7 * arithmeticStackCount tm

/-- Height coefficient of the raw one-hot gate count. -/
noncomputable def arithmeticRawOneHotGateCountHeightCoeff
    (tm : _root_.Turing.FinTM2) : Nat := by
  letI : Fintype tm.K := tm.kFin
  exact ∑ k : tm.K, (3 * (reachableAlphabet tm k).card + 10)

/-- The complete raw one-hot trace length is affine in runtime height. -/
theorem arithmeticRawOneHotGateCount_eq_affine
    (tm : _root_.Turing.FinTM2) (H : Nat) :
    arithmeticRawOneHotGateCount tm H =
      arithmeticRawOneHotGateCountConstant tm +
        arithmeticRawOneHotGateCountHeightCoeff tm * H := by
  letI : Fintype tm.K := tm.kFin
  unfold arithmeticRawOneHotGateCount
    arithmeticRawOneHotGateCountConstant
    arithmeticRawOneHotGateCountHeightCoeff arithmeticStackCount
  calc
    (3 * (labelCount tm + 1) + 4) + (3 * stateCount tm + 4) +
        ∑ k : tm.K,
          ((3 * (H + 1) + 4) +
            H * (3 * ((reachableAlphabet tm k).card + 1) + 4)) =
      (3 * (labelCount tm + 1) + 4) + (3 * stateCount tm + 4) +
        ∑ k : tm.K,
          (7 + (3 * (reachableAlphabet tm k).card + 10) * H) := by
      apply congrArg
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (3 * (labelCount tm + 1) + 4) + (3 * stateCount tm + 4) +
          7 * Fintype.card tm.K +
        (∑ k : tm.K, (3 * (reachableAlphabet tm k).card + 10)) * H := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp
      ring

private def affineValidityForm (constant height start rowBase : Nat) :
    AffineUnaryTripleForm :=
  { constant := constant
    first := height
    second := start
    third := rowBase }

private def arithmeticStackBlockStartConstant
    (tm : _root_.Turing.FinTM2) (k : tm.K) : Nat :=
  arithmeticRawOneHotGateCountConstant tm + 5 +
    arithmeticStackOrdinal tm k

private def arithmeticStackBlockStartHeightCoeff
    (tm : _root_.Turing.FinTM2) (k : tm.K) : Nat :=
  arithmeticRawOneHotGateCountHeightCoeff tm +
    7 * arithmeticStackOrdinal tm k

/-- Eight unary values needed by one standalone stack invocation, in exact
consumption order.  The inserted zero emits the internal `frameEnd` between
the six-field header and the runtime-height payload; the final repeated
height receives the outer stack `frameEnd`. -/
noncomputable def arithmeticValidityTailStackOperandForms
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    List AffineUnaryTripleForm :=
  let blockConstant := arithmeticStackBlockStartConstant tm k
  let blockHeight := arithmeticStackBlockStartHeightCoeff tm k
  let offsetConstant := arithmeticStackOrdinal tm k
  let offsetHeight := cfgStackBitOffsetHeightCoeff tm k
  let maskBaseConstant :=
    1 + (labelCount tm + 1) + stateCount tm + offsetConstant + 1
  let blankConstant :=
    1 + (labelCount tm + 1) + stateCount tm + offsetConstant + 1 +
      (reachableAlphabet tm k).card
  [ affineValidityForm (blockConstant + 1) (blockHeight + 1) 1 0,
    affineValidityForm blockConstant (blockHeight + 1) 1 0,
    affineValidityForm blankConstant (offsetHeight + 1) 0 1,
    affineValidityForm 0 1 0 0,
    affineValidityForm blockConstant blockHeight 1 0,
    affineValidityForm maskBaseConstant (offsetHeight + 1) 0 1,
    affineValidityForm 0 0 0 0,
    affineValidityForm 0 1 0 0 ]

/-- Fixed stack table in canonical machine-stack order. -/
noncomputable def arithmeticValidityTailStackOperandFormsFamily
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  (arithmeticRuntimeStackSourceIndices tm).flatMap fun j =>
    arithmeticValidityTailStackOperandForms tm
      ((arithmeticStackEquiv tm).symm j)

/-- Four fixed fields that precede the variable raw-output frame family in
the final-conjunction source invocation. -/
noncomputable def arithmeticValidityTailFinalPrefixForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  let rawConstant := arithmeticRawOneHotGateCountConstant tm
  let rawHeight := arithmeticRawOneHotGateCountHeightCoeff tm
  let stackCount := arithmeticStackCount tm
  [ affineValidityForm (rawConstant + 5 + stackCount)
      (rawHeight + 7 * stackCount) 1 0,
    affineValidityForm 0 1 0 0,
    affineValidityForm (rawConstant + 5) rawHeight 1 0,
    affineValidityForm (rawConstant + 4) rawHeight 1 0 ]

/-- Complete fixed affine table for one validity-tail row. -/
noncomputable def arithmeticValidityTailFixedOperandForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  arithmeticValidityTailStackOperandFormsFamily tm ++
    arithmeticValidityTailFinalPrefixForms tm

private def validityRowAffineSeed (H start rowBase : Nat) :
    AffineUnaryTripleSeed :=
  { first := H, second := start, third := rowBase }

/-- Semantic fixed values, stated directly from the established compact
source frames rather than from the affine formulas. -/
noncomputable def arithmeticValidityTailFixedOperandValues
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) : List Nat :=
  ((arithmeticRuntimeStackSourceSeeds tm H start rowBase).flatMap fun seed =>
      [seed.cellRight, seed.cellLeft, seed.cellBlank, seed.count,
        seed.maskStart, seed.maskBase + seed.count, 0, seed.count]) ++
    [ arithmeticValidityFinalStart tm H start,
      H,
      arithmeticStackValidityStart tm H start,
      arithmeticHaltedMatchStart tm H start + 4 ]

private theorem arithmeticValidityTailStackOperandForms_eq
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    affineUnaryTripleMap (arithmeticValidityTailStackOperandForms tm k)
        (validityRowAffineSeed H start rowBase) =
      let seed := arithmeticRuntimeStackSourceSeed tm H start rowBase k
      [seed.cellRight, seed.cellLeft, seed.cellBlank, seed.count,
        seed.maskStart, seed.maskBase + seed.count, 0, seed.count] := by
  simp [arithmeticValidityTailStackOperandForms, affineUnaryTripleMap,
    affineUnaryTripleFormValue, affineValidityForm,
    validityRowAffineSeed, arithmeticRuntimeStackSourceSeed,
    arithmeticStackCellTraceStart, arithmeticStackBlockStart,
    arithmeticStackValidityStart, arithmeticHaltedMatchStart,
    arithmeticStackMaskWireBase, arithmeticStackCellBlankBase,
    arithmeticStackBlockStartConstant,
    arithmeticStackBlockStartHeightCoeff,
    arithmeticRawOneHotGateCount_eq_affine,
    cfgStackBitOffset_eq_affine]
  ring <;> simp

private theorem arithmeticValidityTailFinalPrefixForms_eq
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    affineUnaryTripleMap (arithmeticValidityTailFinalPrefixForms tm)
        (validityRowAffineSeed H start rowBase) =
      [ arithmeticValidityFinalStart tm H start,
        H,
        arithmeticStackValidityStart tm H start,
        arithmeticHaltedMatchStart tm H start + 4 ] := by
  simp [arithmeticValidityTailFinalPrefixForms, affineUnaryTripleMap,
    affineUnaryTripleFormValue, affineValidityForm,
    validityRowAffineSeed, arithmeticValidityFinalStart,
    arithmeticStackValidityStart, arithmeticHaltedMatchStart,
    arithmeticRawOneHotGateCount_eq_affine]
  ring <;> simp

/-- The fixed affine table is byte-value exact for every runtime row seed. -/
theorem arithmeticValidityTailFixedOperandForms_eq
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    affineUnaryTripleMap (arithmeticValidityTailFixedOperandForms tm)
        (validityRowAffineSeed H start rowBase) =
      arithmeticValidityTailFixedOperandValues tm H start rowBase := by
  unfold arithmeticValidityTailFixedOperandForms
    arithmeticValidityTailFixedOperandValues
  rw [show affineUnaryTripleMap
      (arithmeticValidityTailStackOperandFormsFamily tm ++
        arithmeticValidityTailFinalPrefixForms tm)
      (validityRowAffineSeed H start rowBase) =
      affineUnaryTripleMap (arithmeticValidityTailStackOperandFormsFamily tm)
          (validityRowAffineSeed H start rowBase) ++
        affineUnaryTripleMap (arithmeticValidityTailFinalPrefixForms tm)
          (validityRowAffineSeed H start rowBase) by
    simp [affineUnaryTripleMap]]
  rw [arithmeticValidityTailFinalPrefixForms_eq]
  congr 1
  unfold arithmeticValidityTailStackOperandFormsFamily
    arithmeticRuntimeStackSourceSeeds
  rw [List.flatMap_map]
  simp only [affineUnaryTripleMap, List.map_flatMap]
  apply List.flatMap_congr
  intro j hj
  exact arithmeticValidityTailStackOperandForms_eq tm H start rowBase
    ((arithmeticStackEquiv tm).symm j)

/-- Fixed operand values for every canonical verifier row. -/
noncomputable def verifierValidityRowTailFixedOperandValues
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List Nat :=
  (verifierValidityRowSeeds W input).flatMap fun seed =>
    arithmeticValidityTailFixedOperandValues W.machine.tm
      seed.height seed.start seed.rowBase

/-- The generic affine source consumes exactly the established row-seed byte
stream at the Cook--Levin specialization. -/
theorem verifierValidityRowTailAffineSeedEncoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineUnaryTripleSeedFamily
        ((verifierValidityRowSeeds W input).map fun seed =>
          validityRowAffineSeed seed.height seed.start seed.rowBase) =
      verifierValidityRowSeedFrames W input := by
  rw [verifierValidityRowSeedFrames_eq_seeds]
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.map_cons, encodeAffineUnaryTripleSeedFamily,
        encodeAffineUnaryTripleSeed, List.flatMap_cons]
      rw [ih]
      rfl

private theorem verifierValidityRowTailAffineValues_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    affineUnaryTripleMapFamily
        (arithmeticValidityTailFixedOperandForms W.machine.tm)
        ((verifierValidityRowSeeds W input).map fun seed =>
          validityRowAffineSeed seed.height seed.start seed.rowBase) =
      verifierValidityRowTailFixedOperandValues W input := by
  unfold affineUnaryTripleMapFamily verifierValidityRowTailFixedOperandValues
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  exact arithmeticValidityTailFixedOperandForms_eq
    W.machine.tm seed.height seed.start seed.rowBase

/-- The raw verifier word polynomially computes all fixed affine values of
every tail invocation.  Runtime-height one-hot frames remain a separate,
already verified structured-row phase. -/
noncomputable def
    verifierValidityRowTailFixedOperandFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Γ =>
        encodeUnaryFrame (verifierValidityRowTailFixedOperandValues W input)) := by
  let seedSource := verifierValidityRowSeedFrames_computableInPolyTime W
  let affineSource := affineUnaryTripleMapFamily_computableInPolyTime
    (arithmeticValidityTailFixedOperandForms W.machine.tm)
  let repackagedSeedSource :
      _root_.Turing.TM2ComputableInPolyTime id
        encodeAffineUnaryTripleSeedFamily
        (fun input : List Γ =>
          (verifierValidityRowSeeds W input).map fun seed =>
            validityRowAffineSeed seed.height seed.start seed.rowBase) :=
    { tm := seedSource.tm
      inputAlphabet := seedSource.inputAlphabet
      outputAlphabet := seedSource.outputAlphabet
      time := seedSource.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierValidityRowTailAffineSeedEncoding_eq W input] using
          seedSource.outputsFun input }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      repackagedSeedSource affineSource
  simpa [Function.comp_def,
    verifierValidityRowTailAffineValues_eq] using Classical.choice composed

/-! ## Fixed invocation delimiters -/

/-- Delimiter layout of one standalone runtime-stack invocation.  The
seventh zero field materializes the header boundary; the eighth height field
is the runtime payload terminated by the outer stack boundary. -/
def arithmeticValidityTailStackOperandDelimiters : List UnaryFrameSym :=
  [.separator, .separator, .separator, .separator,
    .separator, .separator, .frameEnd, .frameEnd]

/-- The four fixed final-conjunction prefix operands remain ordinary unary
blocks; the variable one-hot family follows them in the next source layer. -/
def arithmeticValidityTailFinalPrefixDelimiters : List UnaryFrameSym :=
  [.separator, .separator, .separator, .separator]

/-- One complete cyclic delimiter table for the fixed part of a validity-tail
row: one eight-field stack invocation per fixed machine stack, then the four
final-conjunction prefix fields. -/
def arithmeticValidityTailFixedOperandDelimiters
    (tm : _root_.Turing.FinTM2) : List UnaryFrameSym :=
  ((arithmeticRuntimeStackSourceIndices tm).flatMap fun _ =>
      arithmeticValidityTailStackOperandDelimiters) ++
    arithmeticValidityTailFinalPrefixDelimiters

@[simp] theorem arithmeticValidityTailFixedOperandDelimiters_nonempty
    (tm : _root_.Turing.FinTM2) :
    0 < (arithmeticValidityTailFixedOperandDelimiters tm).length := by
  simp [arithmeticValidityTailFixedOperandDelimiters,
    arithmeticValidityTailFinalPrefixDelimiters]

/-- The delimiter table has exactly one entry for every fixed affine form. -/
theorem arithmeticValidityTailFixedOperandDelimiters_length
    (tm : _root_.Turing.FinTM2) :
    (arithmeticValidityTailFixedOperandDelimiters tm).length =
      (arithmeticValidityTailFixedOperandForms tm).length := by
  simp [arithmeticValidityTailFixedOperandDelimiters,
    arithmeticValidityTailStackOperandDelimiters,
    arithmeticValidityTailFinalPrefixDelimiters,
    arithmeticValidityTailFixedOperandForms,
    arithmeticValidityTailStackOperandFormsFamily,
    arithmeticValidityTailStackOperandForms,
    arithmeticValidityTailFinalPrefixForms, affineValidityForm]

/-- Marked fixed-operand byte stream emitted for every verifier row.  The
cycle resets after the four final prefix fields because its period is exactly
one row's fixed affine table. -/
noncomputable def verifierValidityRowTailMarkedFixedOperandFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameDelimiters
    (arithmeticValidityTailFixedOperandDelimiters W.machine.tm)
    (arithmeticValidityTailFixedOperandDelimiters_nonempty W.machine.tm)
    (encodeUnaryFrame (verifierValidityRowTailFixedOperandValues W input))

/-- Byte-level semantics of the marked fixed stream: the declared row table
is applied to the affine values, so each stack's internal zero field and
outer height field are terminated by `frameEnd`, while all other fixed fields
retain `separator`. -/
theorem verifierValidityRowTailMarkedFixedOperandFrames_eq_cycle
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowTailMarkedFixedOperandFrames W input =
      encodeUnaryFrameWithDelimiterCycle
        (arithmeticValidityTailFixedOperandDelimiters W.machine.tm)
        (arithmeticValidityTailFixedOperandDelimiters_nonempty W.machine.tm)
        (verifierValidityRowTailFixedOperandValues W input) := by
  exact rewriteUnaryFrameDelimiters_encodeUnaryFrame
    (arithmeticValidityTailFixedOperandDelimiters W.machine.tm)
    (arithmeticValidityTailFixedOperandDelimiters_nonempty W.machine.tm)
    (verifierValidityRowTailFixedOperandValues W input)

/-- The raw verifier word computes the fixed validity-tail operand stream
with every stack-family boundary already materialized as `frameEnd`. -/
noncomputable def
    verifierValidityRowTailMarkedFixedOperandFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowTailMarkedFixedOperandFrames W) := by
  let valueSource :=
    verifierValidityRowTailFixedOperandFrames_computableInPolyTime W
  let delimiterSource :=
    unaryFrameDelimiterMap_computableInPolyTime
      (arithmeticValidityTailFixedOperandDelimiters W.machine.tm)
      (arithmeticValidityTailFixedOperandDelimiters_nonempty W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      valueSource delimiterSource
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_def,
          verifierValidityRowTailMarkedFixedOperandFrames] using run }

/-! ## Payload-preserving row source -/

/-- The compact one-hot invocation payload never contains the outer row
boundary symbol. -/
private theorem affineExactlyOneOutputInvocationFamily_no_frameEnd
    (frames : List AffineExactlyOneFrame) :
    ∀ symbol ∈ encodeAffineExactlyOneOutputSourceInvocationFamily frames,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  rw [encodeAffineExactlyOneOutputSourceInvocationFamily,
    List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨frame, hframe, hsymbol⟩
  rw [encodeAffineExactlyOneOutputSourceInvocation, encodeUnaryFrame,
    List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, hvalue, hsymbol⟩
  simp [encodeUnaryFrameBlock] at hsymbol
  rcases hsymbol with ⟨_, rfl⟩ | rfl <;> simp

/-- One normalized verifier row, typed for the payload-preserving affine
source.  Its payload is exactly the compact one-hot source family already
computed by the seed-carrier normalization stage. -/
noncomputable def verifierValidityRowTailPayloadRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineUnaryTriplePayloadRow :=
  (verifierValidityRowSeeds W input).map fun seed =>
    { seed := validityRowAffineSeed seed.height seed.start seed.rowBase
      payload := encodeAffineExactlyOneOutputSourceInvocationFamily
        (validityRowSeedOneHotFrames W.machine.tm seed).reverse }

/-- Well-formed typed family presented to the generic affine source. -/
noncomputable def verifierValidityRowTailPayloadFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : AffineUnaryTriplePayloadFamily :=
  { rows := verifierValidityRowTailPayloadRows W input
    payload_frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [verifierValidityRowTailPayloadRows, List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      exact affineExactlyOneOutputInvocationFamily_no_frameEnd _ symbol hsymbol }

/-- The normalized seed-first byte stream is definitionally the concrete
encoding of the typed payload family. -/
theorem verifierValidityRowTailPayloadFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineUnaryTriplePayloadFamily
        (verifierValidityRowTailPayloadFamily W input) =
      verifierValidityRowSeedFirstOutputInvocationFrames W input := by
  rw [verifierValidityRowSeedFirstOutputInvocationFrames_eq_rows]
  unfold encodeAffineUnaryTriplePayloadFamily
  change encodeAffineUnaryTriplePayloadRowFamily
      (verifierValidityRowTailPayloadRows W input) = _
  unfold verifierValidityRowTailPayloadRows
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.map_cons, encodeAffineUnaryTriplePayloadRowFamily,
        List.flatMap_cons]
      rw [ih]
      simp [encodeAffineUnaryTriplePayloadRow,
        encodeAffineUnaryTripleSeed,
        encodeAffineExactlyOneStructuredRowSeed, validityRowAffineSeed,
        List.append_assoc]

/-- Byte stream after the fixed affine table has been evaluated row by row;
the one-hot payload and both row boundaries are still present. -/
noncomputable def verifierValidityRowTailAffinePayloadFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTriplePayloadRowOutputFamily
    (arithmeticValidityTailFixedOperandForms W.machine.tm)
    (verifierValidityRowTailPayloadRows W input)

/-- Exact row semantics of the payload-preserving affine stage. -/
theorem verifierValidityRowTailAffinePayloadFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowTailAffinePayloadFrames W input =
      (verifierValidityRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
            (arithmeticValidityTailFixedOperandValues W.machine.tm
              seed.height seed.start seed.rowBase) ++
          [.frameEnd] ++
          encodeAffineExactlyOneOutputSourceInvocationFamily
              (validityRowSeedOneHotFrames W.machine.tm seed).reverse ++
            [.frameEnd] := by
  unfold verifierValidityRowTailAffinePayloadFrames
    verifierValidityRowTailPayloadRows
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.map_cons, affineUnaryTriplePayloadRowOutputFamily,
        List.flatMap_cons]
      rw [ih]
      simp only [affineUnaryTriplePayloadRowOutput]
      rw [arithmeticValidityTailFixedOperandForms_eq]

/-- The raw verifier word polynomially computes every row's fixed affine
operands while carrying the variable one-hot source invocations unchanged. -/
noncomputable def
    verifierValidityRowTailAffinePayloadFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowTailAffinePayloadFrames W) := by
  let normalizedSource :=
    verifierValidityRowSeedFirstOutputInvocationFrames_computableInPolyTime W
  let typedNormalizedSource :
      _root_.Turing.TM2ComputableInPolyTime id
        encodeAffineUnaryTriplePayloadFamily
        (verifierValidityRowTailPayloadFamily W) :=
    { tm := normalizedSource.tm
      inputAlphabet := normalizedSource.inputAlphabet
      outputAlphabet := normalizedSource.outputAlphabet
      time := normalizedSource.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierValidityRowTailPayloadFamily_encoding_eq W input] using
          normalizedSource.outputsFun input }
  let affineSource := affineUnaryTriplePayloadFamily_computableInPolyTime
    (arithmeticValidityTailFixedOperandForms W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      typedNormalizedSource affineSource
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      affineUnaryTriplePayloadRowOutputFamily
        (arithmeticValidityTailFixedOperandForms W.machine.tm)
        (verifierValidityRowTailPayloadRows W input))
  simpa [Function.comp_def, verifierValidityRowTailPayloadFamily] using
    Classical.choice composed

/-- The affine stage is exactly the generic fixed-prefix splice input: one
ordinary fixed table, an internal boundary, the protected one-hot payload,
and the outer row boundary. -/
theorem verifierValidityRowTailAffinePayloadFrames_eq_spliceInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowTailAffinePayloadFrames W input =
      encodeUnaryFrameFixedPrefixSpliceInputFamily
        (fun seed : ValidityRowSeed =>
          arithmeticValidityTailFixedOperandValues W.machine.tm
            seed.height seed.start seed.rowBase)
        (fun seed : ValidityRowSeed =>
          encodeAffineExactlyOneOutputSourceInvocationFamily
            (validityRowSeedOneHotFrames W.machine.tm seed).reverse)
        (verifierValidityRowSeeds W input) := by
  rw [verifierValidityRowTailAffinePayloadFrames_eq_rows]
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons,
        encodeUnaryFrameFixedPrefixSpliceInputFamily]
      rw [ih]

/-- Every semantic fixed row has the verifier-fixed delimiter-table length. -/
private theorem arithmeticValidityTailFixedOperandValues_length
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    (arithmeticValidityTailFixedOperandValues tm H start rowBase).length =
      (arithmeticValidityTailFixedOperandDelimiters tm).length := by
  rw [← arithmeticValidityTailFixedOperandForms_eq tm H start rowBase]
  simp [affineUnaryTripleMap,
    arithmeticValidityTailFixedOperandDelimiters_length]

/-- Fixed stack and final-prefix delimiters are now materialized in every
row, while the one-hot invocation payload remains byte-for-byte unchanged. -/
noncomputable def verifierValidityRowTailSplicedSourceFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedPrefixSplice
    (arithmeticValidityTailFixedOperandDelimiters W.machine.tm)
    (verifierValidityRowTailAffinePayloadFrames W input)

/-- Exact row-major splice semantics at the Cook--Levin specialization. -/
theorem verifierValidityRowTailSplicedSourceFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowTailSplicedSourceFrames W input =
      encodeUnaryFrameFixedPrefixSpliceOutputFamily
        (arithmeticValidityTailFixedOperandDelimiters W.machine.tm)
        (fun seed : ValidityRowSeed =>
          arithmeticValidityTailFixedOperandValues W.machine.tm
            seed.height seed.start seed.rowBase)
        (fun seed : ValidityRowSeed =>
          encodeAffineExactlyOneOutputSourceInvocationFamily
            (validityRowSeedOneHotFrames W.machine.tm seed).reverse)
        (verifierValidityRowSeeds W input) := by
  unfold verifierValidityRowTailSplicedSourceFrames
  rw [verifierValidityRowTailAffinePayloadFrames_eq_spliceInput]
  apply rewriteUnaryFrameFixedPrefixSplice_family
  · intro seed
    exact arithmeticValidityTailFixedOperandValues_length
      W.machine.tm seed.height seed.start seed.rowBase
  · intro seed symbol hsymbol
    exact affineExactlyOneOutputInvocationFamily_no_frameEnd _ symbol hsymbol

/-- End-to-end polynomial-time construction of the delimiter-bearing compact
validity-tail source rows from the raw verifier input. -/
noncomputable def
    verifierValidityRowTailSplicedSourceFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowTailSplicedSourceFrames W) := by
  let affineSource :=
    verifierValidityRowTailAffinePayloadFrames_computableInPolyTime W
  let spliceSource := unaryFrameFixedPrefixSplice_computableInPolyTime
    (arithmeticValidityTailFixedOperandDelimiters W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      affineSource spliceSource
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      rewriteUnaryFrameFixedPrefixSplice
        (arithmeticValidityTailFixedOperandDelimiters W.machine.tm)
        (verifierValidityRowTailAffinePayloadFrames W input))
  simpa [Function.comp_def] using Classical.choice composed

/-! ## Identification with the established compact tail source -/

private theorem encodeUnaryFrameWithFixedDelimiters_append
    (left right : List Nat) (leftDelimiters rightDelimiters :
      List UnaryFrameSym)
    (hlength : left.length = leftDelimiters.length) :
    encodeUnaryFrameWithFixedDelimiters (left ++ right)
        (leftDelimiters ++ rightDelimiters) =
      encodeUnaryFrameWithFixedDelimiters left leftDelimiters ++
        encodeUnaryFrameWithFixedDelimiters right rightDelimiters := by
  induction left generalizing leftDelimiters with
  | nil =>
      cases leftDelimiters with
      | nil => rfl
      | cons delimiter delimiters => simp at hlength
  | cons value values ih =>
      cases leftDelimiters with
      | nil => simp at hlength
      | cons delimiter delimiters =>
          simp only [List.length_cons] at hlength
          have hlength' : values.length = delimiters.length :=
            Nat.add_right_cancel hlength
          simp [encodeUnaryFrameWithFixedDelimiters,
            ih delimiters hlength', List.append_assoc]

/-- The eight fixed values and delimiters of one arithmetic stack are
byte-for-byte its established standalone compact invocation. -/
private theorem arithmeticValidityTailStackFixedEncoding_eq
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    let seed := arithmeticRuntimeStackSourceSeed tm H start rowBase k
    encodeUnaryFrameWithFixedDelimiters
        [seed.cellRight, seed.cellLeft, seed.cellBlank, seed.count,
          seed.maskStart, seed.maskBase + seed.count, 0, seed.count]
        arithmeticValidityTailStackOperandDelimiters =
      encodeAffineRuntimeStackStandaloneInvocation seed := by
  simp [arithmeticValidityTailStackOperandDelimiters,
    encodeUnaryFrameWithFixedDelimiters,
    encodeAffineRuntimeStackStandaloneInvocation,
    encodeAffineRuntimeStackSourceInvocation, encodeUnaryFrame,
    encodeUnaryFrameBlock, List.append_assoc]

/-- Materializing all fixed stack fields yields exactly the established
canonical stack-family source invocation. -/
private theorem arithmeticValidityTailStackFamilyFixedEncoding_eq
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    encodeUnaryFrameWithFixedDelimiters
        ((arithmeticRuntimeStackSourceSeeds tm H start rowBase).flatMap
          fun seed =>
            [seed.cellRight, seed.cellLeft, seed.cellBlank, seed.count,
              seed.maskStart, seed.maskBase + seed.count, 0, seed.count])
        ((arithmeticRuntimeStackSourceIndices tm).flatMap fun _ =>
          arithmeticValidityTailStackOperandDelimiters) =
      encodeAffineRuntimeStackStandaloneInvocationFamily
        (arithmeticRuntimeStackSourceSeeds tm H start rowBase) := by
  unfold arithmeticRuntimeStackSourceSeeds
  generalize arithmeticRuntimeStackSourceIndices tm = indices
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      simp only [List.map_cons, List.flatMap_cons,
        encodeAffineRuntimeStackStandaloneInvocationFamily]
      rw [encodeUnaryFrameWithFixedDelimiters_append]
      · rw [arithmeticValidityTailStackFixedEncoding_eq, ih]
      · simp [arithmeticValidityTailStackOperandDelimiters]

/-- The four final fixed values are exactly the fixed prefix of the existing
final-conjunction compact invocation. -/
private theorem arithmeticValidityTailFinalPrefixFixedEncoding_eq
    (tm : _root_.Turing.FinTM2) (H start : Nat) :
    encodeUnaryFrameWithFixedDelimiters
        [ arithmeticValidityFinalStart tm H start,
          H,
          arithmeticStackValidityStart tm H start,
          arithmeticHaltedMatchStart tm H start + 4 ]
        arithmeticValidityTailFinalPrefixDelimiters =
      encodeUnaryFrameBlock (arithmeticValidityFinalStart tm H start) ++
        encodeAffineStackOutputSourceInvocation
          { height := H
            base := arithmeticStackValidityStart tm H start } ++
        encodeUnaryFrameBlock
          (arithmeticHaltedMatchStart tm H start + 4) := by
  simp [arithmeticValidityTailFinalPrefixDelimiters,
    encodeUnaryFrameWithFixedDelimiters,
    encodeAffineStackOutputSourceInvocation, encodeUnaryFrame,
    encodeUnaryFrameBlock, List.append_assoc]

/-- One fully spliced arithmetic row is exactly the compact invocation
consumed by the already verified continuous validity-tail source. -/
private theorem arithmeticValidityTailSplicedRow_eq_sourceInvocation
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    encodeUnaryFrameWithFixedDelimiters
          (arithmeticValidityTailFixedOperandValues tm H start rowBase)
          (arithmeticValidityTailFixedOperandDelimiters tm) ++
        encodeAffineExactlyOneOutputSourceInvocationFamily
            (arithmeticRawOneHotFrames tm H start rowBase).reverse ++
          [.frameEnd] =
      encodeAffineValidityTailSourceInvocation
        (arithmeticValidityTailSourceFrame tm H start rowBase) := by
  unfold arithmeticValidityTailFixedOperandValues
    arithmeticValidityTailFixedOperandDelimiters
  rw [encodeUnaryFrameWithFixedDelimiters_append]
  · rw [arithmeticValidityTailStackFamilyFixedEncoding_eq,
      arithmeticValidityTailFinalPrefixFixedEncoding_eq]
    simp [encodeAffineValidityTailSourceInvocation,
      arithmeticValidityTailSourceFrame,
      arithmeticValidityFinalConjunctionSourceFrame,
      encodeAffineValidityFinalConjunctionSourceInvocation,
      List.append_assoc]
  · unfold arithmeticRuntimeStackSourceSeeds
    generalize arithmeticRuntimeStackSourceIndices tm = indices
    induction indices with
    | nil => rfl
    | cons index rest ih =>
        simp [arithmeticValidityTailStackOperandDelimiters, ih]

/-- Row-major compact invocations for the already verified continuous
validity-tail source. -/
noncomputable def verifierValidityRowTailSourceInvocationFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierValidityRowSeeds W input).flatMap fun seed =>
    encodeAffineValidityTailSourceInvocation
      (arithmeticValidityTailSourceFrame W.machine.tm
        seed.height seed.start seed.rowBase)

/-- The constructed spliced stream is byte-for-byte the established compact
tail-source invocation family. -/
theorem verifierValidityRowTailSplicedSourceFrames_eq_invocations
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowTailSplicedSourceFrames W input =
      verifierValidityRowTailSourceInvocationFrames W input := by
  rw [verifierValidityRowTailSplicedSourceFrames_eq_rows]
  unfold verifierValidityRowTailSourceInvocationFrames
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [encodeUnaryFrameFixedPrefixSpliceOutputFamily,
        List.flatMap_cons]
      rw [show
        encodeUnaryFrameWithFixedDelimiters
              (arithmeticValidityTailFixedOperandValues W.machine.tm
                seed.height seed.start seed.rowBase)
              (arithmeticValidityTailFixedOperandDelimiters W.machine.tm) ++
            encodeAffineExactlyOneOutputSourceInvocationFamily
                (validityRowSeedOneHotFrames W.machine.tm seed).reverse ++
              [.frameEnd] =
          encodeAffineValidityTailSourceInvocation
            (arithmeticValidityTailSourceFrame W.machine.tm
              seed.height seed.start seed.rowBase) by
        simpa [validityRowSeedOneHotFrames] using
          arithmeticValidityTailSplicedRow_eq_sourceInvocation
            W.machine.tm seed.height seed.start seed.rowBase]
      rw [ih]

/-- The raw verifier word polynomially computes the complete compact input
stream for every continuous validity-tail source invocation. -/
noncomputable def
    verifierValidityRowTailSourceInvocationFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowTailSourceInvocationFrames W) := by
  let source :=
    verifierValidityRowTailSplicedSourceFrames_computableInPolyTime W
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierValidityRowTailSplicedSourceFrames_eq_invocations W input]
          using source.outputsFun input }

/-! ## Continuous tail-family execution -/

/-- Typed verifier family consumed by the reusable continuous tail-source
wrapper. -/
noncomputable def verifierValidityRowTailSourceFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    AffineValidityTailSourceFamily
      (arithmeticRuntimeStackSourceBlankSteps W.machine.tm) :=
  { frames := (verifierValidityRowSeeds W input).map fun seed =>
      arithmeticValidityTailSourceFrame W.machine.tm
        seed.height seed.start seed.rowBase
    stack_lengths := by
      intro frame hframe
      rw [List.mem_map] at hframe
      rcases hframe with ⟨seed, hseed, rfl⟩
      exact arithmeticRuntimeStackSourceSeeds_length
        W.machine.tm seed.height seed.start seed.rowBase }

/-- The typed family encoding is exactly the compact invocation stream
constructed above from the raw verifier input. -/
theorem verifierValidityRowTailSourceFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineValidityTailSourceFamily
        (verifierValidityRowTailSourceFamily W input) =
      verifierValidityRowTailSourceInvocationFrames W input := by
  unfold encodeAffineValidityTailSourceFamily
  change encodeAffineValidityTailSourceInvocationFamily
      ((verifierValidityRowSeeds W input).map fun seed =>
        arithmeticValidityTailSourceFrame W.machine.tm
          seed.height seed.start seed.rowBase) = _
  unfold verifierValidityRowTailSourceInvocationFrames
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineValidityTailSourceInvocationFamily, ih]

/-- Executing the continuous compact source family yields exactly the
pre-existing canonical validity-tail operand stream. -/
theorem verifierValidityRowTailSourceFamilyStream_eq_operands
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    affineValidityTailSourceFamilyStream
        (arithmeticRuntimeStackSourceBlankSteps W.machine.tm)
        (verifierValidityRowTailSourceFamily W input).frames =
      verifierValidityRowTailOperandFrames W input := by
  change affineValidityTailSourceFamilyStream
      (arithmeticRuntimeStackSourceBlankSteps W.machine.tm)
      ((verifierValidityRowSeeds W input).map fun seed =>
        arithmeticValidityTailSourceFrame W.machine.tm
          seed.height seed.start seed.rowBase) = _
  unfold verifierValidityRowTailOperandFrames validityRowSeedTailFamily
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.map_cons, affineValidityTailSourceFamilyStream,
        List.flatMap_cons]
      rw [arithmeticValidityTailSourceFrame_eq, ih]
      rfl

/-- The raw verifier word polynomially computes all canonical post-halted
validity-row tail operands.  This closes the former gap between the
seed/one-hot compiler and the established continuous tail controller. -/
noncomputable def verifierValidityRowTailOperandFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowTailOperandFrames W) := by
  let invocationSource :=
    verifierValidityRowTailSourceInvocationFrames_computableInPolyTime W
  let typedInvocationSource :
      _root_.Turing.TM2ComputableInPolyTime id
        encodeAffineValidityTailSourceFamily
        (verifierValidityRowTailSourceFamily W) :=
    { tm := invocationSource.tm
      inputAlphabet := invocationSource.inputAlphabet
      outputAlphabet := invocationSource.outputAlphabet
      time := invocationSource.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierValidityRowTailSourceFamily_encoding_eq W input] using
          invocationSource.outputsFun input }
  let familySource := affineValidityTailSourceFamily_computableInPolyTime
    (arithmeticRuntimeStackSourceBlankSteps W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      typedInvocationSource familySource
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_def,
          verifierValidityRowTailSourceFamilyStream_eq_operands W input]
          using run }

end CLRS.Chapter34.Turing.CookLevin
