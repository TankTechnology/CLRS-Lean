import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorFinalConstraintBoundarySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowOrderReverse
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgressionRowUnmark

/-!
# Complete raw-input source for final conjunction wires

The validity, transition, and boundary sources are first concatenated in the
public semantic order.  A verified marked-row pass then reverses row order
without reversing any unary block, exactly matching the tail-first
conjunction controller's input convention.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- All constraint-output unary blocks in public semantic order. -/
def verifierConstraintOutputSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierValidityOutputSource W input ++
    verifierTransitionOutputSource W input ++
    verifierBoundaryOutputSource W input

/-- The joined forward source is exactly the collected constraint list. -/
theorem verifierConstraintOutputSource_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierConstraintOutputSource W input =
      encodeAffineConjunctionSources
        (verifierConstraintWires W input) := by
  rw [verifierConstraintOutputSource,
    verifierValidityOutputSource_eq,
    verifierTransitionOutputSource_eq,
    verifierBoundaryOutputSource_eq]
  unfold verifierConstraintWires encodeAffineConjunctionSources
  simp only [List.flatMap_append, List.append_assoc]

/-- A fixed polynomial-time TM2 emits the complete forward source list. -/
noncomputable def verifierConstraintOutputSource_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierConstraintOutputSource W) := by
  letI : Fintype Γ := W.alphabetFintype
  let validity := verifierValidityOutputSource_computableInPolyTime W
  let transitions := verifierTransitionOutputSource_computableInPolyTime W
  let first := unaryFrameSameInputConcat_computableInPolyTime
    validity transitions
  let boundary := verifierBoundaryOutputSource_computableInPolyTime W
  let complete := unaryFrameSameInputConcat_computableInPolyTime first boundary
  simpa [verifierConstraintOutputSource, List.append_assoc] using complete

/-- Marked one-wire rows for the semantic constraint list. -/
def verifierConstraintOutputMarkedFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  unaryFrameFullValueMarkedRows (verifierConstraintWires W input)

/-- The marked source obtained from the forward compiler has the advertised
typed family. -/
theorem verifierConstraintOutputMarkedSource_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    markUnaryFrameFixedFieldRows 1
        (verifierConstraintOutputSource W input) =
      encodeUnaryFrameMarkedRowFamily
        (verifierConstraintOutputMarkedFamily W input) := by
  rw [verifierConstraintOutputSource_eq]
  unfold encodeAffineConjunctionSources encodeUnaryFrame
  exact markUnaryFrameSingleFieldRows_encode
    (verifierConstraintWires W input)

/-- Same one-wire rows in the tail-first order consumed by conjunction. -/
def verifierConstraintOutputReversedFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  { rows := (verifierConstraintOutputMarkedFamily W input).rows.reverse
    frameEnd_free := by
      intro row hrow symbol hsymbol
      exact (verifierConstraintOutputMarkedFamily W input).frameEnd_free row
        (by simpa using hrow) symbol hsymbol }

/-- Row-order reversal produces the exact typed reversed family. -/
theorem verifierConstraintOutputReversedFamily_encode
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameMarkedRowOrderReverse
        (verifierConstraintOutputMarkedFamily W input) =
      encodeUnaryFrameMarkedRowFamily
        (verifierConstraintOutputReversedFamily W input) := by
  rfl

/-- Marker-free tail-first unary blocks for the final conjunction. -/
def verifierConstraintOutputReversedSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unmarkAffineUnaryTripleProgressionRows
    (encodeUnaryFrameMarkedRowFamily
      (verifierConstraintOutputReversedFamily W input))

/-- The reversed source is byte-for-byte the conjunction source field. -/
theorem verifierConstraintOutputReversedSource_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierConstraintOutputReversedSource W input =
      encodeAffineConjunctionSources
        (verifierConstraintWires W input).reverse := by
  unfold verifierConstraintOutputReversedSource
    verifierConstraintOutputReversedFamily
    verifierConstraintOutputMarkedFamily
    unaryFrameFullValueMarkedRows encodeUnaryFrameMarkedRowFamily
  rw [unmarkAffineUnaryTripleProgressionRows_markedValues]
  unfold encodeAffineConjunctionSources encodeUnaryFrame
  simp only [List.reverse_map, List.flatten_map_singleton]

/-- The complete tail-first constraint source is generated by fixed
polynomial-time marking, row reversal, and marker erasure passes. -/
noncomputable def verifierConstraintOutputReversedSource_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierConstraintOutputReversedSource W) := by
  letI : Fintype Γ := W.alphabetFintype
  let forward := verifierConstraintOutputSource_computableInPolyTime W
  let markedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch forward
      (markUnaryFrameFixedFieldRows_computableInPolyTime 1)
  let markedRaw := Classical.choice markedExists
  have marked : _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierConstraintOutputMarkedFamily W) :=
    { tm := markedRaw.tm
      inputAlphabet := markedRaw.inputAlphabet
      outputAlphabet := markedRaw.outputAlphabet
      time := markedRaw.time
      outputsFun := fun input => by
        have run := markedRaw.outputsFun input
        simp only [Function.comp_def, id_eq] at run
        rw [verifierConstraintOutputMarkedSource_eq] at run
        exact run }
  let reversedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch marked
      unaryFrameMarkedRowOrderReverse_computableInPolyTime
  let reversedRaw := Classical.choice reversedExists
  have reversed : _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierConstraintOutputReversedFamily W) :=
    { tm := reversedRaw.tm
      inputAlphabet := reversedRaw.inputAlphabet
      outputAlphabet := reversedRaw.outputAlphabet
      time := reversedRaw.time
      outputsFun := fun input => by
        have run := reversedRaw.outputsFun input
        simp only [Function.comp_def, id_eq] at run
        rw [verifierConstraintOutputReversedFamily_encode] at run
        exact run }
  let unmarkedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch reversed
      unmarkAffineUnaryTripleProgressionRows_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unmarkAffineUnaryTripleProgressionRows
      (encodeUnaryFrameMarkedRowFamily
        (verifierConstraintOutputReversedFamily W input)))
  simpa only [Function.comp_def] using Classical.choice unmarkedExists

end CLRS.Chapter34.Turing.CookLevin
