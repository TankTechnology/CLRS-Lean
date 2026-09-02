import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveBranchSelectorSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames

/-!
# Raw-input coordinate rows for recursive branch muxes

The fresh coordinate triples of a fixed recursive branch form one affine
triple progression per transition seed.  A seven-form descriptor table and
the existing progression controller therefore generate the second marked
row of every recursive mux packet directly from the verifier input.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Runtime triple progression of one recursive branch's fresh mux
coordinates. -/
def transitionStmtRecursiveBranchCoordinateProgression
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    AffineUnaryTripleProgression :=
  let muxStart := affineUnaryTripleFormValue
    (transitionStmtBranchMuxStartForm tm labelOffset context test whenTrue
      whenFalse)
    (transitionTailAffineSeed seed)
  { base₁ := muxStart
    base₂ := muxStart + 1
    base₃ := muxStart + 2
    step₁ := 0
    step₂ := 3
    step₃ := 3
    count := cfgBitCount tm (workHeight tm seed.height) }

/-- The runtime progression enumerates the canonical branch coordinate row. -/
theorem transitionStmtRecursiveBranchCoordinateProgression_rows
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    affineUnaryTripleProgressionRows
        (transitionStmtRecursiveBranchCoordinateProgression tm seed
          labelOffset context test whenTrue whenFalse) =
      transitionStmtBranchMuxCoordinates tm seed labelOffset context test
        whenTrue whenFalse := by
  rw [affineUnaryTripleProgressionRows_eq_ofFn]
  unfold transitionStmtRecursiveBranchCoordinateProgression
    transitionStmtBranchMuxCoordinates
  apply List.ofFn_inj.mpr
  funext coordinate
  simp
  omega

/-- Seven fixed affine forms describing one recursive branch coordinate
progression. -/
def transitionStmtRecursiveBranchCoordinateDescriptorForms
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    List AffineUnaryTripleForm :=
  let start := transitionStmtBranchMuxStartForm tm labelOffset context test
    whenTrue whenFalse
  [ start,
    transitionAffineFormAddConst start 1,
    transitionAffineFormAddConst start 2,
    transitionDispatchHeightForm (TransitionAffineNat.const 0),
    transitionDispatchHeightForm (TransitionAffineNat.const 3),
    transitionDispatchHeightForm (TransitionAffineNat.const 3),
    transitionDispatchHeightForm
      ((transitionCfgBitAffine tm).shiftInput (maxPushesPerStep tm)) ]

/-- Evaluating the fixed form table gives exactly the seven runtime
progression fields. -/
theorem transitionStmtRecursiveBranchCoordinateDescriptorForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    affineUnaryTripleMap
        (transitionStmtRecursiveBranchCoordinateDescriptorForms tm
          labelOffset context test whenTrue whenFalse)
        (transitionTailAffineSeed seed) =
      let progression := transitionStmtRecursiveBranchCoordinateProgression
        tm seed labelOffset context test whenTrue whenFalse
      [ progression.base₁, progression.base₂, progression.base₃,
        progression.step₁, progression.step₂, progression.step₃,
        progression.count ] := by
  simp [transitionStmtRecursiveBranchCoordinateDescriptorForms,
    transitionStmtRecursiveBranchCoordinateProgression,
    affineUnaryTripleMap, transitionAffineFormAddConst_value,
    transitionDispatchHeightForm_value, TransitionAffineNat.eval_shiftInput,
    workHeight]

/-- Raw seven-field descriptors for the recursive branch coordinate
progression at every transition seed. -/
noncomputable def verifierTransitionRecursiveBranchCoordinateDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    (transitionStmtRecursiveBranchCoordinateDescriptorForms W.machine.tm
      labelOffset context test whenTrue whenFalse) input

/-- The raw affine image is exactly the structured progression-family
encoding consumed by the generic controller. -/
theorem verifierTransitionRecursiveBranchCoordinateDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ) :
    verifierTransitionRecursiveBranchCoordinateDescriptorFrames W labelOffset
        context test whenTrue whenFalse input =
      encodeAffineUnaryTripleProgressionFamily
        ((verifierTransitionRowSeeds W input).map fun seed =>
          transitionStmtRecursiveBranchCoordinateProgression W.machine.tm seed
            labelOffset context test whenTrue whenFalse) := by
  unfold verifierTransitionRecursiveBranchCoordinateDescriptorFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily encodeUnaryFrame
  rw [List.flatMap_map]
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons, List.map_cons,
        encodeAffineUnaryTripleProgressionFamily]
      rw [transitionStmtRecursiveBranchCoordinateDescriptorForms_value]
      rw [List.flatMap_append, ih]
      rfl

/-- Marked coordinate rows produced by executing one progression per seed. -/
noncomputable def verifierTransitionRecursiveBranchCoordinateFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFixedGroupFrameStream 0
    ((verifierTransitionRowSeeds W input).map fun seed =>
      transitionStmtRecursiveBranchCoordinateProgression W.machine.tm seed
        labelOffset context test whenTrue whenFalse)

private theorem recursiveBranchCoordinate_encodeUnaryFrame_frameEnd_free
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values, symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  rw [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, _, hblock⟩
  simp [encodeUnaryFrameBlock] at hblock
  rcases hblock with ⟨_, rfl⟩ | rfl <;> simp

/-- One marked fresh-coordinate row per transition seed. -/
noncomputable def verifierTransitionRecursiveBranchCoordinateFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  { rows := (verifierTransitionRowSeeds W input).map fun seed =>
      transitionDispatchMuxCoordinateRowFrames
        (transitionStmtBranchMuxCoordinates W.machine.tm seed labelOffset
          context test whenTrue whenFalse)
    frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      unfold transitionDispatchMuxCoordinateRowFrames at hsymbol
      rw [List.mem_flatMap] at hsymbol
      rcases hsymbol with ⟨coordinate, hcoordinate, hencoded⟩
      exact recursiveBranchCoordinate_encodeUnaryFrame_frameEnd_free _ symbol
        hencoded }

/-- The typed coordinate family is exactly the marked progression output. -/
theorem verifierTransitionRecursiveBranchCoordinateFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ) :
    encodeUnaryFrameMarkedRowFamily
        (verifierTransitionRecursiveBranchCoordinateFamily W labelOffset
          context test whenTrue whenFalse input) =
      verifierTransitionRecursiveBranchCoordinateFrames W labelOffset context
        test whenTrue whenFalse input := by
  unfold encodeUnaryFrameMarkedRowFamily
    verifierTransitionRecursiveBranchCoordinateFamily
    verifierTransitionRecursiveBranchCoordinateFrames
  rw [affineUnaryTripleProgressionFixedGroupZeroFrameStream_eq]
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  unfold affineUnaryTripleProgressionFrameStream
    transitionDispatchMuxCoordinateRowFrames
  rw [transitionStmtRecursiveBranchCoordinateProgression_rows]
  rfl

/-- The marked coordinate channel is generated by a concrete fixed
polynomial-time TM2 from the original verifier word. -/
noncomputable def
    verifierTransitionRecursiveBranchCoordinateFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionRecursiveBranchCoordinateFamily W labelOffset context
        test whenTrue whenFalse) := by
  let descriptors := verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionStmtRecursiveBranchCoordinateDescriptorForms W.machine.tm
      labelOffset context test whenTrue whenFalse)
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (fun input => (verifierTransitionRowSeeds W input).map fun seed =>
        transitionStmtRecursiveBranchCoordinateProgression W.machine.tm seed
          labelOffset context test whenTrue whenFalse) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        change _root_.Turing.TM2OutputsInTime descriptors.tm
            (List.map descriptors.inputAlphabet.invFun input)
            (some (List.map descriptors.outputAlphabet.invFun
              (verifierTransitionRecursiveBranchCoordinateDescriptorFrames W
                labelOffset context test whenTrue whenFalse input)))
            (descriptors.time.eval input.length) at run
        rw [verifierTransitionRecursiveBranchCoordinateDescriptorFrames_eq W
          input labelOffset context test whenTrue whenFalse] at run
        exact run }
  let executed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      (affineUnaryTripleProgressionFixedGroupFrameStream_computableInPolyTime 0)
  let source := Classical.choice executed
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        have run := source.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionRecursiveBranchCoordinateFrames,
          verifierTransitionRecursiveBranchCoordinateFamily_encoding_eq W
            input labelOffset context test whenTrue whenFalse] using run }

end CLRS.Chapter34.Turing.CookLevin
