import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Parse

/-!
# General CLIQUE verifier: parser/decoder agreement

This module connects the finite-state syntax front end to the previously fixed
complete decoders on arbitrary raw certificate and instance strings.
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier

private def certificateVerticesState : ParseMode :=
  { side := .certificate, grammar := .certificateVertices, valid := true }

private def certificateVertexState : ParseMode :=
  { side := .certificate, grammar := .certificateVertex, valid := true }

private def invalidCertificateVerticesState : ParseMode :=
  { side := .certificate
    grammar := .certificateVertices
    valid := false }

private def invalidCertificateStartState : ParseMode :=
  { side := .certificate
    grammar := .certificateStart
    valid := false }

private def invalidCertificateVertexState : ParseMode :=
  { side := .certificate
    grammar := .certificateVertex
    valid := false }

private def certificateAccepts (mode : ParseMode) : Prop :=
  mode.valid = true ∧ mode.grammar = .certificateVertices

private instance (mode : ParseMode) : Decidable (certificateAccepts mode) := by
  unfold certificateAccepts
  infer_instance

private theorem scanSymbols_invalid (mode : ParseMode)
    (hvalid : mode.valid = false) (input : List CliqueSym) :
    (scanSymbols mode input).valid = false := by
  induction input generalizing mode with
  | nil => simpa [scanSymbols] using hvalid
  | cons symbol rest ih =>
      simp only [scanSymbols, List.foldl_cons]
      apply ih
      simp [stepSymbol, hvalid]

private theorem scanSymbols_of_invalid (mode : ParseMode)
    (hvalid : mode.valid = false) (input : List CliqueSym) :
    scanSymbols mode input = mode := by
  induction input generalizing mode with
  | nil => rfl
  | cons symbol rest ih =>
      simp only [scanSymbols, List.foldl_cons]
      have hstep : stepSymbol mode symbol = mode := by
        simp [stepSymbol, hvalid]
      rw [hstep]
      exact ih mode hvalid

private theorem not_certificateAccepts_of_invalid (mode : ParseMode)
    (hvalid : mode.valid = false) (input : List CliqueSym) :
    ¬ certificateAccepts (scanSymbols mode input) := by
  intro haccepts
  have hinvalid := scanSymbols_invalid mode hvalid input
  exact Bool.false_ne_true (hinvalid.symm.trans haccepts.1)

private theorem certificateBodies_agree (input : List CliqueSym) :
    certificateAccepts (scanSymbols certificateVerticesState input) ↔
      ∃ vertices, decodeCliqueVertices input = some vertices := by
  apply decodeCliqueVertices.induct
    (motive_1 := fun input =>
      certificateAccepts (scanSymbols certificateVerticesState input) ↔
        ∃ vertices, decodeCliqueVertices input = some vertices)
    (motive_2 := fun vertex input =>
      certificateAccepts (scanSymbols certificateVertexState input) ↔
        ∃ vertices, decodeCliqueVertex vertex input = some vertices)
  all_goals
    simp_all [certificateAccepts, certificateVerticesState,
      certificateVertexState, scanSymbols, stepSymbol, grammarStep,
      decodeCliqueVertices, decodeCliqueVertex, scanSymbols_invalid]
  case case3 =>
    intro t hnil hmark
    cases t with
    | nil => exact (hnil rfl).elim
    | cons symbol rest =>
        cases symbol <;>
          simp_all [scanSymbols, stepSymbol, grammarStep]
        all_goals
          intro hvalid
          have hinvalid := scanSymbols_invalid
            invalidCertificateVerticesState rfl rest
          exact (Bool.false_ne_true (hinvalid.symm.trans hvalid)).elim
  case case7 =>
    intro t vertex htick hend
    cases t with
    | nil =>
        simp [scanSymbols, certificateVertexState, certificateAccepts]
    | cons symbol rest =>
        cases symbol <;>
          simp_all [scanSymbols, stepSymbol, grammarStep]
        all_goals
          change ¬ (scanSymbols
            invalidCertificateVertexState rest).grammar =
              ParseGrammar.certificateVertices
          rw [scanSymbols_of_invalid _ rfl rest]
          decide

private def instanceEdgesState : ParseMode :=
  { side := .instance, grammar := .instanceEdges, valid := true }

private def instanceEdgeLeftState : ParseMode :=
  { side := .instance, grammar := .instanceEdgeLeft, valid := true }

private def instanceEdgeRightState : ParseMode :=
  { side := .instance, grammar := .instanceEdgeRight, valid := true }

private def invalidInstanceEdgesState : ParseMode :=
  { side := .instance
    grammar := .instanceEdges
    valid := false }

private def invalidInstanceEdgeLeftState : ParseMode :=
  { side := .instance
    grammar := .instanceEdgeLeft
    valid := false }

private def invalidInstanceEdgeRightState : ParseMode :=
  { side := .instance
    grammar := .instanceEdgeRight
    valid := false }

private def instanceAccepts (mode : ParseMode) : Prop :=
  mode.valid = true ∧ mode.grammar = .instanceEdges

private theorem instanceEdges_agree (input : List CliqueSym) :
    instanceAccepts (scanSymbols instanceEdgesState input) ↔
      ∃ edges, decodeCliqueEdges input = some edges := by
  apply decodeCliqueEdges.induct
    (motive_1 := fun input =>
      instanceAccepts (scanSymbols instanceEdgesState input) ↔
        ∃ edges, decodeCliqueEdges input = some edges)
    (motive_2 := fun left input =>
      instanceAccepts (scanSymbols instanceEdgeLeftState input) ↔
        ∃ edges, decodeCliqueEdgeLeft left input = some edges)
    (motive_3 := fun left right input =>
      instanceAccepts (scanSymbols instanceEdgeRightState input) ↔
        ∃ edges, decodeCliqueEdgeRight left right input = some edges)
  all_goals
    simp_all [instanceAccepts, instanceEdgesState, instanceEdgeLeftState,
      instanceEdgeRightState, scanSymbols, stepSymbol, grammarStep,
      decodeCliqueEdges, decodeCliqueEdgeLeft, decodeCliqueEdgeRight]
  case case3 =>
    intro t hnil hmark
    cases t with
    | nil => exact (hnil rfl).elim
    | cons symbol rest =>
        cases symbol <;>
          simp_all [scanSymbols, stepSymbol, grammarStep]
        all_goals
          intro hvalid
          have hinvalid := scanSymbols_invalid invalidInstanceEdgesState rfl rest
          exact (Bool.false_ne_true (hinvalid.symm.trans hvalid)).elim
  case case6 =>
    intro t left htick hsep
    cases t with
    | nil =>
        simp [scanSymbols, instanceEdgeLeftState, instanceAccepts]
    | cons symbol rest =>
        cases symbol <;>
          simp_all [scanSymbols, stepSymbol, grammarStep]
        all_goals
          change ¬ (scanSymbols invalidInstanceEdgeLeftState rest).grammar =
            ParseGrammar.instanceEdges
          rw [scanSymbols_of_invalid _ rfl rest]
          decide
  case case10 =>
    intro t left right htick hend
    cases t with
    | nil =>
        simpa [scanSymbols] using hend
    | cons symbol rest =>
        cases symbol <;>
          simp_all [scanSymbols, stepSymbol, grammarStep]
        all_goals
          have hinvalid := scanSymbols_invalid
            invalidInstanceEdgeRightState rfl rest
          exact Bool.false_ne_true (hinvalid.symm.trans htick)

private theorem scan_consumeCliqueTicks (mode : ParseMode)
    (hstep : stepSymbol mode .tick = mode) (input : List CliqueSym) :
    scanSymbols mode input =
      scanSymbols mode (consumeCliqueTicks input).2 := by
  induction input with
  | nil => rfl
  | cons symbol rest ih =>
      cases symbol with
      | tick =>
          simp only [consumeCliqueTicks, scanSymbols, List.foldl_cons, hstep]
          simpa [scanSymbols] using ih
      | _ => rfl

private theorem consumeCliqueTicks_suffix_ne_tick (input rest : List CliqueSym) :
    (consumeCliqueTicks input).2 ≠ .tick :: rest := by
  induction input with
  | nil => simp [consumeCliqueTicks]
  | cons symbol tail ih =>
      cases symbol <;> simp_all [consumeCliqueTicks]

private theorem certificate_scan_agree (certificate : List CliqueSym) :
    certificateAccepts (scanSymbols initialParseMode certificate) ↔
      ∃ vertices, decodeCliqueCertificate certificate = some vertices := by
  cases certificate with
  | nil =>
      simp [certificateAccepts, scanSymbols, initialParseMode,
        decodeCliqueCertificate]
  | cons symbol rest =>
      cases symbol with
      | certificateMark =>
          simpa [scanSymbols, initialParseMode, stepSymbol, grammarStep,
            decodeCliqueCertificate, certificateVerticesState] using
            certificateBodies_agree rest
      | _ =>
          constructor
          · intro haccepts
            change certificateAccepts
              (scanSymbols invalidCertificateStartState rest) at haccepts
            exact (not_certificateAccepts_of_invalid _ rfl rest haccepts).elim
          · rintro ⟨vertices, hdecode⟩
            simp [decodeCliqueCertificate] at hdecode

private def instanceStartState : ParseMode :=
  { side := .instance, grammar := .instanceStart, valid := true }

private def instanceVertexCountState : ParseMode :=
  { side := .instance, grammar := .instanceVertexCount, valid := true }

private def instanceTargetSizeState : ParseMode :=
  { side := .instance, grammar := .instanceTargetSize, valid := true }

private def invalidInstanceStartState : ParseMode :=
  { side := .instance
    grammar := .instanceStart
    valid := false }

private def invalidInstanceVertexCountState : ParseMode :=
  { side := .instance
    grammar := .instanceVertexCount
    valid := false }

private def invalidInstanceTargetSizeState : ParseMode :=
  { side := .instance
    grammar := .instanceTargetSize
    valid := false }

private theorem not_instanceAccepts_of_invalid (mode : ParseMode)
    (hvalid : mode.valid = false) (input : List CliqueSym) :
    ¬ instanceAccepts (scanSymbols mode input) := by
  intro haccepts
  have hinvalid := scanSymbols_invalid mode hvalid input
  exact Bool.false_ne_true (hinvalid.symm.trans haccepts.1)

private theorem targetSizeField_agree (input : List CliqueSym) :
    instanceAccepts (scanSymbols instanceTargetSizeState input) ↔
      ∃ targetSize edgeInput edges,
        consumeCliqueTicks input =
          (targetSize, .fieldSep :: edgeInput) ∧
        decodeCliqueEdges edgeInput = some edges := by
  have hscan := scan_consumeCliqueTicks instanceTargetSizeState (by rfl) input
  generalize hfield : consumeCliqueTicks input = field at hscan ⊢
  rcases field with ⟨targetSize, suffix⟩
  rw [hscan]
  cases suffix with
  | nil =>
      simp [instanceAccepts, scanSymbols, instanceTargetSizeState]
  | cons symbol edgeInput =>
      cases symbol with
      | tick =>
          have hsuffix : (consumeCliqueTicks input).2 = .tick :: edgeInput :=
            congrArg Prod.snd hfield
          exact (consumeCliqueTicks_suffix_ne_tick input edgeInput hsuffix).elim
      | fieldSep =>
          change instanceAccepts (scanSymbols instanceEdgesState edgeInput) ↔ _
          rw [instanceEdges_agree]
          constructor
          · rintro ⟨edges, hdecode⟩
            exact ⟨targetSize, edgeInput, edges, rfl, hdecode⟩
          · rintro ⟨targetSize', edgeInput', edges, hpair, hdecode⟩
            cases hpair
            exact ⟨edges, hdecode⟩
      | _ =>
          constructor
          · intro haccepts
            change instanceAccepts
              (scanSymbols invalidInstanceTargetSizeState edgeInput) at haccepts
            exact (not_instanceAccepts_of_invalid _ rfl edgeInput haccepts).elim
          · rintro ⟨targetSize', edgeInput', edges, hpair, hdecode⟩
            cases hpair

private theorem vertexCountField_agree (input : List CliqueSym) :
    instanceAccepts (scanSymbols instanceVertexCountState input) ↔
      ∃ vertexCount afterVertices targetSize edgeInput edges,
        consumeCliqueTicks input =
          (vertexCount, .fieldSep :: afterVertices) ∧
        consumeCliqueTicks afterVertices =
          (targetSize, .fieldSep :: edgeInput) ∧
        decodeCliqueEdges edgeInput = some edges := by
  have hscan := scan_consumeCliqueTicks instanceVertexCountState (by rfl) input
  generalize hfield : consumeCliqueTicks input = field at hscan ⊢
  rcases field with ⟨vertexCount, suffix⟩
  rw [hscan]
  cases suffix with
  | nil =>
      simp [instanceAccepts, scanSymbols, instanceVertexCountState]
  | cons symbol afterVertices =>
      cases symbol with
      | tick =>
          have hsuffix : (consumeCliqueTicks input).2 = .tick :: afterVertices :=
            congrArg Prod.snd hfield
          exact (consumeCliqueTicks_suffix_ne_tick input afterVertices hsuffix).elim
      | fieldSep =>
          change instanceAccepts
            (scanSymbols instanceTargetSizeState afterVertices) ↔ _
          rw [targetSizeField_agree]
          constructor
          · rintro ⟨targetSize, edgeInput, edges, htarget, hdecode⟩
            exact ⟨vertexCount, afterVertices, targetSize, edgeInput, edges,
              rfl, htarget, hdecode⟩
          · rintro ⟨vertexCount', afterVertices', targetSize, edgeInput,
              edges, hpair, htarget, hdecode⟩
            cases hpair
            exact ⟨targetSize, edgeInput, edges, htarget, hdecode⟩
      | _ =>
          constructor
          · intro haccepts
            change instanceAccepts
              (scanSymbols invalidInstanceVertexCountState afterVertices) at haccepts
            exact (not_instanceAccepts_of_invalid _ rfl afterVertices haccepts).elim
          · rintro ⟨vertexCount', afterVertices', targetSize, edgeInput,
              edges, hpair, htarget, hdecode⟩
            cases hpair

private theorem instanceMarkedBody_agree (input : List CliqueSym) :
    instanceAccepts (scanSymbols instanceVertexCountState input) ↔
      ∃ I, decodeCliqueInstance (.instanceMark :: input) = some I := by
  rw [vertexCountField_agree]
  constructor
  · rintro ⟨vertexCount, afterVertices, targetSize, edgeInput, edges,
      hvertex, htarget, hedges⟩
    refine ⟨{ vertexCount := vertexCount
              targetSize := targetSize
              edges := edges }, ?_⟩
    simp [decodeCliqueInstance, hvertex, htarget, hedges]
  · rintro ⟨I, hdecode⟩
    generalize hvertex : consumeCliqueTicks input = vertexField at hdecode
    rcases vertexField with ⟨vertexCount, vertexSuffix⟩
    cases vertexSuffix with
    | nil => simp [decodeCliqueInstance, hvertex] at hdecode
    | cons separator afterVertices =>
        cases separator with
        | fieldSep =>
            generalize htarget : consumeCliqueTicks afterVertices =
              targetField at hdecode
            rcases targetField with ⟨targetSize, targetSuffix⟩
            cases targetSuffix with
            | nil =>
                simp [decodeCliqueInstance, hvertex, htarget] at hdecode
            | cons separator edgeInput =>
                cases separator with
                | fieldSep =>
                    generalize hedges : decodeCliqueEdges edgeInput =
                      edgeResult at hdecode
                    cases edgeResult with
                    | none =>
                        simp [decodeCliqueInstance, hvertex, htarget,
                          hedges] at hdecode
                    | some edges =>
                        simp [decodeCliqueInstance, hvertex, htarget,
                          hedges] at hdecode
                        cases hdecode
                        exact ⟨vertexCount, afterVertices, targetSize,
                          edgeInput, edges, rfl, htarget, hedges⟩
                | _ =>
                    simp [decodeCliqueInstance, hvertex, htarget] at hdecode
        | _ => simp [decodeCliqueInstance, hvertex] at hdecode

private theorem instance_scan_agree (input : List CliqueSym) :
    instanceAccepts (scanSymbols instanceStartState input) ↔
      ∃ I, decodeCliqueInstance input = some I := by
  cases input with
  | nil =>
      simp [instanceAccepts, scanSymbols, instanceStartState,
        decodeCliqueInstance]
  | cons symbol rest =>
      cases symbol with
      | instanceMark =>
          simpa [scanSymbols, instanceStartState, stepSymbol, grammarStep,
            decodeCliqueInstance, instanceVertexCountState] using
            instanceMarkedBody_agree rest
      | _ =>
          constructor
          · intro haccepts
            change instanceAccepts
              (scanSymbols invalidInstanceStartState rest) at haccepts
            exact (not_instanceAccepts_of_invalid _ rfl rest haccepts).elim
          · rintro ⟨I, hdecode⟩
            simp [decodeCliqueInstance] at hdecode

private theorem scanSymbols_side (mode : ParseMode) (input : List CliqueSym) :
    (scanSymbols mode input).side = mode.side := by
  induction input generalizing mode with
  | nil => rfl
  | cons symbol rest ih =>
      simp only [scanSymbols, List.foldl_cons]
      calc
        (List.foldl stepSymbol (stepSymbol mode symbol) rest).side =
            (stepSymbol mode symbol).side := by
              simpa [scanSymbols] using ih (stepSymbol mode symbol)
        _ = mode.side := stepSymbol_side mode symbol

private theorem stepSeparator_afterCertificate (certificate : List CliqueSym) :
    stepSeparator (scanSymbols initialParseMode certificate) =
      if certificateAccepts (scanSymbols initialParseMode certificate) then
        instanceStartState
      else
        invalidInstanceStartState := by
  have hside := scanSymbols_side initialParseMode certificate
  generalize hmode : scanSymbols initialParseMode certificate = mode at hside ⊢
  rcases mode with ⟨side, grammar, valid⟩
  simp [initialParseMode] at hside
  subst side
  cases valid <;> cases grammar <;>
    simp [certificateAccepts, stepSeparator, instanceStartState,
      invalidInstanceStartState]

/-- The finite-state syntax marker is exact on arbitrary raw inputs: it is
`syntaxOK` precisely when both pre-existing complete decoders succeed. -/
theorem parsePairStatus_eq_syntaxOK_iff
    (certificate input : List CliqueSym) :
    parsePairStatus certificate input = .syntaxOK ↔
      (∃ vertices, decodeCliqueCertificate certificate = some vertices) ∧
      ∃ I, decodeCliqueInstance input = some I := by
  unfold parsePairStatus
  dsimp only
  rw [stepSeparator_afterCertificate]
  by_cases hcertificate :
      certificateAccepts (scanSymbols initialParseMode certificate)
  · simp [hcertificate, instanceStartState]
    constructor
    · rintro ⟨hside, hvalid, hgrammar⟩
      exact ⟨(certificate_scan_agree certificate).mp hcertificate,
        (instance_scan_agree input).mp ⟨hvalid, hgrammar⟩⟩
    · rintro ⟨hcertificateDecode, hinstanceDecode⟩
      have haccepts := (instance_scan_agree input).mpr hinstanceDecode
      exact ⟨scanSymbols_side instanceStartState input,
        haccepts.1, haccepts.2⟩
  · simp [hcertificate, scanSymbols_of_invalid, invalidInstanceStartState]
    intro vertices hdecode I hinstance
    exact hcertificate ((certificate_scan_agree certificate).mpr
      ⟨vertices, hdecode⟩)

/-- Initial parser mode for a standalone graph-instance string. -/
def initialInstanceParseMode : ParseMode :=
  { side := .instance, grammar := .instanceStart, valid := true }

/-- Complete finite-state verdict for a standalone certificate string. -/
def certificateSyntaxAccepts (certificate : List CliqueSym) : Bool :=
  let final := scanSymbols initialParseMode certificate
  final.valid && decide (final.grammar = .certificateVertices)

/-- Complete finite-state verdict for a standalone graph-instance string. -/
def instanceSyntaxAccepts (input : List CliqueSym) : Bool :=
  let final := scanSymbols initialInstanceParseMode input
  final.valid && decide (final.grammar = .instanceEdges)

/-- Standalone certificate syntax agrees with the complete decoder on every
raw string. -/
theorem certificateSyntaxAccepts_eq_true_iff
    (certificate : List CliqueSym) :
    certificateSyntaxAccepts certificate = true ↔
      ∃ vertices, decodeCliqueCertificate certificate = some vertices := by
  simpa [certificateSyntaxAccepts, certificateAccepts] using
    certificate_scan_agree certificate

/-- Standalone instance syntax agrees with the complete decoder on every raw
string. -/
theorem instanceSyntaxAccepts_eq_true_iff (input : List CliqueSym) :
    instanceSyntaxAccepts input = true ↔
      ∃ I, decodeCliqueInstance input = some I := by
  simpa [instanceSyntaxAccepts, initialInstanceParseMode, instanceAccepts,
    instanceStartState] using instance_scan_agree input

end CLRS.Chapter34.Turing.GeneralCliqueVerifier
