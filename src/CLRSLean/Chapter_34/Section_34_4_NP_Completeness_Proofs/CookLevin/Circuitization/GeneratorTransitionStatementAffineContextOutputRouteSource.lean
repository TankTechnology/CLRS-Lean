import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveRoute
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextBranchRouteFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextLinearResultFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveLinearRouteBounds

/-!
# Concrete total output-route sources for arbitrary statements

Every statement has exactly one of two output representations: a normalized
linear route or the fresh row produced by its final branch mux.  Both cases
already have concrete raw-input compilers.  This module hides that split
behind one semantic marked-row family and supplies the corresponding fixed
polynomial-time TM2.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem outputRoute_encodeUnaryFrame_frameEnd_free
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values, symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  induction values with
  | nil => simp [encodeUnaryFrame] at hsymbol
  | cons value values ih =>
      simp only [encodeUnaryFrame, List.flatMap_cons] at hsymbol
      rw [List.mem_append] at hsymbol
      rcases hsymbol with hhead | htail
      · unfold encodeUnaryFrameBlock at hhead
        rw [List.mem_append] at hhead
        rcases hhead with htick | hseparator
        · have : symbol = UnaryFrameSym.tick :=
            List.eq_of_mem_replicate htick
          subst symbol
          decide
        · have : symbol = UnaryFrameSym.separator := by
            simpa using hseparator
          subst symbol
          decide
      · exact ih htail

private theorem unaryFrameMarkedRowFamily_eq_of_rows
    (left right : UnaryFrameMarkedRowFamily)
    (hrows : left.rows = right.rows) : left = right := by
  cases left with
  | mk leftRows leftFree =>
      cases right with
      | mk rightRows rightFree =>
          simp only at hrows
          subst rightRows
          rfl

/-- One semantic complete output-route row per verifier transition seed. -/
noncomputable def verifierTransitionStmtOutputRouteFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (q : _root_.Turing.TM2.Stmt W.machine.tm.Γ W.machine.tm.Λ
      W.machine.tm.σ)
    (hsupport : ∀ k, stmtPushSet W.machine.tm q k ⊆
      reachableAlphabet W.machine.tm k)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  { rows := (verifierTransitionRowSeeds W input).map fun seed =>
      encodeUnaryFrame
        (transitionStmtOutputRouteValues W.machine.tm seed labelOffset
          context q hsupport)
    frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      exact outputRoute_encodeUnaryFrame_frameEnd_free _ symbol hsymbol }

/-- In the linear case, the total family is definitionally the normalized
linear-result family at the encoding boundary. -/
theorem verifierTransitionStmtOutputRouteFamily_encoding_eq_linear
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (q : _root_.Turing.TM2.Stmt W.machine.tm.Γ W.machine.tm.Λ
      W.machine.tm.σ)
    (hsupport : ∀ k, stmtPushSet W.machine.tm q k ⊆
      reachableAlphabet W.machine.tm k)
    (result : TransitionStmtLinearResult W.machine.tm)
    (hresult : transitionStmtLinearResult W.machine.tm context q hsupport =
      some result) :
    encodeUnaryFrameMarkedRowFamily
        (verifierTransitionStmtOutputRouteFamily W labelOffset context q
          hsupport input) =
      encodeUnaryFrameMarkedRowFamily
        (verifierTransitionLinearResultRouteFamily W labelOffset result
          input) := by
  apply congrArg encodeUnaryFrameMarkedRowFamily
  apply unaryFrameMarkedRowFamily_eq_of_rows
  simp [verifierTransitionStmtOutputRouteFamily,
    verifierTransitionLinearResultRouteFamily,
    transitionStmtOutputRouteValues, hresult]

/-- In the branch case, the total family is the final-mux branch family at
the encoding boundary. -/
theorem verifierTransitionStmtOutputRouteFamily_encoding_eq_branch
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (q : _root_.Turing.TM2.Stmt W.machine.tm.Γ W.machine.tm.Λ
      W.machine.tm.σ)
    (hsupport : ∀ k, stmtPushSet W.machine.tm q k ⊆
      reachableAlphabet W.machine.tm k)
    (offset : TransitionAffineNat)
    (hlinear : transitionStmtLinearResult W.machine.tm context q hsupport =
      none)
    (hoffset : transitionStmtFinalBranchMuxOffsetAffine W.machine.tm q =
      some offset) :
    encodeUnaryFrameMarkedRowFamily
        (verifierTransitionStmtOutputRouteFamily W labelOffset context q
          hsupport input) =
      encodeUnaryFrameMarkedRowFamily
        (verifierTransitionStmtBranchRouteFamily W labelOffset context offset
          input) := by
  apply congrArg encodeUnaryFrameMarkedRowFamily
  apply unaryFrameMarkedRowFamily_eq_of_rows
  simp [verifierTransitionStmtOutputRouteFamily,
    verifierTransitionStmtBranchRouteFamily,
    transitionStmtOutputRouteValues, hlinear, hoffset]

/-- If every possible normalized result satisfies its affine-span endpoint
bounds, an arbitrary fixed statement's total semantic route has a concrete
polynomial-time raw-input source. -/
noncomputable def
    verifierTransitionStmtOutputRouteFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (q : _root_.Turing.TM2.Stmt W.machine.tm.Γ W.machine.tm.Λ
      W.machine.tm.σ)
    (hsupport : ∀ k, stmtPushSet W.machine.tm q k ⊆
      reachableAlphabet W.machine.tm k)
    (hbounds : ∀ input seed,
      seed ∈ verifierTransitionRowSeeds W input →
        ∀ result,
          transitionStmtLinearResult W.machine.tm context q hsupport =
              some result →
            result.RouteBounds W.machine.tm seed labelOffset) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionStmtOutputRouteFamily W labelOffset context q
        hsupport) := by
  cases hlinear : transitionStmtLinearResult W.machine.tm context q
      hsupport with
  | some result =>
      let source :=
        verifierTransitionLinearResultRouteFamily_computableInPolyTime W
          labelOffset result (fun input seed hseed =>
            hbounds input seed hseed result hlinear)
      exact
        { tm := source.tm
          inputAlphabet := source.inputAlphabet
          outputAlphabet := source.outputAlphabet
          time := source.time
          outputsFun := fun input => by
            simpa only [id_eq,
              verifierTransitionStmtOutputRouteFamily_encoding_eq_linear W
                input labelOffset context q hsupport result hlinear] using
              source.outputsFun input }
  | none =>
      cases hbranch : transitionStmtFinalBranchMuxOffsetAffine W.machine.tm q with
      | some offset =>
          let source :=
            verifierTransitionStmtBranchRouteFamily_computableInPolyTime W
              labelOffset context offset
          exact
            { tm := source.tm
              inputAlphabet := source.inputAlphabet
              outputAlphabet := source.outputAlphabet
              time := source.time
              outputsFun := fun input => by
                simpa only [id_eq,
                  verifierTransitionStmtOutputRouteFamily_encoding_eq_branch W
                    input labelOffset context q hsupport offset hlinear
                      hbranch] using source.outputsFun input }
      | none =>
          have hlinearIff :=
            transitionStmtLinearResult_isSome_iff_terminal W.machine.tm
              context q hsupport
          rw [hlinear] at hlinearIff
          have hnotTerminal :
              ¬ (transitionStmtTerminalLayout W.machine.tm q).isSome := by
            simpa using hlinearIff
          have hbranchSome :=
            (transitionStmtFinalBranchMuxOffsetAffine_isSome_iff
              W.machine.tm q).2 hnotTerminal
          rw [hbranch] at hbranchSome
          simp at hbranchSome

/-- Every complete output row of one fixed verifier program label is
concretely polynomial-time computable from the raw input word. -/
noncomputable def
    verifierTransitionLabelOutputRouteFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionStmtOutputRouteFamily W labelOffset
        (TransitionStmtAffineContext.initial W.machine.tm)
        (W.machine.tm.m label)
        (stmtPushSet_program_subset W.machine.tm label)) := by
  apply verifierTransitionStmtOutputRouteFamily_computableInPolyTime
  intro input seed hseed result hresult
  apply transitionStmtRecursiveContextPadding_linearResult_routeBounds
    W.machine.tm seed labelOffset
      (TransitionStmtAffineContext.initial W.machine.tm)
      (W.machine.tm.m label)
      (stmtPushSet_program_subset W.machine.tm label)
  · exact transitionStmtRecursiveContextPadding_initial_verifier W input seed
      (verifierTransitionRowSeeds_height_eq W input seed hseed) label
  · intro k
    simpa [TransitionStmtAffineContext.initial,
      transitionStmtStackActionPushCountFor] using
      stmtMaxPushes_le_maxPushesPerStep W.machine.tm label k
  · exact hresult

end CLRS.Chapter34.Turing.CookLevin
