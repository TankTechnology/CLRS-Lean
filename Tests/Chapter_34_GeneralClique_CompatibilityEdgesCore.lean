import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesIterations

open CLRS.Chapter34.Turing.PolyBuilder

namespace CLRS.Chapter34.Turing.TMClique

#check compatibilityEdgesProgram
#check occurrenceRowsCompatibleCode
#check compatibilityEdges_loadCanonicalRun
#check compatibilityEdges_currentRowRun
#check compatibilityEdges_priorClauseEqRun
#check compatibilityEdges_priorClauseLtRun
#check compatibilityEdges_priorClauseGtRun
#check compatibilityEdges_priorVariableEqRun
#check compatibilityEdges_priorVariableLtRun
#check compatibilityEdges_priorVariableGtRun
#check compatibilityEdges_priorClauseComparisonRun
#check compatibilityEdges_priorVariableComparisonRun
#check compatibilityEdges_priorRowRun
#check compatibilityEdges_priorRowsRun
#check compatibilityEdges_priorRowsDoneRun
#check compatibilityEdges_cleanupCurrentRun
#check compatibilityEdges_restoreTaggedRowRun
#check compatibilityEdges_restoreTaggedRowsRun
#check compatibilityEdges_emitFlaggedRowRun
#check compatibilityEdges_emitCompatibleEdgeRun
#check compatibilityEdges_emitPriorRowRun
#check compatibilityEdges_emitPriorRowsRun
#check compatibilityEdges_finishIterationRun
#check compatibilityEdges_outerIterationRun
#check compatibilityEdges_outerIterationsRun
#print axioms compatibilityEdges_currentRowRun
#print axioms compatibilityEdges_priorClauseEqRun
#print axioms compatibilityEdges_priorVariableEqRun
#print axioms compatibilityEdges_priorClauseComparisonRun
#print axioms compatibilityEdges_priorRowRun
#print axioms compatibilityEdges_priorRowsRun
#print axioms compatibilityEdges_cleanupCurrentRun
#print axioms compatibilityEdges_restoreTaggedRowRun
#print axioms compatibilityEdges_restoreTaggedRowsRun
#print axioms compatibilityEdges_emitFlaggedRowRun
#print axioms compatibilityEdges_emitCompatibleEdgeRun
#print axioms compatibilityEdges_emitPriorRowsRun
#print axioms compatibilityEdges_finishIterationRun
#print axioms compatibilityEdges_outerIterationRun
#print axioms compatibilityEdges_outerIterationsRun

private def runCompatibilityFuel : Nat →
    BuilderCfg compatibilityEdgesProgram → BuilderCfg compatibilityEdgesProgram
  | 0, cfg => cfg
  | fuel + 1, cfg =>
      match step compatibilityEdgesProgram cfg with
      | none => cfg
      | some next => runCompatibilityFuel fuel next

private def sampleFormula : CNF :=
  [[Literal.pos 0, Literal.neg 1], [Literal.pos 1], [Literal.neg 0]]

private def sampleResult := runCompatibilityFuel 10000
  (initialCfg compatibilityEdgesProgram
    (encodeIndexedOccurrenceRows sampleFormula))

example : sampleResult.output = encodeOccurrenceCliqueEdges sampleFormula := by
  native_decide

example : sampleResult.input = [] ∧ sampleResult.work₁ = [] ∧
    sampleResult.work₂ = [] ∧ sampleResult.counter₁ = [] ∧
    sampleResult.counter₂ = [] ∧ sampleResult.counter₃ = [] := by
  native_decide

end CLRS.Chapter34.Turing.TMClique
