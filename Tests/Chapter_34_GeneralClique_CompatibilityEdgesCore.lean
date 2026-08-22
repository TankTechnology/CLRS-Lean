import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesCurrent

open CLRS.Chapter34.Turing.PolyBuilder

namespace CLRS.Chapter34.Turing.TMClique

#check compatibilityEdgesProgram
#check occurrenceRowsCompatibleCode
#check compatibilityEdges_loadCanonicalRun
#check compatibilityEdges_currentRowRun
#print axioms compatibilityEdges_currentRowRun

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
