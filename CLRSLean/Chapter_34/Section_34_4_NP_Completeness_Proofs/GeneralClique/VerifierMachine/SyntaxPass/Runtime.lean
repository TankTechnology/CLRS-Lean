import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.SyntaxPass.Semantics

/-!
# General CLIQUE verifier: polynomial runtime of the syntax pass
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.SyntaxPass

open PolyBuilder
open _root_.Turing

/-- The fixed finite-state Boolean grammar checker runs in polynomial time on
raw certificate/instance pairs. -/
noncomputable def syntaxPassComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun pr : List CliqueSym × List CliqueSym => pairEncoding pr.1 pr.2)
      boolEncoding (fun pr => syntaxPass pr.1 pr.2) := by
  let raw := statefulFlatMap_computableInPolyTime syntaxSpec
  exact {
    tm := raw.tm
    inputAlphabet := raw.inputAlphabet
    outputAlphabet := raw.outputAlphabet
    time := raw.time
    outputsFun := fun pr => by
      have run := raw.outputsFun (pairEncoding pr.1 pr.2)
      have hstream :
          rewriteStatefulFlatMap syntaxSpec (pairEncoding pr.1 pr.2) =
            boolEncoding (syntaxPass pr.1 pr.2) := by
        simpa [syntaxPassStream] using
          syntaxPassStream_pairEncoding pr.1 pr.2
      simp only [id_eq] at run
      rw [hstream] at run
      simpa using run }

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.SyntaxPass
