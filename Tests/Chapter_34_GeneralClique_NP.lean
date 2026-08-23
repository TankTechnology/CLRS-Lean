import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.NP

/-!
# Regression test: concrete general CLIQUE NP membership
-/

open CLRS Chapter34
open CLRS.Chapter34.Turing.GeneralCliqueVerifier

#check concreteCliqueVerifier_eq_cliqueVerifier
#check cliqueVerifierComputableInPolyTime
#check generalCliqueVerifierRuntimePolynomial
#check generalCliqueVerifierMachine
#check generalCliqueVerifierMachine_outputs
#check generalCLIQUE_polyTimeVerifiable
#check generalCLIQUE_mem_ClassNP
