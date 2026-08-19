import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLoader

open StateTransition
open CLRS.Chapter34.Turing.PolyBuilder

#check UnaryTripleLoaderLabel
#check unaryTripleLoaderProgram
#check unaryTripleLoaderCfg
#check unaryTripleLoaderReadyCfg
#check unaryTripleLoaderSteps
#check unaryTripleLoader_run
#check unaryTripleLoaderProgramFor UnaryFrameSym
#check unaryTripleLoader_runFor (Δ := UnaryFrameSym)

#print axioms unaryTripleLoader_run
