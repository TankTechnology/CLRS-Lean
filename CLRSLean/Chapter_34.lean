import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.AndOr
import CLRSLean.Chapter_34.Section_34_2_Polynomial_Time_Verification
import CLRSLean.Chapter_34.Section_34_2_Polynomial_Time_Verification.PairProjection
import CLRSLean.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility
import CLRSLean.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility.Core
import CLRSLean.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility.Hardness
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CircuitSAT
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.Basic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.Encoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.Verification
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.Basic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.Steps
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.CertificatePhases
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.LookupPhases
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.Cleanup
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.CircuitPhases
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.CircuitRun
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.RejectSteps
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.RejectPhases
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.RejectBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.CircuitReject
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.BoundedReject
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.CanonicalRun
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.MalformedRun
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.MalformedBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.PolynomialRuntime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.NP
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SatTo3CNFSat
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SatTo3CNFMachine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CNFToClique
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CNFToCliqueMachine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Syntax
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Clock
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialClock
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryIndex
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.NatEncoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.InputGate
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.CircuitPrefix
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.BoolPool
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOne
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOne.AffineTrace
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOne.AffineRun
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOneFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneRowFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.EqFin
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionalEqFin
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.NotFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionalConjunctionFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.InputShapeController
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.VerifierTailController
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.VerifierBodyController
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.MuxFin
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OrFin
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Pop
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Statement
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatementController
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.DispatchController
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.TransitionScript
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.TransitionController
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.TransitionFamilyController
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.TransitionFamilyScript
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Narrowing
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OneHotMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OneHotPredicate
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OneHotPairMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.BoolEq
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.SuffixOr
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Not
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneOutputSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneOutputFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineStackOutputFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineValidityFinalConjunctionSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOnePrefixSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneHeightSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneCellProgressionSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStackSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStackFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStructuredRowSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStructuredRowFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryFrame
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryFrameFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryIndexFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryProgression
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialAffineUnaryProgression
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgression
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialAffineUnaryTripleProgression
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLoader
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Cell
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.CellFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Stack
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Conjunction
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ValidityTail
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineValidityTailRowFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineValidityTailStackFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ValidityRow
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ValidityRowFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.ReachableAlphabet
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Configuration
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.CircuitBuilder
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.CircuitBuilder.ConstantPool
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.CircuitBuilder.FiniteFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BundleCombinators
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StackPrimitives
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StackSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.FiniteLookup
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StackCircuits
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.ControlCircuits
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.PrimitiveRowSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.Validity
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.ValidityIndices
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.ValidityBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.Workspace
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StatementCircuits
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StatementCircuits.Core
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StatementCircuits.Trace
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StatementCircuits.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StatementCircuits.Bounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Dispatch
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Dispatch.Core
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Dispatch.Trace
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Dispatch.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Core
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Trace
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Bounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Fresh
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Fresh.At
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Fresh.Core
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Fresh.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Fresh.Witness
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BoundaryCircuits
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BoundaryCircuits.Static
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BoundaryCircuits.Initial
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BoundaryCircuits.Accepting
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BoundaryCircuits.Symbolic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.Finishing
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Witness
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Horizon
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauLayout
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauLayout.Core
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauLayout.Allocation
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauLayout.Assignment
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauWitness
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauConstraints
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauConstraints.ValidityFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauConstraints.TransitionFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauConstraints.TransitionFamilyTrace
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauConstraints.Families
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauConstraints.Witness
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.VerifierInput
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.VerifierInput.Support
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.VerifierInput.Arms
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.VerifierInput.Core
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.VerifierInput.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.VerifierInput.Semantics.Helpers
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly.Core
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly.Structure
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly.Evaluation
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly.Completeness
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly.Soundness
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly.Bounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly.EncodingBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorClock
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorHeader
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidity
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityOneHot
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityBoolEq
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityStack
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRow
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRows
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorFirstValidityHaltedFrame
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowIndices
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowAffineOperands
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowHaltedOperands
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowSeeds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowOneHotOperands
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowTailOperands
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransition
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInitialBoundary
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundary
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorAcceptingBoundary
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTail
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorBody
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorConjunction
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.ReductionMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Textbook

/-! # Chapter 34 — NP-Completeness

Chapter 34 of CLRS covers NP-completeness: the complexity classes **P** and
**NP**, polynomial-time reducibility, and NP-completeness.

This chapter formalizes the polynomial-time framework and the represented
NP-completeness reductions through Section 34.4.  It is built on Mathlib's
`Turing.TM2ComputableInPolyTime` (machine-level polynomial-time computability
with `Polynomial ℕ` time bounds).

## Sections

### 34.1 Polynomial Time

* `CLRS.Chapter34.Language` — a set of strings over an alphabet
* `CLRS.Chapter34.PolyTimeComputable` — a function computed by a TM2 machine
  in time bounded by a polynomial in the input length
* `CLRS.Chapter34.PolyTimeDecidable` — a language decided by a
  polynomial-time decision function
* `CLRS.Chapter34.ClassP` — the class of polynomial-time decidable languages

### 34.2 Polynomial-Time Verification

* `CLRS.Chapter34.pairEncoding` — encode a certificate/input pair as one string
* `CLRS.Chapter34.PolyTimeVerifiable` — a language verifiable by a
  polynomial-time verifier with polynomial-size certificates
* `CLRS.Chapter34.ClassNP` — the class of polynomially verifiable languages

### 34.3 NP-Completeness and Reducibility

* `CLRS.Chapter34.PolyTimeReducible` — `L₁ ≤_P L₂`, polynomial-time
  reducibility
* `CLRS.Chapter34.NPHard` / `NPComplete` — the NP-hard / NP-complete classes
* `CLRS.Chapter34.ClassNPC` — the class of NP-complete languages

**Status: `partial`** — the complete framework (languages, polytime,
class `P`, class `NP`, reducibility, NP-hard/NP-complete) is defined, and the
theorem layer is complete: composition, `P ⊆ NP`, transitivity of `≤_P`, and
the closure of `ClassP` under complement, union, and intersection.  Section
34.4 includes the concrete CIRCUIT-SAT → SAT and SAT → at-most-three-literal
3-CNF-SAT reductions, plus a reduction from 3-CNF-SAT to its specialized
occurrence-graph clique language.  The concrete
{lit}`Turing.TM3CNF.sat_reducible_to_threeCNFSat` machine theorem is sealed by
the Chapter 34 public interface.  The bounded-builder kernel now
includes verified scan/copy, symbol-local bounded-loop, and row-major
nested-loop macros, each with canonical exact independent and compiled runs;
their costs are respectively `3n + 3`, `2n + L + 3`, and
`2n² + 5n + L + 4`.  The Cook--Levin foundation now also extracts finite
reachable alphabets for fixed bundled machines, encodes canonical bounded
configurations without assuming the full work alphabets are finite, proves
exact-horizon stuttering equivalence, and establishes a uniform stack-height
bound that counts every push along a bundled statement path.  Canonical row
validity is now circuitized with exact decoding semantics and an exact gate
cost affine in the height bound.  Verified one-step workspace bridges now
widen and narrow row bundles with exact gate costs, overflow-fit semantics,
and successful-decoding preservation.  Widening now exposes its exact two-gate
Boolean constant pool for downstream reuse.  The circuit kernel also provides
finite-family mux and streaming equality with exact respective costs
`3n + 1` and `6n + 1`; canonical row flattening lifts these operations to
whole configuration bundles with exact costs `3w + 1` and `6w + 1`, where
the row width w denotes {lit}`cfgBitCount tm H`; typed stack views meanwhile
support zero-gate functional replacement.  Pure fixed-width stack push, peek,
and pop on raw Boolean bundles now have exact coordinate laws, supported-head
codec round trips, raw one-hot preservation under an explicit capacity
premise, and a full-stack overflow theorem.  These primitives do not yet prove
wire-level transition correctness by themselves.  Finite-family equality
additionally has one fixed runtime controller that
loads all wire indices from delimiter-bearing unary frames, emits the exact
true-seeded XNOR/aggregate-AND trace, and satisfies a linear input-length
runtime bound.  The corresponding runtime finite-family mux remains open.
Canonical Boolean stack encodings now carry exact list semantics: push is cons under
capacity, peek is head, pop is tail plus the old head, and every successful
whole-row evaluation projects to the corresponding represented machine stack.
Wire-level wrappers reuse a shared Boolean pool, keep push/peek zero-gate,
give positive-width pop exact one-OR cost, and compute capacity with one NOT,
while preserving complete-row frames.  The structural compiler
{lit}`compileStmt` covers all seven {lit}`TM2.Stmt` constructors—halt, goto,
load, push, peek, pop, and branch—using fixed finite truth tables.  Its
complete-row evaluation theorem is exactly {lit}`TM2.stepAux` under explicit
prefix capacity, and it publishes both an exact structural gate delta and a
fixed-machine/statement affine emitted-gate bound.  Finite program-label
dispatch now selects statements compiled against the same source row,
preserves the reserved-none stuttering case, and publishes exact complete-row
semantics and gate cost.  The local {lit}`transitionCircuit` widens into the
one-step workspace, dispatches, narrows under its internally checked fit bit,
compares the complete public target row, and accepts exactly
{lit}`stutterStep tm c`; its result records the exact total gate delta and a
fixed-machine affine emitted-gate bound.  Canonical row validity,
finite-label dispatch, and local transition construction now publish
height-independent coefficients, while finished validity and transition
wrappers are proved well formed and evaluation preserving.  The fresh-layout
layer now allocates consecutive nonaliasing rows at any external
input offset.  {lit}`freshTransitionCircuitAt_complete_nat` preserves an
arbitrary base assignment outside the two row intervals, while
{lit}`freshTransitionCircuit_complete` constructs the finite assignment used
by general-circuit satisfiability.  Exact boundary constraints now compare the
complete first/last row against canonical {lit}`initList`/{lit}`haltList`
targets, reject oversized or unsupported concrete targets with a real false
wire, and expose a symbolic-input-stack initial form for certificate-linked
assembly.  Whole-tableau circuitization now allocates every verifier row,
checks canonical validity and all adjacent stuttering steps, enforces bounded
certificate/input shape and exact endpoint rows, and closes a well-formed
general circuit.  Its satisfiability is equivalent to language membership and
its gate count, input count, and complete unary encoding length are controlled
by explicit fixed-verifier polynomials.  The exported function-level
`cookLevinMap` preserves language membership exactly and has a proved output-
length bound.  `GeneralCircuitSAT` also has an executable finite Boolean-
certificate checker whose bounded-certificate semantics is exact.  A concrete
TM2 computes that checker Boolean on every input; every successful, rejecting,
and malformed route is covered by one explicit quartic step polynomial.
Consequently `GeneralCircuitSAT` is now proved polynomially verifiable and a
member of `ClassNP`.  The explicit Cook--Levin map, semantic equivalence, and
polynomial output-length theorem are packaged for every NP language by
{lit}`cookLevin_textbookCircuitization`.  This is the semantic-and-size core of
the textbook construction, not an NP-hardness theorem: polynomial output
length alone does not prove polynomial-time computability.  The concrete
polynomial-time Cook--Levin generator TM2 remains the explicit bridge to the
standard {lit}`NPHard` and {lit}`NPComplete` predicates.  A general
graph-plus-{lit}`k` CLIQUE target and Section 34.5 remain unrepresented.

Theorem layer:

- `Turing.TM2ComputableInPolyTime.comp` (via `Turing.TM2Comp.comp_scratch`):
  composition of polynomial-time machines is polynomial-time (Mathlib leaves
  this as `proof_wanted`; closed here).  Unlocks `P ⊆ NP` and the transitivity
  of `PolyTimeReducible`.
- `PolyTimeDecidable.compl` / `ClassP_compl`: `P` is closed under complement.
- `PolyTimeDecidable.union` / `ClassP_union` and `PolyTimeDecidable.inter` /
  `ClassP_inter`: `P` is closed under union and intersection, via the AND/OR
  machine `Turing.TM2AndOr.andOrMachine` (which duplicates the input, runs both
  deciders, and combines with AND/OR).
- `ClassP_subset_ClassNP`: `P ⊆ NP` (Theorem 34.2).

Open problems (whether `P = NP`) and the Section 34.5 reductions such as
VERTEX-COVER, HAM-CYCLE, and SUBSET-SUM are intentionally out of scope for now.
-/

namespace CLRS

namespace Chapter34

end Chapter34

end CLRS
