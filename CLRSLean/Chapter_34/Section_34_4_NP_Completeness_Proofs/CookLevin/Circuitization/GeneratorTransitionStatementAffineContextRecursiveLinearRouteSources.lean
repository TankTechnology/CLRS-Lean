import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextLinearResultFamily

/-!
# Concrete source availability for every recursive linear leaf

The preceding row-local theorem is uniformized over every verifier input and
then converted to an actual machine witness at every terminal node of the
fixed recursive plan.  This isolates the remaining problem as physical
source-stream assembly rather than leaf-route computability.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Every terminal result in a fixed plan satisfies its route bounds for all
raw verifier inputs and all transition-row seeds. -/
def TransitionStmtRecursivePlan.UniformLinearRouteBounds
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) :
    TransitionStmtRecursivePlan W.machine.tm → Prop
  | .terminal _ result => ∀ input seed,
      seed ∈ verifierTransitionRowSeeds W input →
        result.RouteBounds W.machine.tm seed labelOffset
  | .prefix _ continuation =>
      continuation.UniformLinearRouteBounds W labelOffset
  | .branch _ _ _ _ _ truePlan falsePlan =>
      truePlan.UniformLinearRouteBounds W labelOffset ∧
        falsePlan.UniformLinearRouteBounds W labelOffset

/-- Pointwise route bounds commute with the finite recursive plan shape. -/
theorem TransitionStmtRecursivePlan.uniformLinearRouteBounds_of_pointwise
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (plan : TransitionStmtRecursivePlan W.machine.tm)
    (hpointwise : ∀ input seed,
      seed ∈ verifierTransitionRowSeeds W input →
        plan.LinearRouteBounds W.machine.tm seed labelOffset) :
    plan.UniformLinearRouteBounds W labelOffset := by
  induction plan with
  | terminal forms result =>
      intro input seed hseed
      exact hpointwise input seed hseed
  | «prefix» forms continuation ih =>
      apply ih
      intro input seed hseed
      exact hpointwise input seed hseed
  | branch context test whenTrue whenFalse predicateForms truePlan
      falsePlan ihTrue ihFalse =>
      constructor
      · apply ihTrue
        intro input seed hseed
        exact (hpointwise input seed hseed).1
      · apply ihFalse
        intro input seed hseed
        exact (hpointwise input seed hseed).2

/-- Machine-level source witness at every terminal result in the plan. -/
def TransitionStmtRecursivePlan.LinearRouteSources
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) :
    TransitionStmtRecursivePlan W.machine.tm → Prop
  | .terminal _ result => Nonempty
      (_root_.Turing.TM2ComputableInPolyTime id
        encodeUnaryFrameMarkedRowFamily
        (verifierTransitionLinearResultRouteFamily W labelOffset result))
  | .prefix _ continuation =>
      continuation.LinearRouteSources W labelOffset
  | .branch _ _ _ _ _ truePlan falsePlan =>
      truePlan.LinearRouteSources W labelOffset ∧
        falsePlan.LinearRouteSources W labelOffset

/-- Uniform semantic bounds instantiate the concrete affine-span TM2 at every
terminal leaf. -/
theorem TransitionStmtRecursivePlan.linearRouteSources_of_uniformBounds
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (plan : TransitionStmtRecursivePlan W.machine.tm)
    (hbounds : plan.UniformLinearRouteBounds W labelOffset) :
    plan.LinearRouteSources W labelOffset := by
  induction plan with
  | terminal forms result =>
      exact ⟨verifierTransitionLinearResultRouteFamily_computableInPolyTime
        W labelOffset result hbounds⟩
  | «prefix» forms continuation ih =>
      exact ih hbounds
  | branch context test whenTrue whenFalse predicateForms truePlan
      falsePlan ihTrue ihFalse =>
      exact ⟨ihTrue hbounds.1, ihFalse hbounds.2⟩

/-- Every terminal leaf of a verifier label has route bounds uniformly over
all raw inputs. -/
theorem verifierTransitionRecursivePlan_uniformLinearRouteBounds
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ) :
    (transitionStmtRecursivePlan W.machine.tm labelOffset
      (TransitionStmtAffineContext.initial W.machine.tm)
      (W.machine.tm.m label)
      (stmtPushSet_program_subset W.machine.tm label)).UniformLinearRouteBounds
        W labelOffset := by
  apply TransitionStmtRecursivePlan.uniformLinearRouteBounds_of_pointwise
    W labelOffset
  intro input seed hseed
  exact verifierTransitionRecursivePlan_linearRouteBounds W input seed
    (verifierTransitionRowSeeds_height_eq W input seed hseed)
    labelOffset label

/-- Every terminal leaf of every fixed verifier label now has an actual
polynomial-time raw-input source machine. -/
theorem verifierTransitionRecursivePlan_linearRouteSources
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ) :
    (transitionStmtRecursivePlan W.machine.tm labelOffset
      (TransitionStmtAffineContext.initial W.machine.tm)
      (W.machine.tm.m label)
      (stmtPushSet_program_subset W.machine.tm label)).LinearRouteSources
        W labelOffset := by
  apply TransitionStmtRecursivePlan.linearRouteSources_of_uniformBounds
  exact verifierTransitionRecursivePlan_uniformLinearRouteBounds W
    labelOffset label

end CLRS.Chapter34.Turing.CookLevin
