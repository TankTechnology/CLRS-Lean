import CLRSLean.Chapter_34.BinaryNat
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Instance
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding.PairOrder

/-!
# Raw finite syntax for decision-TSP
-/

namespace CLRS.Chapter34

/-- Finite alphabet shared by serialized TSP instances and certificates. -/
inductive TSPSym
  | instanceMark
  | certificateMark
  | numberMark
  | bit (value : Bool)
  | fieldEnd
  | recordEnd
deriving DecidableEq, Fintype, Repr

/-- Proof-free complete-matrix representation decoded from a finite word. -/
structure TSPData where
  vertexCount : Nat
  budget : Nat
  weights : List Nat
deriving DecidableEq, Repr

namespace TSPData

/-- Successive off-diagonal orientation fields carry the same undirected
weight.  A dangling final field is rejected. -/
def OrientationPairsEqual : List Nat → Prop
  | [] => True
  | [_] => False
  | forward :: reverse :: rest =>
      forward = reverse ∧ OrientationPairsEqual rest

/-- First orientation from every consecutive off-diagonal pair.  A dangling
field is retained so equality with `secondOrientations` rejects it. -/
def firstOrientations : List Nat → List Nat
  | [] => []
  | [value] => [value]
  | forward :: _ :: rest => forward :: firstOrientations rest

/-- Second orientation from every consecutive off-diagonal pair. -/
def secondOrientations : List Nat → List Nat
  | [] | [_] => []
  | _ :: reverse :: rest => reverse :: secondOrientations rest

theorem orientationPairsEqual_iff (weights : List Nat) :
    OrientationPairsEqual weights ↔
      firstOrientations weights = secondOrientations weights := by
  induction weights using List.twoStepInduction with
  | nil => simp [OrientationPairsEqual, firstOrientations, secondOrientations]
  | singleton value =>
      simp [OrientationPairsEqual, firstOrientations, secondOrientations]
  | cons_cons forward reverse rest ih _ =>
      simp [OrientationPairsEqual, firstOrientations, secondOrientations, ih]

instance (weights : List Nat) : Decidable (OrientationPairsEqual weights) := by
  induction weights using List.twoStepInduction with
  | nil => exact isTrue trivial
  | singleton value => exact isFalse id
  | cons_cons forward reverse rest _ ih =>
      simp only [OrientationPairsEqual]
      infer_instance

/-- The matrix contains exactly one weight for every ordered vertex pair and
the two orientations of every off-diagonal pair agree.  This is the standard
symmetric decision-TSP input model used by CLRS. -/
def WellFormed (data : TSPData) : Prop :=
  data.weights.length = data.vertexCount * data.vertexCount ∧
    OrientationPairsEqual (data.weights.drop data.vertexCount)

instance (data : TSPData) : Decidable data.WellFormed := by
  unfold WellFormed
  infer_instance

/-- Interpret the canonical complete-pair order as the existing typed
decision-TSP model.  Malformed short matrices use a zero fallback, but the raw
language separately requires `WellFormed`, so accepted instances never
observe it. -/
def toInstance (data : TSPData) : TSPInstance where
  vertexCount := data.vertexCount
  budget := data.budget
  weight u v := lookupTSPWeight (tspPairOrder data.vertexCount)
    data.weights u.val v.val

/-- Honest raw decision semantics. -/
def HasTour (data : TSPData) : Prop :=
  data.WellFormed ∧ data.toInstance.HasTour

end TSPData
end CLRS.Chapter34
