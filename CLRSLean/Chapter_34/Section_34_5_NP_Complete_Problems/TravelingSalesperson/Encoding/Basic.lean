import CLRSLean.Chapter_34.BinaryNat
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Instance

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

/-- Proof-free row-major representation decoded from a finite word. -/
structure TSPData where
  vertexCount : Nat
  budget : Nat
  weights : List Nat
deriving DecidableEq, Repr

namespace TSPData

/-- The matrix contains exactly one weight for every ordered vertex pair. -/
def WellFormed (data : TSPData) : Prop :=
  data.weights.length = data.vertexCount * data.vertexCount

instance (data : TSPData) : Decidable data.WellFormed := by
  unfold WellFormed
  infer_instance

/-- Interpret a row-major record as the existing typed decision-TSP model.
Malformed short matrices use a zero fallback, but the raw language separately
requires `WellFormed`, so accepted instances never observe it. -/
def toInstance (data : TSPData) : TSPInstance where
  vertexCount := data.vertexCount
  budget := data.budget
  weight u v := data.weights.getD (u.val * data.vertexCount + v.val) 0

/-- Honest raw decision semantics. -/
def HasTour (data : TSPData) : Prop :=
  data.WellFormed ∧ data.toInstance.HasTour

end TSPData
end CLRS.Chapter34
