import CLRSLean.FourthEdition.Chapter_23.Section_23_3_Johnsons_Algorithm.Execution

open CLRS.Chapter24
open WeightedGraph JohnsonExecution

#check johnsonStored
#check johnsonStored_read
#check johnsonStored_work_le
#check johnsonStored_row
#check sourceRow_width

namespace JohnsonExecutionTests

example : extractMin (fun x : Nat => (x : WithTop ℝ)) [] = (none, 0) := rfl
example : extractMin (fun x : Nat => (x : WithTop ℝ)) [3, 1, 2] =
    (some (1, [3, 2]), 3) := by norm_num [extractMin]
example : extractMin (fun _ : Nat => (0 : WithTop ℝ)) [3, 1, 2] =
    (some (3, [1, 2]), 3) := by norm_num [extractMin]

def empty : WeightedGraph (Fin 0) where
  edges := ∅
  w := fun _ _ => 0

example : (johnsonStored empty).rows = #[] := rfl
example : (johnsonStored empty).work = 4 := by
  simp [johnsonStored, sourceRows, prepare_work]

def single : WeightedGraph (Fin 1) where
  edges := ∅
  w := fun _ _ => 0

private theorem single_nonneg : single.Nonneg := by intro u v h; simp [single] at h
example : read (johnsonStored single) 0 0 = 0 := by
  rw [johnsonStored_eq_relaxDist single (single.noNegCycle_of_nonneg single_nonneg)]
  simp

-- A negative edge is valid because the directed graph has no nontrivial closed walk.
def negative : WeightedGraph (Fin 2) where
  edges := {(0, 1)}
  w := fun _ _ => -7

private theorem negative_noNegCycle : negative.NoNegCycle := by
  intro s p hp
  cases p with
  | nil => simp [walkWeight]
  | cons a p =>
    cases p with
    | nil => simp [walkWeight]
    | cons b p =>
      cases p with
      | nil =>
        have hab := hp.chain
        have has := hp.head
        have hbs := hp.last
        simp [WeightedGraph.Adj, negative] at hab
        simp at has hbs
        subst a
        subst b
        obtain ⟨h0, h1⟩ := hab
        omega
      | cons c p =>
        have hab := hp.chain
        simp only [List.isChain_cons_cons] at hab
        have h1 := hab.1
        have h2 := hab.2.1
        simp [WeightedGraph.Adj, negative] at h1 h2
        omega

example : read (johnsonStored negative) 0 1 = (-7 : WithTop ℝ) := by
  rw [johnsonStored_eq_relaxDist negative negative_noNegCycle]
  have hp : negative.preds 1 = {0} := by decide
  simp only [relaxDist, relaxStep, hp, Finset.inf_singleton]
  norm_num [negative]

example : read (johnsonStored negative) 1 0 = ⊤ := by
  rw [johnsonStored_eq_relaxDist negative negative_noNegCycle]
  norm_num [relaxDist, relaxStep, preds, negative, Finset.univ_fin2]

example : read (johnsonStored negative) 0 0 = 0 := by
  rw [johnsonStored_eq_relaxDist negative negative_noNegCycle]
  norm_num [relaxDist, relaxStep, preds, negative, Finset.univ_fin2]

example : read (johnsonStored negative) 1 1 = 0 := by
  rw [johnsonStored_eq_relaxDist negative negative_noNegCycle]
  have hp : negative.preds 1 = {0} := by decide
  simp only [relaxDist, relaxStep, hp, Finset.inf_singleton]
  norm_num [negative]

example : (johnsonStored negative).rows.size = 2 := johnsonStored_size _
example : (johnsonStored negative).work ≤ 116 := by
  simpa using johnsonStored_work_le_polynomial negative

-- The preprocessing itself computes and stores the finite Johnson potentials.
example (v : Fin 2) : vecRead (potentialPhase negative).1 v =
    (negative.johnsonPotential negative_noNegCycle v : WithTop ℝ) :=
  potentialPhase_read _ _ _

example : (prepare negative).work = 66 := by simpa using prepare_work negative
example : (bfLoop (edgeTable negative (Equiv.refl _)) (0 : Fin 2) 1).2 = 12 := by simp

example (G : WeightedGraph (Fin n)) (hNC : G.NoNegCycle) (i j : Fin n) :
    G.IsShortestDist i j (read (johnsonStored G) i j) := johnsonStored_correct G hNC i j

#print axioms johnsonStored_correct
#print axioms johnsonStored_work_le
end JohnsonExecutionTests
