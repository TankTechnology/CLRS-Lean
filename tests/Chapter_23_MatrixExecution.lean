import CLRSLean.FourthEdition.Chapter_23.MatrixExecution.Reindex
import CLRSLean.Audit.Axioms

open CLRS.Chapter24 CLRS.Chapter24.MatrixExecution

noncomputable def sample : Fin 2 → Fin 2 → WithTop ℝ :=
  fun i j => if i = j then 0 else if i = 0 then 3 else 4

-- Empty matrices do not create cells or evaluate candidates.
example : (square (fun _ _ : Fin 0 => (⊤ : WithTop ℝ)) 4).writes = 0 := by simp
example : (floyd (fun _ _ : Fin 0 => (⊤ : WithTop ℝ)) []).visits = 0 := by simp
-- Initialization plus two actual completed tables: twelve writes, eight updates.
example : (floyd sample [0, 1]).writes = 12 := by simp
example : (floyd sample [0, 1]).visits = 8 := by simp
example : (square sample 2).writes = 12 := by simp
example : (square sample 2).visits = 16 := by simp

example : read (floyd sample [0, 1]).table (0 : Fin 2) 1 = 3 := by
  rw [floyd_read]
  norm_num [WeightedGraph.floydFrom, sample]

-- Asymmetric entries and nontrivial minimum selection are retained in stored cells.
example : read (multiply 2 (initialRun sample).table (initialRun sample).table)
    (1 : Fin 2) 0 = 4 := by
  rw [multiply_read]
  norm_num [WeightedGraph.minPlusMul, Fin.sum_univ_two, Finset.univ_fin2, initialRun_read, sample]

-- Enumeration need not be the identity: compare the actual indexed output to the original matrix.
example (e : Fin 2 ≃ Fin 2) :
    read (floydOn e sample [0, 1]).table (e 0) (e 1) = 3 := by
  rw [floydOn_read]
  norm_num [WeightedGraph.floydFrom, sample]

example (t : Stored) : (diagonalScan 2 t).2 = 2 := diagonalScan_visits _ _

#assert_axioms multiply_read
#assert_axioms multiply_visits
#assert_axioms floyd_read
#assert_axioms square_read
#assert_axioms cycleFloydOn_shortest
#assert_axioms diagonalScan_negative_iff
#assert_axioms fasterOn_shortest
