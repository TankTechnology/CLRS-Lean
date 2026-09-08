import CLRSLean.FourthEdition.Chapter_32.Section_32_3_Finite_Automata

/-!
# One constructed transition table and a counted scan

The table is an explicit scan parameter and is built once by the matcher.
Counters count table cells and transition requests only. Suffix search inside
{lit}`delta`, alphabet indexing and list-table lookup are not constant-time
operations in this representation, so these counts are not construction or
machine-runtime bounds.
-/
namespace CLRS.Chapter32.DFAExecution
variable {α : Type} [BEq α] [DecidableEq α] [LawfulBEq α]

structure Scan where
  positions : List Nat
  transitions : Nat

def scan (alphabet : List α) (table : List (List Nat)) (m : Nat) : Nat → Nat → Text α → Scan
  | processed, q, [] => ⟨if q == m then [processed-m] else [],0⟩
  | processed, q, c :: rest =>
    let next := transitionLookup alphabet table q c
    let tail := scan alphabet table m (processed+1) next rest
    ⟨if q == m then (processed-m)::tail.positions else tail.positions, tail.transitions+1⟩

omit [DecidableEq α] [LawfulBEq α] in
@[simp] theorem scan_transitions (alphabet : List α) (table : List (List Nat))
    (m processed q : Nat) (xs : Text α) :
    (scan alphabet table m processed q xs).transitions = xs.length := by
  induction xs generalizing processed q with
  | nil => rfl
  | cons c xs ih => simp [scan, ih]

omit [DecidableEq α] [LawfulBEq α] in
theorem scan_refines (alphabet : List α) (P : Text α) (m : Nat) (scanned : Text α)
    (q : Nat) (xs : Text α) :
    (scan alphabet (transitionTable alphabet P) m scanned.length q xs).positions =
      dfaScanTable alphabet P m scanned q xs := by
  induction xs generalizing scanned q with
  | nil => rfl
  | cons c xs ih =>
    simp only [scan, dfaScanTable]
    have h := ih (scanned ++ [c]) (transitionLookup alphabet (transitionTable alphabet P) q c)
    simpa using congrArg (fun tail => if q == m then (scanned.length-m)::tail else tail) h

structure Result where
  table : List (List Nat)
  positions : List Nat
  cells : Nat
  transitions : Nat

def execute (alphabet : List α) (P T : Text α) : Result :=
  let table := transitionTable alphabet P
  let output := scan alphabet table P.length 0 0 T
  ⟨table, output.positions, (table.map List.length).sum, output.transitions⟩

@[simp] theorem execute_transitions (alphabet : List α) (P T : Text α) :
    (execute alphabet P T).transitions = T.length := scan_transitions _ _ _ _ _ _

@[simp] theorem execute_cells (alphabet : List α) (P T : Text α) :
    (execute alphabet P T).cells = (P.length + 1) * alphabet.length :=
  transitionTableBuildCost_eq _ _

theorem execute_correct (alphabet : List α) (P T : Text α) (hT : ∀ c ∈ T, c ∈ alphabet) :
    (execute alphabet P T).positions = naiveMatcher T P := by
  have h := scan_refines alphabet P P.length [] 0 T
  change (scan alphabet (transitionTable alphabet P) P.length 0 0 T).positions = _
  exact h.trans (dfaMatcherTable_eq_naive alphabet P T hT)

end CLRS.Chapter32.DFAExecution
