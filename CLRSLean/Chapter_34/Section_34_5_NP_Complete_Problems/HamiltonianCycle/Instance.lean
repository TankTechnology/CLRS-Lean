import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding

/-!
# Finite undirected Hamiltonian-cycle instances

HAM-CYCLE reuses the chapter's normalized finite undirected graph structure.
The existing `targetSize` field is required to equal `vertexCount` by the raw
language, giving a canonical graph-only subgrammar without adding another
alphabet.  A cycle is represented by an ordered list of all vertices.
-/

namespace CLRS.Chapter34

abbrev HamiltonianCycleInstance := CliqueInstance
abbrev HamiltonianCycleSym := CliqueSym
abbrev encodeHamiltonianCycleInstance := encodeCliqueInstance
abbrev decodeHamiltonianCycleInstance := decodeCliqueInstance

namespace CliqueInstance

/-- Adjacency of every consecutive pair along a list path. -/
def PathAdjacent (I : CliqueInstance) : List Nat → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => I.Adj u v ∧ I.PathAdjacent (v :: rest)

/-- Last element of a nonempty list, expressed without proof arguments. -/
def lastFrom (current : Nat) : List Nat → Nat
  | [] => current
  | next :: rest => lastFrom next rest

/-- Every path edge and the closing last-to-first edge are present. -/
def CycleAdjacent (I : CliqueInstance) : List Nat → Prop
  | [] => False
  | first :: rest =>
      I.PathAdjacent (first :: rest) ∧ I.Adj (lastFrom first rest) first

/-- A list is a Hamiltonian cycle when it lists every vertex exactly once and
all path and closing edges exist.  Requiring at least three vertices matches
the textbook simple-cycle convention. -/
def ListRepresentsHamiltonianCycle
    (I : CliqueInstance) (vertices : List Nat) : Prop :=
  3 ≤ I.vertexCount ∧
    vertices.Nodup ∧
    vertices.length = I.vertexCount ∧
    (∀ v ∈ vertices, v < I.vertexCount) ∧
    I.CycleAdjacent vertices

/-- The graph has a Hamiltonian cycle. -/
def HasHamiltonianCycle (I : CliqueInstance) : Prop :=
  ∃ vertices, I.ListRepresentsHamiltonianCycle vertices

instance decidablePathAdjacent (I : CliqueInstance) :
    (vertices : List Nat) → Decidable (I.PathAdjacent vertices)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | u :: v :: rest =>
      match inferInstanceAs (Decidable (I.Adj u v)),
          decidablePathAdjacent I (v :: rest) with
      | isTrue huv, isTrue hrest => isTrue ⟨huv, hrest⟩
      | isFalse huv, _ => isFalse fun h => huv h.1
      | _, isFalse hrest => isFalse fun h => hrest h.2

instance decidableCycleAdjacent (I : CliqueInstance) (vertices : List Nat) :
    Decidable (I.CycleAdjacent vertices) := by
  cases vertices <;> simp only [CycleAdjacent] <;> infer_instance

instance decidableListRepresentsHamiltonianCycle
    (I : CliqueInstance) (vertices : List Nat) :
    Decidable (I.ListRepresentsHamiltonianCycle vertices) := by
  unfold ListRepresentsHamiltonianCycle
  infer_instance

end CliqueInstance
end CLRS.Chapter34
