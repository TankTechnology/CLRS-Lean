import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Instance

/-!
# The CLRS edge gadget for VERTEX-COVER to HAM-CYCLE

This file isolates the finite, local graph from Figure 34.16.  Vertices
`0,...,5` are the six ports on the left side and vertices `6,...,11` are the
six ports on the right side.  The ten vertical edges and four crossing edges
are listed explicitly, so later global numbering proofs do not depend on a
picture.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

/-- Local number of vertices in one CLRS edge gadget. -/
def widgetVertexCount : Nat := 12

/-- Local vertex number on one of the two six-vertex sides. -/
def widgetVertex (rightSide : Bool) (position : Nat) : Nat :=
  (if rightSide then 6 else 0) + position

/-- The fourteen normalized edges in the CLRS edge gadget. -/
def widgetEdges : List (Nat × Nat) :=
  [ (0, 1), (1, 2), (2, 3), (3, 4), (4, 5),
    (6, 7), (7, 8), (8, 9), (9, 10), (10, 11),
    (0, 8), (2, 6), (3, 11), (5, 9) ]

/-- The local gadget as an ordinary finite undirected graph. -/
def widgetInstance : CliqueInstance where
  vertexCount := widgetVertexCount
  targetSize := widgetVertexCount
  edges := widgetEdges

/-- The left six-vertex traversal used when both endpoints cover the source
edge. -/
def widgetLeftPath : List Nat := [0, 1, 2, 3, 4, 5]

/-- The right six-vertex traversal used when both endpoints cover the source
edge. -/
def widgetRightPath : List Nat := [6, 7, 8, 9, 10, 11]

/-- The all-vertex traversal whose external endpoints lie on the left side. -/
def widgetLeftFullPath : List Nat :=
  [0, 1, 2, 6, 7, 8, 9, 10, 11, 3, 4, 5]

/-- The all-vertex traversal whose external endpoints lie on the right side. -/
def widgetRightFullPath : List Nat :=
  [6, 7, 8, 0, 1, 2, 3, 4, 5, 9, 10, 11]

/-- A local path has distinct, in-range vertices and follows gadget edges. -/
def IsWidgetPath (vertices : List Nat) : Prop :=
  vertices.Nodup ∧
    (∀ v ∈ vertices, v < widgetVertexCount) ∧
    widgetInstance.PathAdjacent vertices

theorem widgetInstance_wellFormed : widgetInstance.WellFormed := by
  decide

theorem widgetEdges_length : widgetEdges.length = 14 := by
  rfl

theorem widgetLeftPath_isWidgetPath : IsWidgetPath widgetLeftPath := by
  norm_num [IsWidgetPath, widgetLeftPath, widgetVertexCount, widgetInstance,
    widgetEdges, CliqueInstance.PathAdjacent, CliqueInstance.Adj]

theorem widgetRightPath_isWidgetPath : IsWidgetPath widgetRightPath := by
  norm_num [IsWidgetPath, widgetRightPath, widgetVertexCount, widgetInstance,
    widgetEdges, CliqueInstance.PathAdjacent, CliqueInstance.Adj]

theorem widgetLeftFullPath_isWidgetPath : IsWidgetPath widgetLeftFullPath := by
  norm_num [IsWidgetPath, widgetLeftFullPath, widgetVertexCount, widgetInstance,
    widgetEdges, CliqueInstance.PathAdjacent, CliqueInstance.Adj]

theorem widgetRightFullPath_isWidgetPath : IsWidgetPath widgetRightFullPath := by
  norm_num [IsWidgetPath, widgetRightFullPath, widgetVertexCount, widgetInstance,
    widgetEdges, CliqueInstance.PathAdjacent, CliqueInstance.Adj]

theorem widgetLeftFullPath_length : widgetLeftFullPath.length = widgetVertexCount := by
  rfl

theorem widgetRightFullPath_length : widgetRightFullPath.length = widgetVertexCount := by
  rfl

theorem widgetLeftPath_append_rightPath_nodup :
    (widgetLeftPath ++ widgetRightPath).Nodup := by
  decide

theorem widgetLeftPath_append_rightPath_length :
    (widgetLeftPath ++ widgetRightPath).length = widgetVertexCount := by
  rfl

theorem mem_widgetLeftFullPath_iff (v : Nat) :
    v ∈ widgetLeftFullPath ↔ v < widgetVertexCount := by
  simp [widgetLeftFullPath, widgetVertexCount]
  omega

theorem mem_widgetRightFullPath_iff (v : Nat) :
    v ∈ widgetRightFullPath ↔ v < widgetVertexCount := by
  simp [widgetRightFullPath, widgetVertexCount]
  omega

theorem mem_widgetLeft_or_rightPath_iff (v : Nat) :
    v ∈ widgetLeftPath ∨ v ∈ widgetRightPath ↔ v < widgetVertexCount := by
  simp [widgetLeftPath, widgetRightPath, widgetVertexCount]
  omega

end CLRS.Chapter34.HamiltonianCycleReduction
