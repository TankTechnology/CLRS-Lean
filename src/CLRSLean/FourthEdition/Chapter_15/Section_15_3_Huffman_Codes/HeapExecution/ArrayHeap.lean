import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes.HeapExecution.Entry
import CLRSLean.FourthEdition.Chapter_06.Section_06_5_Priority_Queues.Insert.Basic

/-!
# List-backed binary heap execution

The executable array stores stamped Huffman entries.  A numeric rank is used only
for comparisons; the trees remain aligned with their cells through every
swap.  The proof layer maps the execution to Chapter 6's verified natural-key
max-heap operations.
-/

namespace CLRS.HuffmanV2

/-- Swap two cells in an arbitrary list-backed array. -/
def swapEntries {α : Type} (a : List α) (i j : Nat) : List α :=
  match a[i]?, a[j]? with
  | some ai, some aj => (a.set i aj).set j ai
  | _, _ => a

/-- Push one cell upward while its numeric rank exceeds its parent's rank. -/
def bubbleUpFuel (rank : HeapEntry → Nat) :
    Nat → List HeapEntry → Nat → Nat → List HeapEntry
  | 0, a, _heapSize, _i => a
  | fuel + 1, a, heapSize, i =>
      if _ : 0 < i then
        if CLRS.Chapter06.valAt (a.map rank) (CLRS.Chapter06.parent i) <
            CLRS.Chapter06.valAt (a.map rank) i then
          bubbleUpFuel rank fuel (swapEntries a i (CLRS.Chapter06.parent i))
            heapSize (CLRS.Chapter06.parent i)
        else
          a
      else
        a

/-- Push one cell downward toward the larger-ranked child. -/
def bubbleDownFuel (rank : HeapEntry → Nat) :
    Nat → List HeapEntry → Nat → Nat → List HeapEntry
  | 0, a, _heapSize, _i => a
  | fuel + 1, a, heapSize, i =>
      let largest := CLRS.Chapter06.maxChildIndex (a.map rank) heapSize i
      if largest = i then
        a
      else
        bubbleDownFuel rank fuel (swapEntries a i largest) heapSize largest

/-- Append an entry and execute the ordinary binary-heap upward repair. -/
def heapInsertRaw (rank : HeapEntry → Nat)
    (a : List HeapEntry) (e : HeapEntry) : List HeapEntry :=
  bubbleUpFuel rank a.length (a ++ [e]) (a.length + 1) a.length

/-- Extract the root, move the last cell to the root, and repair downward. -/
def heapExtractMaxRaw (rank : HeapEntry → Nat) :
    List HeapEntry → Option (HeapEntry × List HeapEntry)
  | [] => none
  | root :: rest =>
      let newSize := rest.length
      let moved := swapEntries (root :: rest) 0 newSize
      let active := moved.take newSize
      some (root, bubbleDownFuel rank newSize active newSize 0)

/-- Repeated insertion builds a heap while keeping the input element multiset. -/
def heapBuildRaw (rank : HeapEntry → Nat) (entries : List HeapEntry) :
    List HeapEntry :=
  entries.foldl (heapInsertRaw rank) []

/-- The concrete array satisfies the Chapter 6 max-heap predicate after ranking. -/
def IsRankHeap (rank : HeapEntry → Nat) (a : List HeapEntry) : Prop :=
  CLRS.Chapter06.ArrayMaxHeap (a.map rank) a.length

end CLRS.HuffmanV2
