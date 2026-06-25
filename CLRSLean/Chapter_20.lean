import CLRSLean.Chapter_20.Section_20_1_VEB_Universe
import CLRSLean.Chapter_20.Section_20_2_VEB_Tree

/-!
# Chapter 20 - van Emde Boas Trees

Chapter 20 starts with a first-pass van Emde Boas universe decomposition and a
finite-set specification model.  The current Lean surface proves high/low/index
arithmetic and the correctness of membership, extrema, successor, predecessor,
insert, and delete against a represented finite set, including empty-result
specifications for extrema, successor, and predecessor plus membership-,
extrema-, and neighbor-query-after-update specifications.

## Sections

* 20.1 Universe decomposition: {lit}`proved` for the first-pass side-length
  arithmetic.
  Main results:
  {lit}`CLRS.Chapter20.VEB.index_high_low`,
  {lit}`CLRS.Chapter20.VEB.high_lt`, and
  {lit}`CLRS.Chapter20.VEB.low_lt`.
* 20.2 Tree specification: {lit}`partial`.
  Main results:
  {lit}`CLRS.Chapter20.VEB.member_correct`,
  {lit}`CLRS.Chapter20.VEB.minimum_correct`,
  {lit}`CLRS.Chapter20.VEB.minimum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.maximum_correct`,
  {lit}`CLRS.Chapter20.VEB.maximum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.successor_correct`,
  {lit}`CLRS.Chapter20.VEB.successor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.predecessor_correct`,
  {lit}`CLRS.Chapter20.VEB.predecessor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_member_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_minimum_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_maximum_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_predecessor_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_member_iff`,
  {lit}`CLRS.Chapter20.VEB.delete_minimum_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_maximum_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_successor_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_predecessor_correct`, and
  {lit}`CLRS.Chapter20.VEB.operationDepth_linear`.

## Current Gaps

Recursive summary/cluster storage, word-RAM base cases, and a Chapter 3
asymptotic bridge for {lit}`O(log log u)` remain strengthening targets.
-/

namespace CLRS
namespace Chapter20
end Chapter20
end CLRS
