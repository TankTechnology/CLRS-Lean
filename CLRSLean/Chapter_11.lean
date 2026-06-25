import CLRSLean.Chapter_11.Section_11_1_Direct_Address_Tables
import CLRSLean.Chapter_11.Section_11_2_Chained_Hash_Tables

/-!
# Chapter 11 - Hash Tables

Chapter 11 introduces direct-address tables and hash tables.  The current
CLRS-Lean pass separates deterministic table correctness from probabilistic
performance analysis.  Section 11.2 now includes a finite-uniform bucket
interface: when the searched bucket is uniformly distributed, expected chain
length is exactly the load factor.

## Sections

* 11.1 Direct-address tables: {lit}`proved` for the functional table model.
  Main results: {lit}`CLRS.Chapter11.search_insert_same`,
  {lit}`CLRS.Chapter11.search_insert_other`,
  {lit}`CLRS.Chapter11.search_delete_same`.
* 11.2 Hash tables: {lit}`partial`.
  Main results: {lit}`CLRS.Chapter11.bucket_hashInsert_same`,
  {lit}`CLRS.Chapter11.hashSearch_hashInsert_self`,
  {lit}`CLRS.Chapter11.hashSearch_hashInsert_iff`,
  {lit}`CLRS.Chapter11.hashSearch_hashDelete_self`,
  {lit}`CLRS.Chapter11.hashSearch_hashDelete_iff`,
  {lit}`CLRS.Chapter11.uniformAverageFin_indicator_singleton`,
  {lit}`CLRS.Chapter11.expectedSearchChainLength_eq_loadFactor`,
  {lit}`CLRS.Chapter11.expectedUnsuccessfulSearchCost_eq_one_plus_loadFactor`,
  and {lit}`CLRS.Chapter11.expectedSearchChainLength_finiteHashInsert`.

## Current Gaps

The deterministic insert/delete/search layer is compiler-clean, and the
finite-uniform bucket layer proves the first expected-chain-length interface.
The remaining probability gap is a full model over random keys or random hash
functions with independence assumptions.
-/

namespace CLRS
namespace Chapter11
end Chapter11
end CLRS
