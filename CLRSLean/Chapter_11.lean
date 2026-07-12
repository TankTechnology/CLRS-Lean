import CLRSLean.Chapter_11.Section_11_1_Direct_Address_Tables
import CLRSLean.Chapter_11.Section_11_2_Chained_Hash_Tables
import CLRSLean.Chapter_11.Section_11_3_Hash_Functions

/-!
# Chapter 11 - Hash Tables

Chapter 11 introduces direct-address tables and hash tables.  The current
CLRS-Lean pass separates deterministic table correctness from probabilistic
performance analysis.  Section 11.2 now includes a finite-uniform bucket
interface: when the searched bucket is uniformly distributed, expected chain
length is exactly the load factor, and one insertion increases load factor and
unsuccessful-search cost by {lit}`1/m`.

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
  {lit}`CLRS.Chapter11.uniformAverageFin_add`,
  {lit}`CLRS.Chapter11.uniformAverageFin_nonneg`,
  {lit}`CLRS.Chapter11.finiteHashLoadFactor_nonneg`,
  {lit}`CLRS.Chapter11.expectedSearchChainLength_eq_loadFactor`,
  {lit}`CLRS.Chapter11.expectedSearchChainLength_nonneg`,
  {lit}`CLRS.Chapter11.expectedUnsuccessfulSearchCost_eq_one_plus_loadFactor`,
  {lit}`CLRS.Chapter11.expectedUnsuccessfulSearchCost_ge_one`,
  {lit}`CLRS.Chapter11.expectedSearchChainLength_finiteHashInsert`,
  {lit}`CLRS.Chapter11.finiteHashLoadFactor_finiteHashInsert`,
  {lit}`CLRS.Chapter11.expectedUnsuccessfulSearchCost_finiteHashInsert`,
  {lit}`CLRS.Chapter11.expectedRandomChainLength_eq_loadFactor`,
  {lit}`CLRS.Chapter11.expectedRandomUnsuccessfulSearchCost`,
  {lit}`CLRS.Chapter11.pairCollisionProb`,
  {lit}`CLRS.Chapter11.expectedRandomSuccessfulSearchCost`,
  {lit}`CLRS.Chapter11.universal_expected_collisions`,
  and {lit}`CLRS.Chapter11.universal_expected_search_cost`.
* 11.3 Hash functions: {lit}`proved`.
  Main results: {lit}`CLRS.Chapter11.divisionHash_lt`,
  {lit}`CLRS.Chapter11.multiplicationHash_lt`,
  {lit}`CLRS.Chapter11.affineHash_isUniversal`,
  {lit}`CLRS.Chapter11.affineHash_expected_collisions`,
  and {lit}`CLRS.Chapter11.affineHash_expected_search_cost`.

## Current Gaps

The deterministic insert/delete/search layer is compiler-clean, and the
finite-uniform bucket layer proves the load-factor, nonnegativity, and
single-insert expected-cost interfaces.  The SUHA layer proves the expected
chain length, unsuccessful-search cost {lit}`1 + α`, and successful-search cost
{lit}`1 + (n-1)/(2m)` as true expectations, and a universal random-hash-*function*
family bounds expected collisions by {lit}`α` and search cost by {lit}`1 + α`.
Section 11.3 supplies a concrete universal family (the prime-field affine family
{lit}`h_{a,b}(k) = a * k + b`) that discharges the {lit}`IsUniversal` hypothesis,
so the universal-hashing bounds are no longer conditional.  The remaining gap is
RAM / probe-count operational semantics.
-/

namespace CLRS
namespace Chapter11
end Chapter11
end CLRS
