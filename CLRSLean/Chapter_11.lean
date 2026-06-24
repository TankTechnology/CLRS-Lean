import CLRSLean.Chapter_11.Section_11_1_Direct_Address_Tables
import CLRSLean.Chapter_11.Section_11_2_Chained_Hash_Tables

/-!
# Chapter 11 - Hash Tables

Chapter 11 introduces direct-address tables and hash tables.  The current
CLRSLean pass separates deterministic table correctness from probabilistic
performance analysis.

## Sections

* 11.1 Direct-address tables: `proved` for the functional table model.
  Main results: {lit}`CLRS.Chapter11.search_insert_same`,
  {lit}`CLRS.Chapter11.search_insert_other`,
  {lit}`CLRS.Chapter11.search_delete_same`.
* 11.2 Hash tables: `partial`.
  Main results: {lit}`CLRS.Chapter11.bucket_hashInsert_same`,
  {lit}`CLRS.Chapter11.hashSearch_hashInsert_self`,
  {lit}`CLRS.Chapter11.bucket_hashInsert_other`.

## Current Gaps

The expected-time analysis under simple uniform hashing is not yet formalized.
That requires a probability model over keys and hash functions, so it is kept
separate from the deterministic lookup-correctness layer.
-/

namespace CLRS
namespace Chapter11
end Chapter11
end CLRS
