# Chapter 20 - van Emde Boas Trees

- Status: `partial`
- Lean entry: `CLRSLean/Chapter_20.lean`
- Interface test: `Tests/Chapter_20_Interface.lean`

## Proved First-Pass Surface

- `CLRS.Chapter20.VEB.index_high_low`
- `CLRS.Chapter20.VEB.high_index`
- `CLRS.Chapter20.VEB.low_index`
- `CLRS.Chapter20.VEB.index_lt`
- `CLRS.Chapter20.VEB.high_lt`
- `CLRS.Chapter20.VEB.low_lt`
- `CLRS.Chapter20.VEB.member_correct`
- `CLRS.Chapter20.VEB.minimum_correct`
- `CLRS.Chapter20.VEB.minimum_none_iff`
- `CLRS.Chapter20.VEB.maximum_correct`
- `CLRS.Chapter20.VEB.maximum_none_iff`
- `CLRS.Chapter20.VEB.successor_correct`
- `CLRS.Chapter20.VEB.successor_none_iff`
- `CLRS.Chapter20.VEB.predecessor_correct`
- `CLRS.Chapter20.VEB.predecessor_none_iff`
- `CLRS.Chapter20.VEB.insert_correct`
- `CLRS.Chapter20.VEB.insert_member_iff`
- `CLRS.Chapter20.VEB.insert_minimum_correct`
- `CLRS.Chapter20.VEB.insert_maximum_correct`
- `CLRS.Chapter20.VEB.insert_successor_correct`
- `CLRS.Chapter20.VEB.insert_predecessor_correct`
- `CLRS.Chapter20.VEB.delete_correct`
- `CLRS.Chapter20.VEB.delete_member_iff`
- `CLRS.Chapter20.VEB.delete_minimum_correct`
- `CLRS.Chapter20.VEB.delete_maximum_correct`
- `CLRS.Chapter20.VEB.delete_successor_correct`
- `CLRS.Chapter20.VEB.delete_predecessor_correct`
- `CLRS.Chapter20.VEB.operationDepth_zero`
- `CLRS.Chapter20.VEB.operationDepth_succ`
- `CLRS.Chapter20.VEB.operationDepth_linear`

## Remaining Work

The current chapter proves side-length universe arithmetic, including bounded
high/low recomposition facts, and finite-set operation specifications.
It also records the first-pass operation-depth base and step recurrence facts.
Recursive summary/cluster state, word-RAM base cases, and a full `O(log log u)`
asymptotic bridge are still open.
