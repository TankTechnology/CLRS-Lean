import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_10

/-! # Chapter 10 flagship trust surface -/

#check CLRS.Chapter10.arrayPop_arrayPush
#check CLRS.Chapter10.arrayEnqueue_tail_wraps
#check CLRS.Chapter10.ofLCRS_toLCRS

#assert_axioms CLRS.Chapter10.arrayPop_arrayPush
#assert_axioms CLRS.Chapter10.arrayEnqueue_tail_wraps
#assert_axioms CLRS.Chapter10.ofLCRS_toLCRS

example :
    (CLRS.Chapter10.arrayPush 7
      ({ store := fun _ => 0, top := 0, capacity := 2 } : CLRS.Chapter10.ArrayStack Nat)).map
        (fun stack => stack.top) = some 1 := by
  decide

#assert_axioms CLRS.Chapter10.ArrayStack.empty_valid
#assert_axioms CLRS.Chapter10.ArrayQueue.empty_valid
#assert_axioms CLRS.Chapter10.arrayPush_preserves_valid
#assert_axioms CLRS.Chapter10.arrayPop_preserves_valid
#assert_axioms CLRS.Chapter10.arrayEnqueue_preserves_valid
#assert_axioms CLRS.Chapter10.arrayDequeue_preserves_valid
#assert_axioms CLRS.Chapter10.arrayEnqueue_valid_input
#assert_axioms CLRS.Chapter10.arrayDequeue_valid_input
#assert_axioms CLRS.Chapter10.listSearch_eq_none_iff
#assert_axioms CLRS.Chapter10.listSearch_eq_some_iff_firstIndex
