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
