import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.ComposedPreservation

/-!
# Non-root occupancy preservation for composed B-tree deletion

Raw {lit}`composedDelete` preserves non-root occupancy under the CLRS
descent-readiness guard.  Raw root deletion has a deliberately different
contract: it may produce an empty root with one child, so root callers must
apply {lit}`normalizeRoot` rather than expect raw root occupancy.
-/

namespace CLRS.Chapter18.BTree

/--
Raw composed deletion preserves non-root occupancy when the node starts with
at least {name}`t` keys.  This is the occupancy projection of
{name}`composedDelete_nonRoot_preserves`; the corresponding root operation is
{name}`composedDeleteRoot`, which normalizes the permitted one-child transient.
-/
lemma composedDelete_occupancy
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hinv : NodeWF t false tr) (hready : t ≤ numKeys tr) :
    Occupancy t false (composedDelete t x tr) :=
  (composedDelete_nonRoot_preserves t x ht hinv hready).2.1.occupancy

end CLRS.Chapter18.BTree
