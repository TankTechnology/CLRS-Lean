import CLRSLean.FourthEdition.Chapter_13.Section_13_2_Rotations.Refinement

/-!
# Section 13.2 — Rotations

The functional tree layer proves preservation of inorder keys and BST ordering.
The indexed pointer layer implements both rotations, reconnecting the old
parent's appropriate child or the store root and reparenting a non-NIL middle
child. Missing nodes or pivot children leave the store unchanged.

{lit}`StoreReprAt` tracks an expected parent and a finite owned footprint:
nonempty nodes are non-NIL, children have disjoint footprints, the root and
external parent are excluded from descendant footprints, and parent links are
consistent. {lit}`StoreRepr` additionally requires an absent sentinel;
{lit}`Represents` fixes the root's parent to NIL. Both public representation
predicates are functional: one store address cannot represent two trees.

{lit}`rotateLeftP_refines_subtree` and {lit}`rotateRightP_refines_subtree`
prove the actual pointer operations implement the functional rotations and
preserve the owned footprint. Their {lit}`RotationResult` contract states the
precise outside-node frame, including the former parent's updated child link.
The root refinement theorems cover whole stores. {lit}`RotationContext` and
{lit}`rotateLeftP_refines_context` / {lit}`rotateRightP_refines_context` lift
an interior rotation through represented ancestors, preserving siblings and
reconstructing the enclosing whole-store representation.

The store is a sparse functional model of pointer assignments. The returned
{lit}`rotateCost = 6` is a uniform upper assignment budget, comprising five
required assignments and an optional middle-parent assignment; it is not an
exact instrumented count or a runtime bound for immutable node-table evaluation.
Rotations alone preserve BST ordering, not red-black color balance. The
insertion/deletion analysis in the following sections is a separate boundary.
-/
