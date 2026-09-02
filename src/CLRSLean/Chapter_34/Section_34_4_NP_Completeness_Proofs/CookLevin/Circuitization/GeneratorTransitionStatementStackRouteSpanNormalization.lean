import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteAffineAtomNormalization
import Mathlib.Data.List.DropRight
import Mathlib.Tactic

/-!
# Compact spans for normalized statement stack routes

Sequential push/pop normalization never permutes the surviving coordinates of
the original stack.  It only removes a prefix and suffix and inserts fixed
values on either side.  `TransitionRouteSpan` records exactly that compact
normal form.  This module proves that its static head/tail rewrites agree with
ordinary `List.drop` and `List.rdrop` whenever the rewrite remains inside the
surviving source interval.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- A compact route consisting of inserted prefix values, one surviving
interval of the original source, and inserted suffix values. -/
@[ext] structure TransitionRouteSpan (α : Type) where
  headValues : List α
  sourceDrop : Nat
  sourceRdrop : Nat
  tailValues : List α
deriving DecidableEq, Repr

/-- Surviving original-source interval carried by a span. -/
def TransitionRouteSpan.middle (span : TransitionRouteSpan α)
    (source : List α) : List α :=
  (source.drop span.sourceDrop).rdrop span.sourceRdrop

/-- Interpret a compact route against its original source. -/
def TransitionRouteSpan.eval (span : TransitionRouteSpan α)
    (source : List α) : List α :=
  span.headValues ++ span.middle source ++ span.tailValues

/-- Identity compact route. -/
def TransitionRouteSpan.identity : TransitionRouteSpan α :=
  { headValues := []
    sourceDrop := 0
    sourceRdrop := 0
    tailValues := [] }

@[simp] theorem TransitionRouteSpan.eval_identity (source : List α) :
    (TransitionRouteSpan.identity : TransitionRouteSpan α).eval source =
      source := by
  simp [TransitionRouteSpan.identity, TransitionRouteSpan.eval,
    TransitionRouteSpan.middle]

/-- Map only the inserted constants; source interval coordinates remain
structural and are interpreted against a target-typed source later. -/
def TransitionRouteSpan.map (f : α → β)
    (span : TransitionRouteSpan α) : TransitionRouteSpan β :=
  { headValues := span.headValues.map f
    sourceDrop := span.sourceDrop
    sourceRdrop := span.sourceRdrop
    tailValues := span.tailValues.map f }

/-- Mapping a compact span changes exactly its inserted head and tail values.
-/
theorem TransitionRouteSpan.eval_map
    (f : α → β) (span : TransitionRouteSpan α) (source : List β) :
    (span.map f).eval source =
      span.headValues.map f ++
        (source.drop span.sourceDrop).rdrop span.sourceRdrop ++
          span.tailValues.map f := by
  rfl

/-- Remove a fixed number of leading values.  If the inserted prefix is too
short, the remaining deletion is transferred to the original-source span. -/
def TransitionRouteSpan.dropHead (amount : Nat)
    (span : TransitionRouteSpan α) : TransitionRouteSpan α :=
  if amount ≤ span.headValues.length then
    { span with headValues := span.headValues.drop amount }
  else
    { headValues := []
      sourceDrop := span.sourceDrop + (amount - span.headValues.length)
      sourceRdrop := span.sourceRdrop
      tailValues := span.tailValues }

/-- Remove a fixed number of trailing values.  If the inserted suffix is too
short, the remaining deletion is transferred to the original-source span. -/
def TransitionRouteSpan.dropTail (amount : Nat)
    (span : TransitionRouteSpan α) : TransitionRouteSpan α :=
  if amount ≤ span.tailValues.length then
    { span with tailValues := span.tailValues.rdrop amount }
  else
    { headValues := span.headValues
      sourceDrop := span.sourceDrop
      sourceRdrop := span.sourceRdrop + (amount - span.tailValues.length)
      tailValues := [] }

/-- Insert one leading constant. -/
def TransitionRouteSpan.prepend (value : α)
    (span : TransitionRouteSpan α) : TransitionRouteSpan α :=
  { span with headValues := value :: span.headValues }

/-- Insert one trailing constant. -/
def TransitionRouteSpan.append (span : TransitionRouteSpan α)
    (value : α) : TransitionRouteSpan α :=
  { span with tailValues := span.tailValues ++ [value] }

@[simp] theorem TransitionRouteSpan.map_dropHead
    (f : α → β) (span : TransitionRouteSpan α) (amount : Nat) :
    (span.dropHead amount).map f = (span.map f).dropHead amount := by
  unfold TransitionRouteSpan.dropHead TransitionRouteSpan.map
  simp only [List.length_map]
  split_ifs <;>
    apply TransitionRouteSpan.ext <;> simp

@[simp] theorem TransitionRouteSpan.map_dropTail
    (f : α → β) (span : TransitionRouteSpan α) (amount : Nat) :
    (span.dropTail amount).map f = (span.map f).dropTail amount := by
  unfold TransitionRouteSpan.dropTail TransitionRouteSpan.map
  simp only [List.length_map]
  split_ifs <;>
    apply TransitionRouteSpan.ext <;> simp [List.rdrop]

@[simp] theorem TransitionRouteSpan.map_prepend
    (f : α → β) (span : TransitionRouteSpan α) (value : α) :
    (span.prepend value).map f = (span.map f).prepend (f value) := by
  rfl

@[simp] theorem TransitionRouteSpan.map_append
    (f : α → β) (span : TransitionRouteSpan α) (value : α) :
    (span.append value).map f = (span.map f).append (f value) := by
  simp [TransitionRouteSpan.map, TransitionRouteSpan.append]

private theorem middle_drop
    (source : List α) (left right amount : Nat) :
    ((source.drop left).rdrop right).drop amount =
      (source.drop (left + amount)).rdrop right := by
  unfold List.rdrop
  rw [List.drop_take, List.drop_drop]
  congr 1
  simp only [List.length_drop]
  omega

/-- Static head deletion agrees with deleting the interpreted list, provided
the requested amount does not reach the inserted suffix. -/
theorem TransitionRouteSpan.eval_dropHead
    (span : TransitionRouteSpan α) (source : List α) (amount : Nat)
    (hinside : amount ≤ span.headValues.length + (span.middle source).length) :
    (span.dropHead amount).eval source =
      (span.eval source).drop amount := by
  unfold TransitionRouteSpan.dropHead
  by_cases hhead : amount ≤ span.headValues.length
  · rw [if_pos hhead]
    simp only [TransitionRouteSpan.eval, TransitionRouteSpan.middle]
    symm
    simpa only [List.append_assoc] using
      (List.drop_append_of_le_length
        (l₁ := span.headValues)
        (l₂ := (source.drop span.sourceDrop).rdrop span.sourceRdrop ++
          span.tailValues) hhead)
  · rw [if_neg hhead]
    have hheadLength : span.headValues.length ≤ amount := by omega
    have hmiddle :
        amount - span.headValues.length ≤ (span.middle source).length := by
      omega
    have hdrop :
        (span.eval source).drop amount =
          (span.middle source).drop
              (amount - span.headValues.length) ++ span.tailValues := by
      unfold TransitionRouteSpan.eval
      rw [show span.headValues ++ span.middle source ++ span.tailValues =
          span.headValues ++ (span.middle source ++ span.tailValues) by
        simp only [List.append_assoc]]
      rw [List.drop_append]
      rw [List.drop_eq_nil_of_le hheadLength]
      simp only [List.nil_append]
      rw [List.drop_append_of_le_length hmiddle]
    rw [hdrop]
    simp only [TransitionRouteSpan.eval, TransitionRouteSpan.middle]
    simp only [List.nil_append]
    rw [middle_drop]

/-- Static tail deletion agrees with deleting the interpreted list, provided
the requested amount does not reach the inserted prefix. -/
theorem TransitionRouteSpan.eval_dropTail
    (span : TransitionRouteSpan α) (source : List α) (amount : Nat)
    (hinside : amount ≤ span.tailValues.length + (span.middle source).length) :
    (span.dropTail amount).eval source =
      (span.eval source).rdrop amount := by
  unfold TransitionRouteSpan.dropTail
  by_cases htail : amount ≤ span.tailValues.length
  · rw [if_pos htail]
    simp only [TransitionRouteSpan.eval, TransitionRouteSpan.middle]
    rw [List.rdrop_append_of_le_length amount htail]
  · rw [if_neg htail]
    have htailLength : span.tailValues.length ≤ amount := by omega
    have hmiddle :
        amount - span.tailValues.length ≤ (span.middle source).length := by
      omega
    have hamount :
        amount = span.tailValues.length +
          (amount - span.tailValues.length) := by omega
    simp only [TransitionRouteSpan.eval]
    rw [hamount, List.rdrop_append_length_add]
    rw [List.rdrop_append_of_le_length _ hmiddle]
    unfold TransitionRouteSpan.middle
    rw [List.rdrop_add]
    simp [htailLength]

/-- Leading insertion commutes with span interpretation. -/
@[simp] theorem TransitionRouteSpan.eval_prepend
    (span : TransitionRouteSpan α) (source : List α) (value : α) :
    (span.prepend value).eval source = value :: span.eval source := by
  simp [TransitionRouteSpan.prepend, TransitionRouteSpan.eval,
    TransitionRouteSpan.middle]

/-- Trailing insertion commutes with span interpretation. -/
@[simp] theorem TransitionRouteSpan.eval_append
    (span : TransitionRouteSpan α) (source : List α) (value : α) :
    (span.append value).eval source = span.eval source ++ [value] := by
  simp [TransitionRouteSpan.append, TransitionRouteSpan.eval,
    TransitionRouteSpan.middle, List.append_assoc]

end CLRS.Chapter34.Turing.CookLevin
