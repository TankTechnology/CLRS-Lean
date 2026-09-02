import CLRSLean.FourthEdition.Chapter_15.Section_15_1_Activity_Selection

/-!
# CLRS §15.1 textbook activity inputs

The executable core intentionally accepts arbitrary natural-number endpoints.
This small layer states the textbook input contract {lit}`sᵢ < fᵢ` and provides a
subtype for clients that want the contract enforced by the type checker.
-/

namespace CLRS.ActivitySelection

/-- The endpoint condition imposed on every activity in CLRS §15.1. -/
def TextbookValid (a : Activity) : Prop :=
  a.start < a.finish

/-- A list consists entirely of textbook-valid activities. -/
def TextbookInput (xs : List Activity) : Prop :=
  ∀ a ∈ xs, TextbookValid a

/-- An activity whose endpoints satisfy the textbook contract. -/
abbrev TextbookActivity := {a : Activity // TextbookValid a}

theorem textbookInput_nil : TextbookInput [] := by
  simp [TextbookInput]

theorem textbookInput_cons {a : Activity} {xs : List Activity} :
    TextbookInput (a :: xs) ↔ TextbookValid a ∧ TextbookInput xs := by
  simp [TextbookInput]

theorem TextbookInput.of_sublist {xs ys : List Activity}
    (hxs : TextbookInput xs) (hsub : ys.Sublist xs) :
    TextbookInput ys := by
  intro a ha
  exact hxs a (hsub.subset ha)

theorem TextbookInput.activitiesAfter {a : Activity} {xs : List Activity}
    (hxs : TextbookInput xs) :
    TextbookInput (activitiesAfter a xs) :=
  hxs.of_sublist (activitiesAfter_sublist a xs)

theorem TextbookInput.greedySelect {xs : List Activity}
    (hxs : TextbookInput xs) :
    TextbookInput (greedySelect xs) :=
  hxs.of_sublist (greedySelect_sublist xs)

end CLRS.ActivitySelection
