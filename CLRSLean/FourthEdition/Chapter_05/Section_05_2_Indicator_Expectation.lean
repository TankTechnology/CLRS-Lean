import CLRSLean.FourthEdition.Chapter_05.Section_05_2_Indicator_Random_Variables

/-!
# 5.2. Indicator expectation as event probability

This small interface file exposes the textbook identity used throughout
Chapter 5: the expectation of an indicator random variable is the probability
of its event.  Both sides use the same finite uniform sample space, so this is
an interface theorem rather than a second probability model.
-/

namespace CLRS
namespace Chapter05

open CLRS.Probability

/-- The probability of an event in a finite uniform sample space. -/
noncomputable def eventProbability {Omega : Type} [Fintype Omega]
    [DecidableEq Omega] (P : Omega -> Prop) [DecidablePred P] : Real :=
  fintypeExpect (fun omega => indicator (P omega))

/-- **Indicator expectation identity (CLRS Lemma 5.1 interface).**
The expectation of an event's indicator is the probability of that event. -/
theorem indicator_expectation_eq_probability {Omega : Type} [Fintype Omega]
    [DecidableEq Omega] (P : Omega -> Prop) [DecidablePred P] :
    fintypeExpect (fun omega => indicator (P omega)) = eventProbability P := rfl

end Chapter05
end CLRS
