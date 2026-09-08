import CLRSLean.FourthEdition.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Definitions
import CLRSLean.FourthEdition.Chapter_29.Section_29_1_Standard_And_Slack_Forms.SlackVariables
import CLRSLean.FourthEdition.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Equivalence
import CLRSLean.FourthEdition.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Normalization

/-!
# 29.1 Standard and slack forms

The represented foundation defines standard-form maximization programs over
finite real matrices, and converts the general linear-programming form to
standard form while preserving feasibility and the objective.  Subsequent child
modules add slack variables and prove their exact feasibility equivalence.

The canonical Chapter 29 guide additionally imports {lit}`SolverWrapper`,
which connects this normalization to the initialized SIMPLEX development in
the supplementary online material. Its basic/nonbasic dictionary model and
{lit}`GeneralLP.solve_complete` certify infeasible, optimal or unbounded
outcomes. This section is the formulation layer of that larger development;
it does not claim a polynomial SIMPLEX bound or executable exact-real choices.

## Implementation details

The split proof layers remain available outside the main sidebar:

* [Standard-Form Definitions](CLRSLean/FourthEdition/Chapter_29/Section_29_1_Standard_And_Slack_Forms/Definitions/)
* [Canonical Slack Variables](CLRSLean/FourthEdition/Chapter_29/Section_29_1_Standard_And_Slack_Forms/SlackVariables/)
* [Standard/Slack Equivalence](CLRSLean/FourthEdition/Chapter_29/Section_29_1_Standard_And_Slack_Forms/Equivalence/)
* [Certified General-Form Solver](CLRSLean/FourthEdition/Chapter_29/Section_29_1_Standard_And_Slack_Forms/SolverWrapper/)
* [General-Form Normalization](CLRSLean/FourthEdition/Chapter_29/Section_29_1_Standard_And_Slack_Forms/Normalization/)
-/

namespace CLRS
namespace Chapter29
end Chapter29
end CLRS
