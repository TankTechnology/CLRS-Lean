import CLRSLean.Chapter_29.Section_29_1_3_Simplex
import CLRSLean.Chapter_29.Section_29_4_5_Duality

/-!
# Chapter 29 — Linear Programming

Chapter 29 covers the simplex algorithm for solving linear programs and the
fundamental theory of LP duality.

**Sections**

- **29.1–29.3 — Standard Form, Slack Form, and the Simplex Algorithm**
  (file: `Section_29_1_3_Simplex.lean`)

  Main declarations:
  {lit}`StandardLP`, {lit}`SlackForm`, {lit}`StandardLP.toSlackForm`,
  {lit}`SlackForm.basicSolution`, {lit}`SlackForm.pivot`,
  {lit}`SlackForm.simplex`, {lit}`SlackForm.blandEntering`,
  {lit}`SlackForm.blandLeaving`, {lit}`SlackForm.IsOptimal`,
  {lit}`simplex_correct`.

  Status: {lit}`partial`.  Definitions are fully specified; proofs deferred.

- **29.4–29.5 — Duality**
  (file: `Section_29_4_5_Duality.lean`)

  Main declarations:
  {lit}`StandardLP.dual`, {lit}`weak_duality`, {lit}`strong_duality`,
  {lit}`complementarySlackness`, {lit}`complementary_slackness_iff_optimal`.

  Status: {lit}`partial`.  All theorem interfaces formalized; proofs deferred.

**Design Notes**

The types `Mat n m` and `Vec n` are reused from the conventions established
in Chapter 28 (`Matrix (Fin n) (Fin m) ℝ` and `Fin n → ℝ`).  The simplex
formalization uses a lightweight finite-dimensional model suitable for
algorithmic reasoning.

**Deferred Work**

- All correctness proofs for PIVOT and SIMPLEX.
- Termination proof for SIMPLEX with Bland's rule.
- Constructive proof of strong duality via simplex final tableau.
- Two-phase simplex method for finding an initial basic feasible solution.
-/

namespace CLRS
namespace Chapter29
end Chapter29
end CLRS
