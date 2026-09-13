import CLRSLean.FourthEdition.Chapter_03.Section_03_1_Asymptotic_Notation.Core
import CLRSLean.FourthEdition.Chapter_03.Section_03_1_Asymptotic_Notation.CLRSBridge

/-!
# 3.2. Asymptotic Notation: Formal Definitions

This fourth-edition reader facade presents the formal definitions and laws for
the five asymptotic relations.  The implementation is shared with Section 3.1,
but this page gives Section 3.2 its own canonical route and proof inventory.

## Definitions

The imported development defines {lit}`isBigO`, {lit}`isBigOmega`,
{lit}`isBigTheta`, {lit}`isLittleO`, and {lit}`isLittleOmega` over natural
inputs, together with real-domain variants.

## Main results

* {name}`CLRS.Chapter03.isBigO_iff_clrs`,
  {name}`CLRS.Chapter03.isBigOmega_iff_clrs`, and
  {name}`CLRS.Chapter03.isBigTheta_iff_clrs` identify the Mathlib definitions
  with the eventually nonnegative textbook inequalities.
* {name}`CLRS.Chapter03.isLittleO_iff_clrs_strict` and
  {name}`CLRS.Chapter03.isLittleOmega_iff_clrs_strict` give the strict
  quantified characterizations under the required eventual-positivity
  assumptions.
* {name}`CLRS.Chapter03.isLittleO_trans` and
  {name}`CLRS.Chapter03.isLittleOmega_trans` prove transitivity.

Status: `proved` for the formal asymptotic relations and the stated textbook
bridges.
-/
