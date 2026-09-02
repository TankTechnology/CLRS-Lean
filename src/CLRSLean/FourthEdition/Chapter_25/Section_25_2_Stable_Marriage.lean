import Mathlib
import CLRSLean.FourthEdition.Chapter_25.Section_25_2_Stable_Marriage.S1_Preference_Model
import CLRSLean.FourthEdition.Chapter_25.Section_25_2_Stable_Marriage.S2_Gale_Shapley
import CLRSLean.FourthEdition.Chapter_25.Section_25_2_Stable_Marriage.S3_Optimality

/-!
# 25.2. The stable-marriage problem

This section formalizes the stable-marriage problem of CLRS §25.2 and the
Gale–Shapley proposal algorithm: the preference model (rank functions,
pairings, blocking pairs, stability), the functional proposal loop with
well-founded termination, and the stability theorems for its output.

Main results:

- `PreferenceProfile` / `Pairing`: the preference and pairing model
- `Pairing.Stable`: absence of blocking pairs (CLRS eq. (25.10))
- `gs`: the Gale–Shapley output pairing
- `gs_terminates_le_n_sq`: the proposal loop terminates within `|M| · |W|`
  proposals
- `gs_stable` (Theorem 25.5): the Gale–Shapley output is stable
- `stable_matching_exists`: every preference profile has a stable pairing
- `gs_perfect`: equal-size sides yield a perfect Gale–Shapley pairing
- `gs_man_optimal` (Theorem 25.6): every man receives his best valid partner
- `gs_woman_pessimal`: the same output is woman-pessimal among stable pairings

Current gaps:

- None for the finite preference model and the textbook optimality theorems.

Notation conventions used in this section:

- `M` : men, `W` : women (finite types, `DecidableEq`)
- `P` : preference profile with rank functions `mRank` / `wRank` (smaller
  ranks are better)
- `μ` : pairing with partner functions `mPartner` / `wPartner`

## Implementation details

The section is split into the following sub-modules:

* [Preference Model](CLRSLean/FourthEdition/Chapter_25/Section_25_2_Stable_Marriage/S1_Preference_Model/)
* [Gale–Shapley Algorithm](CLRSLean/FourthEdition/Chapter_25/Section_25_2_Stable_Marriage/S2_Gale_Shapley/)
* [Optimality](CLRSLean/FourthEdition/Chapter_25/Section_25_2_Stable_Marriage/S3_Optimality/)
-/
