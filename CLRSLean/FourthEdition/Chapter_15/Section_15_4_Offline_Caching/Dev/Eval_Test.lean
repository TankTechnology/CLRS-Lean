import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Dev.B5_Iteration

/-!
# Dev: minimal experiment for the case-B no-op accounting

Small computable checks: next-use offsets and the farthest-in-future choice
for the example sequence, plus the caches of the hand-built `d` schedule.

Experiment: `sigma = [1, 2, 3, 2, 4, 5, 1, 3]`, `C0 = {1, 2}`.

* FIF at position 2 (request 3) evicts the farthest of pages 1 and 2: page 1 is
  requested again at 6, page 2 at 3, so the farthest page is 1.
- d evicts 2 at 2, then 1 at 3 (true eviction of the window page), then 1
  at 4 and 5 (later branch-1 positions - no-ops for `d` itself).
-/

namespace CLRS

namespace Caching

open Finset

-- request sequence (a=1, b=2, c=3, d=4, e=5)
def σ₁ : List Page := [1, 2, 3, 2, 4, 5, 1, 3]

-- d: evicts 2 at 2, then 1 at 3, 4, 5 (later ones are no-ops), junk elsewhere
def d₁ : ℕ → Page
  | 2 => 2
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | _ => 0

-- computable checks (farthestInFuture/schedCache for fifoSchedule are
-- noncomputable, so #eval cannot run them; the farthest choice is checked
-- directly instead)
#eval nextUse σ₁ 3 1
#eval nextUse σ₁ 3 2
#eval farthestInList (fun p => nextUse σ₁ 3 p) [1, 2]
#eval farthestInList (fun p => nextUse σ₁ 3 p) [2, 1]
-- d caches (d₁ is computable)
#eval List.range 8 |>.map (fun s => schedCache d₁ ({1, 2} : Finset Page) σ₁ s)

end Caching

end CLRS
