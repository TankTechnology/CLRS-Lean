import CLRSLean.FourthEdition.Chapter_04.Section_04_4_Recursion_Tree_Method.Branching.IntegerTree.Balanced
import CLRSLean.FourthEdition.Chapter_04.Section_04_4_Recursion_Tree_Method.Branching.IntegerTree.Unbalanced
import CLRSLean.FourthEdition.Chapter_04.Section_04_7_Akra_Bazzi

/-!
# Connections to Chapter 4 asymptotic interfaces

The exact integer-tree theorems and the asymptotic theorems remain separate
claims.  The balanced cost supplies an all-input floor recurrence directly;
for the unequal branches this file exposes the characteristic root used by the
existing Akra--Bazzi layer.  The one-unit rounding bound is proved in
`Unbalanced.lean`.
-/

namespace CLRS
namespace Chapter04

/-- The integer unequal-depth example uses the classic Akra--Bazzi root {lit}`p=1`. -/
theorem unbalancedInteger_akraBazziRoot :
    IsAkraBazziRoot [(1, (3 : Real)), (1, (3 : Real) / 2)] 1 :=
  akraBazziRoot_two_thirds_one

end Chapter04
end CLRS
