import CLRSLean.FourthEdition.Chapter_31

/-!
# Fourth-edition Chapter 31 interface checks

These checks pin the public interface of the §31.8 random-witness analysis
(MILLER-RABIN error bound) additions.
-/

namespace CLRS
namespace Chapter31

-- §31.8 random-witness analysis
#check strongPseudoprime_coprime
#check isStrongLiar_of_strongPseudoprime
#check strongLiars_nat_card_le

/-! The headline theorems must not carry `sorryAx` or any project axiom. -/
#print axioms strongPseudoprime_coprime
#print axioms isStrongLiar_of_strongPseudoprime
#print axioms strongLiars_nat_card_le

end Chapter31
end CLRS
