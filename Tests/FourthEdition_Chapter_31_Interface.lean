import CLRSLean.FourthEdition.Chapter_31

/-!
# Fourth-edition Chapter 31 interface checks

These checks pin the public interface of the §31.8 random-witness analysis
(MILLER-RABIN error bound) additions and the §31.6 repeated-squaring
exponentiation.
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

-- §31.6 repeated-squaring modular exponentiation with operation count
#check modExpWithCount
#check modExpWithCount_spec
#check modExpWithCount_count_le

#print axioms modExpWithCount_spec
#print axioms modExpWithCount_count_le

-- §31.4 executable modular-linear-equation solver
#check modularLinearEquationSolution
#check modularLinearEquationSolution_spec
#check modularLinearEquationSolver
#check modularLinearEquationSolver_length
#check modularLinearEquationSolver_sound
#check modularLinearEquationSolver_complete
#check modularLinearEquationSolver_nodup

#print axioms modularLinearEquationSolution_spec
#print axioms modularLinearEquationSolver_complete

-- §31.7 RSA key generation and running time
#check rsaPrivateExponent
#check rsaPrivateExponent_spec
#check rsaEncrypt
#check rsaEncrypt_spec
#check rsaEncrypt_count_le
#check rsaDecrypt
#check rsaDecrypt_spec
#check rsaDecrypt_count_le
#check rsaKeyGen
#check rsaKeyGen_spec

#print axioms rsaPrivateExponent_spec
#print axioms rsaKeyGen_spec

-- §31.8 executable multi-base Miller-Rabin loop
#check millerRabinLoop
#check millerRabinLoop_fst_iff
#check millerRabinLoop_count_le

#print axioms millerRabinLoop_fst_iff
#print axioms millerRabinLoop_count_le

end Chapter31
end CLRS
