import CLRSLean.FourthEdition.Chapter_05

/-!
# Fourth-edition Chapter 5 interface checks

These checks pin the public interface of the executable HIRE-ASSISTANT
pseudocode layer in the native fourth-edition §5.1 source.
-/

namespace CLRS
namespace Chapter05

-- §5.1 executable HIRE-ASSISTANT pseudocode
#check recordsFrom
#check hireAssistant
#check recordsFrom_step
#check hireAssistant_cons
#check recordsFrom_le_length
#check hireAssistant_le_length
#check hireAssistant_pos

-- The executable loop counts left-to-right maxima (records).
example : hireAssistant [] = 0 := by native_decide
example : hireAssistant [7] = 1 := by native_decide
example : hireAssistant [3, 1, 4, 1, 5, 9, 2, 6] = 4 := by native_decide
example : recordsFrom 5 [1, 6, 3, 9, 8] = 2 := by native_decide

/-! The headline theorems must not carry `sorryAx` or any project axiom. -/
#print axioms recordsFrom_step
#print axioms hireAssistant_le_length

end Chapter05
end CLRS
