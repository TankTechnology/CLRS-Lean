import CLRSLean.FourthEdition.Chapter_32

namespace CLRS
namespace Chapter32

-- §32.1 string model
#check Text
#check matchesAt
#check naiveMatcher
#check naiveMatcher_sound
#check naiveMatcher_complete

-- §32.2 Rabin-Karp: hash and the rolling recurrence
#check hash
#check hash_snoc
#check hash_cons
#check hash_slide
#check slideHash

-- §32.2 Rabin-Karp: hash-and-confirm matcher
#check rabinKarpMatcher
#check rabinKarp_sound
#check rabinKarp_complete
#check rabinKarp_correct

-- §32.2 Rabin-Karp: rolling matcher and its cost
#check rabinKarpRolling
#check rabinKarpRollingMatches
#check rabinKarpRollingCost
#check rabinKarpRollingMatches_correct
#check rabinKarpRollingCost_eq
#check rabinKarpRollingCost_le

-- §32.2 Rabin-Karp: axioms clean on the headline theorems
#print axioms rabinKarpRollingMatches_correct
#print axioms rabinKarpRollingCost_le
#print axioms hash_slide

-- §32.3 Finite automata: suffix function and δ/δ*
#check suffixLen
#check delta
#check deltaStar
#check suffixLen_snoc_le
#check suffixLen_snoc_eq
#check deltaStar_accepts_iff_suffix

-- §32.3 Finite automata: all-occurrences matcher and correctness
#check dfaMatcher
#check dfaMatcher_sound
#check dfaMatcher_complete
#check dfaMatcher_correct

-- §32.3 Finite automata: transition table and lookup
#check transitionTable
#check transitionLookup
#check transitionLookup_eq_delta
#check dfaMatcherTable
#check dfaMatcherTable_correct
#check dfaMatcherTable_eq_naive

-- §32.3 Finite automata: costed preprocessing and scan
#check transitionTableBuildCost
#check transitionTableBuildCost_eq
#check dfaMatcherCost
#check dfaMatcherCost_eq
#check dfaTotalCost_eq

-- §32.3 Finite automata: axioms clean on the headline theorems
#print axioms dfaMatcher_correct
#print axioms transitionLookup_eq_delta
#print axioms dfaMatcherTable_correct
#print axioms transitionTableBuildCost_eq

-- §32.5 Suffix arrays: suffix order and validity
#check suffixAt
#check suffixLe
#check suffixArray
#check SuffixArrayValid
#check suffixArray_valid

-- §32.5 Suffix arrays: pattern search
#check suffixArraySearch
#check suffixArraySearch_mem_iff

-- §32.5 Suffix arrays: axioms clean on the headline theorems
#print axioms suffixArray_valid
#print axioms suffixArraySearch_mem_iff

end Chapter32
end CLRS
