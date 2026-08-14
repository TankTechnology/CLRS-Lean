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

-- §32.4 Knuth-Morris-Pratt: prefix function
#check prefixLen
#check prefixLen_satisfies
#check prefixLen_maximal
#check prefixLen_chain_step
#check prefixLen_snoc_eq
#check computePrefixFunction
#check computePrefixFunction_correct

-- §32.4 Knuth-Morris-Pratt: all-occurrences scan and refinement
#check kmpMatcher
#check kmpStep
#check kmpStep_eq_delta
#check kmpMatcher_correct
#check kmpMatcher_sound
#check kmpMatcher_complete

-- §32.4 Knuth-Morris-Pratt: costed construction + scan, linear total bound
#check computePrefixFunctionWithCost
#check computePrefixFunctionWithCost_result
#check computePrefixFunctionWithCost_cost_le
#check kmpMatcherWithCost
#check kmpMatcherWithCost_result
#check kmpMatcherWithCost_cost_le
#check kmpTotalCost
#check kmpTotalCost_le

-- §32.4 Knuth-Morris-Pratt: axioms clean on the headline theorems
#print axioms computePrefixFunction_correct
#print axioms kmpMatcher_correct
#print axioms computePrefixFunctionWithCost_cost_le
#print axioms kmpTotalCost_le

-- §32.5 Suffix arrays: suffix order and validity
#check suffixAt
#check suffixLe
#check suffixArray
#check SuffixArrayValid
#check suffixArray_valid

-- §32.5 Suffix arrays: pattern search
#check suffixArraySearch
#check suffixArraySearch_mem_iff

-- §32.5 Suffix arrays: textbook-complexity construction
#check suffixCompare
#check mergeSortWithCost
#check mergeSortWithCost_cost_le_clog
#check mergeSortWithCost_cost_le_log
#check suffixArrayFast
#check suffixArrayBuildWork
#check suffixArrayFast_valid
#check suffixArrayFast_work_le
#check suffixArrayFast_work_isBigO_nlogn

-- §32.5 Suffix arrays: textbook-complexity range query
#check patternLE
#check patternGT
#check lowerDecide
#check upperDecide
#check binarySearchFirst
#check binarySearchFirstCost
#check binarySearchFirst_spec
#check binarySearchFirstCost_cost_le
#check suffixArrayLower
#check suffixArrayUpper
#check suffixArrayLower_le_upper
#check suffixArrayRange
#check suffixArrayRange_mem_iff
#check suffixArrayQueryWork
#check suffixArrayQueryWork_le
#check suffixArrayQueryWork_isBigO_logn

-- §32.5 Suffix arrays: axioms clean on the headline theorems
#print axioms suffixArray_valid
#print axioms suffixArraySearch_mem_iff
#print axioms suffixArrayFast_valid
#print axioms suffixArrayFast_work_le
#print axioms suffixArrayRange_mem_iff
#print axioms suffixArrayQueryWork_le

end Chapter32
end CLRS
