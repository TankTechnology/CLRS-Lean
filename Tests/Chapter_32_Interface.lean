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

end Chapter32
end CLRS
