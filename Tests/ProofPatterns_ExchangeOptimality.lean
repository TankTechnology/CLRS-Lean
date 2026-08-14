import CLRSLean.ProofPatterns.Exchange

namespace CLRS

#check ProofPatterns.Optimal
#check ProofPatterns.Optimal.feasible_chosen
#check ProofPatterns.Optimal.noWorse_than
#check ProofPatterns.Optimal.of_noWorse
#check ProofPatterns.optimal_of_exchange

example {feasible : Nat → Prop} {old new : Nat}
    (hold : ProofPatterns.Optimal feasible (· ≤ ·) old)
    (hnew : feasible new) (hnewOld : new ≤ old) :
    ProofPatterns.Optimal feasible (· ≤ ·) new :=
  ProofPatterns.Optimal.of_noWorse hold hnew hnewOld Nat.le_trans

example {feasible target : List Nat → Prop} {chosen : List Nat}
    (hchosen : feasible chosen)
    (hexchange : ∀ other, feasible other →
      ∃ exchanged, target exchanged ∧
        ProofPatterns.ExchangeCertificate.NoLessScore
          List.length exchanged other)
    (htarget : ∀ exchanged, target exchanged →
      ProofPatterns.ExchangeCertificate.NoLessScore
        List.length chosen exchanged) :
    ProofPatterns.Optimal feasible
      (ProofPatterns.ExchangeCertificate.NoLessScore List.length) chosen :=
  ProofPatterns.optimal_of_exchange hchosen hexchange htarget (by
    intro a b c hab hbc
    exact Nat.le_trans hbc hab)

end CLRS
