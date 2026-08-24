import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Instance
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.DigitPacking
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Reduction
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Encoding
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Language
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Certificate
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Bridge
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.RawReduction

/-!
# SUBSET-SUM

Exports a finite indexed natural-number instance model and the fully proved
typed textbook reduction from 3-CNF-SAT.  Stable item labels preserve distinct
copies with equal numerical values, and the input-dependent radix makes the
carry-free column argument explicit.  It also exports an honest serialized
language whose certificates are lists of distinct, in-range value indices.
-/
