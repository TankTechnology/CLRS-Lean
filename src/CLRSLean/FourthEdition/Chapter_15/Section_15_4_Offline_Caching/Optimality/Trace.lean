import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Optimality.Trace.A6_Iteration

/-!
# Section 15.4 trace-coupling proof

The optimality proof proceeds through legal cache traces, exact one-page cache
differences, a recursive ordered/credited suffix coupling, one-step exchange,
and finite iteration.

Proof layers:

* [Legal cache traces](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/Optimality/Trace/A1_LegalTrace/)
* [Exact one-page cache difference](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/Optimality/Trace/A2_OnePageDiff/)
* [Recursive coupling core](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/Optimality/Trace/A3_CouplingCore/)
* [Coupling correctness](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/Optimality/Trace/A4_CouplingCorrect/)
* [One-step FIF exchange](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/Optimality/Trace/A5_Exchange/)
* [Finite exchange iteration](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/Optimality/Trace/A6_Iteration/)
-/
