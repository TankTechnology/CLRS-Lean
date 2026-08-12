import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B11_CopyOut

/-!
# SAT → 3-CNF-SAT reduction machine

The TM2 machine computing `encCNF (to3CNF_len (decode x) x.length)` for
`x : List FormulaSym`.  It counts the input length, then does a recursive
descent over the prefix-polish formula, emitting the Tseitin clause templates
with auxiliary variables allocated from the input length.

The semantic reduction `cnfSatisfiable_to3CNF_iff` (and the list encoding
`encCNF`) live in `SatTo3CNFSat`; this file is the machine that computes the
encoding.

This file is a facade that re-exports the machine split across the
`Dev/` sub-modules (see each module for its part of the construction).

**Status (2026-08-12).**  The machine definition, the `count`/`reorder`/`rd`/
`pv` step lemmas, the `reduce` dispatch, the `const`/`not`/`and`/`or`/`iff`
clause emissions (`emitAnd_phase`/`emitOr_phase`/`emitIff_phase`), the
generic move/restore loops, the `parkVal`/`unparkVal` temp-tape subroutines,
the junk `const false` phases, the recursive descent `parse_phase`, and the
`copyOut` phase (`copyOut_phase` + `done_step`, transferring `o` to `out` and
halting) are split and compiling in `Dev.B1`–`Dev.B11`.

**Current gaps.**

- The polynomial-time bounds (`Dev.B12_Bounds`: `to3CNF'_bounds`,
  `decodeAux_enc_consumed_le`, `encCNF_to3CNF'_le`, `satTo3CNFTime`, …) and
  the full-machine run `satTo3CNFOutputsFun` + `TM2ComputableInPolyTime`
  (`Dev.B13_OutputsFun`) are **deferred**: they were broken in the committed
  single-file version of this module and are not part of the `Dev.B1`–`Dev.B11`
  split committed here.  The complete `outputsFun` construction is preserved in
  the git history of this file (lines 6977–7154 of the pre-split file).
- Consequently the assembled `PolyTimeReducible SAT ThreeCNFSat` is not yet
  written.
-/
