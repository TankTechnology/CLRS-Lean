import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B13_OutputsFun

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

**Focused implementation status (2026-08-13).**  The machine definition, the `count`/`reorder`/`rd`/
`pv` step lemmas, the `reduce` dispatch, the `const`/`not`/`and`/`or`/`iff`
clause emissions (`emitAnd_phase`/`emitOr_phase`/`emitIff_phase`), the
generic move/restore loops, the `parkVal`/`unparkVal` temp-tape subroutines,
the junk `const false` phases, the recursive descent `parse_phase`, and the
`copyOut` phase (`copyOut_phase` + `done_step`, transferring `o` to `out` and
halting) are split and compiling in `Dev.B1`–`Dev.B11`.  `Dev.B12_Bounds`
proves the decoder, encoder-size, and polynomial-time bounds;
`Dev.B13_OutputsFun` composes the complete run and packages it as
`TM2ComputableInPolyTime`.  The theorem below exposes the resulting
`PolyTimeReducible SAT ThreeCNFSat`.

The focused source and interface gates and the repository-wide build pass.
This represented reduction is promoted in the Chapter 34 public interface;
the chapter remains partial only for separately recorded coverage gaps.
-/

namespace CLRS

namespace Chapter34

namespace Turing

namespace TM3CNF

/-- **Lemma 34.7 (computational form).**  SAT polynomial-time reduces to
3-CNF-SAT through the concrete, length-indexed Tseitin encoder. -/
theorem sat_reducible_to_threeCNFSat :
    PolyTimeReducible SAT ThreeCNFSat := by
  refine ⟨fun x => encCNF (to3CNF_len (decode x) x.length), ?_, ?_⟩
  · exact ⟨satTo3CNFComputableInPolyTime⟩
  · intro x
    change Formula.Satisfiable (decode x) ↔
      IsThreeCNF (decodeCNF (encCNF (to3CNF_len (decode x) x.length))) ∧
        CnfSatisfiable (decodeCNF (encCNF (to3CNF_len (decode x) x.length)))
    rw [decodeCNF_encCNF]
    constructor
    · intro hsat
      exact ⟨isThreeCNF_to3CNF_len (decode x) x.length,
        (cnfSatisfiable_to3CNF_len_iff (decode x) x.length
          (numVars_decode_le x)).2 hsat⟩
    · intro h
      exact (cnfSatisfiable_to3CNF_len_iff (decode x) x.length
        (numVars_decode_le x)).1 h.2

end TM3CNF

end Turing

end Chapter34

end CLRS
