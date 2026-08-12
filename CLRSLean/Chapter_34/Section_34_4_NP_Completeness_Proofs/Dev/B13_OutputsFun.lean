import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B12_Bounds

/-!
# Dev B13: the full machine run and `outputsFun`

`satTo3CNFOutputsFun`: the full-machine phase composition, the polynomial time bound, and the assembled `TM2ComputableInPolyTime` instance.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

    EvalsToInTime.trans Sstep (1 + (parseSteps f0 n + ((n + 1) + (n + 1)))) ((y + 1) + 2) initC C4 (some C5) h1234 hemTrue
  have h123456 : EvalsToInTime Sstep initC (some C6) ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1)))))) :=
    EvalsToInTime.trans Sstep (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1))))) ((C5.stk K.o).length + 1) initC C5 (some C6) h12345 hcopyOut
  have h1234567 : EvalsToInTime Sstep initC (some C7) (rest.length + 1 + ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1))))))) :=
    EvalsToInTime.trans Sstep ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1)))))) (rest.length + 1) initC C6 (some C7) h123456 hclearIn
  have h12345678 : EvalsToInTime Sstep initC (some C8) (next + 1 + (rest.length + 1 + ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1)))))))) :=
    EvalsToInTime.trans Sstep (rest.length + 1 + ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1))))))) (next + 1) initC C7 (some C8) h1234567 hclearCnt
  have h123456789 : EvalsToInTime Sstep initC (some C9) (1 + (next + 1 + (rest.length + 1 + ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1))))))))) :=
    EvalsToInTime.trans Sstep (next + 1 + (rest.length + 1 + ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1)))))))) 1 initC C8 (some C9) h12345678 hdone
  have hout : (C5.stk K.o).reverse = encCNF (to3CNF_len f0 n) := by
    have hrev : (C5.stk K.o).reverse = encCNF cls ++ encCNF [[Literal.pos y]] := by
      simp [C5, List.reverse_append, List.reverse_reverse]
    have htl : to3CNF_len f0 n = cls ++ [[Literal.pos y]] := by
      simp [to3CNF_len, cls, y, forceTrue]
    rw [hrev, ← htl]
    simp [encCNF]
  have hfinalCfg : C9 = haltList mach outList := by
    apply Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext k
      cases k <;> simp [C9, haltList, outList, hout]
  have hinit : initList mach inp = initC := by
    apply Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext k
      cases k <;> simp [initC, initList, stk]
  have hparse_le : parseSteps f0 n ≤ 240 * n * n + 680 * n + 480 := by
    have h := parseSteps_le f0 n
    have hf0 : (enc f0).length ≤ 2 * n + 3 := by
      simpa [f0, n] using enc_decode_le inp
    have helen0 : 0 ≤ (enc f0).length := by simp
    nlinarith [h, hf0, helen0]
  have hbounds := to3CNF'_bounds f0 n
  have hy_le : y ≤ 3 * n + 3 := by
    have hy0 : y ≤ n + (enc f0).length := by simpa [y] using hbounds.1
    have hf0 : (enc f0).length ≤ 2 * n + 3 := by simpa [f0, n] using enc_decode_le inp
    nlinarith [hy0, hf0]
  have hnext_le : next ≤ 3 * n + 3 := by
    have hn0 : next ≤ n + (enc f0).length := by simpa [next] using hbounds.2
    have hf0 : (enc f0).length ≤ 2 * n + 3 := by simpa [f0, n] using enc_decode_le inp
    nlinarith [hn0, hf0]
  have henc : (encCNF cls).length ≤ 72 * n * n + 216 * n + 162 := by
    have h := encCNF_to3CNF'_le f0 n
    have hcl : (encCNF cls).length ≤ 12 * (enc f0).length * (n + (enc f0).length + 1) + 6 * (enc f0).length := by
      simpa [cls] using h
    have hf0 : (enc f0).length ≤ 2 * n + 3 := by simpa [f0, n] using enc_decode_le inp
    have helen0 : 0 ≤ (enc f0).length := by simp
    nlinarith [hcl, hf0, helen0]
  have hoLen : (C5.stk K.o).length ≤ 72 * n * n + 219 * n + 169 := by
    have hlen : (C5.stk K.o).length = (encCNF [[Literal.pos y]]).length + (encCNF cls).length := by
      simp [C5, List.length_append]
    have hyenc : (encCNF [[Literal.pos y]]).length = y + 4 := by
      simp [encCNF, encClause, encLit, litSym, litIndex]
    rw [hlen, hyenc]
    nlinarith [hy_le, henc]
  have hrest_le : rest.length ≤ n := by
    have h := decodeAux_suffix_le n inp
    simpa [rest, n] using h
  have hct : satTo3CNFTime.eval n = 800 * n * n + 3000 * n + 2000 := by
    simp [satTo3CNFTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_natCast]
    ring
  have htotal_le :
      1 + (next + 1 + (rest.length + 1 + ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1))))))))
        ≤ satTo3CNFTime.eval n := by
    rw [hct]
    nlinarith [hparse_le, hy_le, hnext_le, hoLen, hrest_le]
  have hfull : EvalsToInTime Sstep initC (some (haltList mach outList))
      (1 + (next + 1 + (rest.length + 1 + ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1))))))))) := by
    simpa [hfinalCfg] using h123456789
  change EvalsToInTime Sstep (initList mach inp) (some (haltList mach outList))
      (satTo3CNFTime.eval inp.length)
  rw [hinit]
  exact ⟨hfull.toEvalsTo, le_trans hfull.steps_le_m htotal_le⟩

/-- The reduction machine computes the 3-CNF encoding in polynomial time. -/
noncomputable def satTo3CNFComputableInPolyTime :
    TM2ComputableInPolyTime (id : List FormulaSym → List FormulaSym) (id : List CNFSym → List CNFSym)
      (fun inp => encCNF (to3CNF_len (decode inp) inp.length)) where
  tm := mach
  inputAlphabet := satInputAlphabet
  outputAlphabet := satOutputAlphabet
  time := satTo3CNFTime
  outputsFun := fun inp => by
    simpa [satInputAlphabet, satOutputAlphabet] using satTo3CNFOutputsFun inp

end TM3CNF

end Turing

end Chapter34

end CLRS

end TM3CNF

end Turing

end Chapter34

end CLRS
