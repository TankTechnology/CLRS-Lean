import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B12_Bounds

/-!
# Dev B13: the full machine run and `outputsFun`

This module adapts the initial scan phases, composes every previously proved
machine phase, proves the global polynomial step bound, and packages the
concrete encoder as `TM2ComputableInPolyTime`.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

/-- `count` from any pre-state: the count step pops from `in` and overwrites the
state, so `count_phase_aux` (stated from `St.rd default`) applies from the
machine's initial state `St.init` as well. -/
lemma count_phase (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[inp.length + 1]
        (some (⟨some Label.count, v, stk inp T c V F S O U⟩ : (mach).Cfg))
      = some (⟨some Label.reorder, St.done, stk [] (inp.reverse ++ T) (c + inp.length) V F S O U⟩ : (mach).Cfg) := by
  induction inp generalizing T c v with
  | nil =>
      simp [stk, Sstep, prog, flip]
  | cons s rest ih =>
      have hone := count_step s rest T c V F S O U
      rw [show (s :: rest).length + 1 = (rest.length + 1) + 1 by simp [List.length_cons]]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[rest.length + 1]
          (Sstep (⟨some Label.count, St.rd s, stk (s :: rest) T c V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.reorder, St.done, stk [] ((s :: rest).reverse ++ T) (c + (s :: rest).length) V F S O U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (v := St.rd s) (T := s :: T) (c := c + 1)
      calc
        (flip bind Sstep)^[rest.length + 1]
            (some (⟨some Label.count, St.rd s, stk rest (s :: T) (c + 1) V F S O U⟩ : (mach).Cfg))
          = some (⟨some Label.reorder, St.done, stk [] (rest.reverse ++ (s :: T)) ((c + 1) + rest.length) V F S O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.reorder, St.done, stk [] ((s :: rest).reverse ++ T) (c + (s :: rest).length) V F S O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stk, List.reverse_cons, List.cons_append, List.append_assoc, List.length_cons, Nat.add_comm, Nat.add_assoc] <;> try omega

/-- `reorder` from any pre-state: the reorder step pops from `temp` and
overwrites the state, so `reorder_phase_aux` (stated from `St.rd default`)
applies from the state `St.done` left by the count phase. -/
lemma reorder_phase (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[T.length + 1]
        (some (⟨some Label.reorder, v, stk inp T c V F S O U⟩ : (mach).Cfg))
      = some (⟨some Label.rd, St.done, stk (T.reverse ++ inp) [] c V F S O U⟩ : (mach).Cfg) := by
  induction T generalizing inp v with
  | nil =>
      simp [stk, Sstep, prog, flip]
  | cons s rest ih =>
      have hone : Sstep (⟨some Label.reorder, St.rd s, stk inp (s :: rest) c V F S O U⟩ : (mach).Cfg)
          = some (⟨some Label.reorder, St.rd s, stk (s :: inp) rest c V F S O U⟩ : (mach).Cfg) := by
        apply congrArg some
        apply Turing.TM2Comp.Cfg_ext
        · rfl
        · rfl
        · funext k
          cases k <;> simp [stk, Function.update, prog, Sstep]
      rw [show (s :: rest).length + 1 = (rest.length + 1) + 1 by simp [List.length_cons]]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[rest.length + 1]
          (Sstep (⟨some Label.reorder, St.rd s, stk inp (s :: rest) c V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.rd, St.done, stk ((s :: rest).reverse ++ inp) [] c V F S O U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (inp := s :: inp) (v := St.rd s)
      calc
        (flip bind Sstep)^[rest.length + 1]
            (some (⟨some Label.reorder, St.rd s, stk (s :: inp) rest c V F S O U⟩ : (mach).Cfg))
          = some (⟨some Label.rd, St.done, stk (rest.reverse ++ (s :: inp)) [] c V F S O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.rd, St.done, stk ((s :: rest).reverse ++ inp) [] c V F S O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stk, List.reverse_cons, List.cons_append, List.append_assoc, Nat.add_comm, Nat.add_assoc] <;> try omega

/-- The full machine run: count, reorder, the recursive descent, the root unit
clause, copying `o` to `out`, and clearing the junk.  The final `out` tape is
`encCNF (to3CNF_len (decode inp) inp.length)`. -/
noncomputable def satTo3CNFOutputsFun (inp : List FormulaSym) :
    _root_.Turing.TM2OutputsInTime mach inp
      (some (encCNF (to3CNF_len (decode inp) inp.length)))
      (satTo3CNFTime.eval inp.length) := by
  let n := inp.length
  let f0 := decode inp
  let rest := (decodeAux n inp).2
  let cls := (to3CNF' f0 n).1
  let y := (to3CNF' f0 n).2.1
  let next := (to3CNF' f0 n).2.2
  let outList := encCNF (to3CNF_len f0 n)
  let initC : (mach).Cfg := ⟨some Label.count, St.init, stk inp [] 0 [] [] [] [] []⟩
  let C1 : (mach).Cfg := ⟨some Label.reorder, St.done, stk [] inp.reverse n [] [] [] [] []⟩
  let C2 : (mach).Cfg := ⟨some Label.rd, St.done, stk inp [] n [] [] [] [] []⟩
  have hdec : decodeAux n inp = (f0, rest) := by
    change decodeAux inp.length inp = (f0, rest)
    rfl
  have hV : ([] : List Bool).head? ≠ some true := by simp
  have hparse0 : ∀ v₀ : St, ∃ v₁ : St,
      (flip bind Sstep)^[parseSteps f0 n]
        (some (⟨some Label.rd, v₀, stk inp [] n [] [] [] [] []⟩ : (mach).Cfg))
        = some (⟨some Label.reduce, v₁, stk rest [] next
            (false :: List.replicate (y + 1) true) [] []
            ((encCNF cls).reverse) []⟩ : (mach).Cfg) := by
    intro v₀
    simpa using parse_phase f0 n inp rest n [] [] [] [] [] hV le_rfl hdec v₀
  have hparse_done : ∃ v₁ : St,
      (flip bind Sstep)^[parseSteps f0 n]
        (some (⟨some Label.rd, St.done, stk inp [] n [] [] [] [] []⟩ : (mach).Cfg))
        = some (⟨some Label.reduce, v₁, stk rest [] next
            (false :: List.replicate (y + 1) true) [] []
            ((encCNF cls).reverse) []⟩ : (mach).Cfg) := hparse0 St.done
  let v₁ : St := Classical.choose hparse_done
  have hparse : (flip bind Sstep)^[parseSteps f0 n]
      (some (⟨some Label.rd, St.done, stk inp [] n [] [] [] [] []⟩ : (mach).Cfg))
      = some (⟨some Label.reduce, v₁, stk rest [] next
          (false :: List.replicate (y + 1) true) [] []
          ((encCNF cls).reverse) []⟩ : (mach).Cfg) := by
    simpa [v₁] using Classical.choose_spec hparse_done
  let C3 : (mach).Cfg := ⟨some Label.reduce, v₁, stk rest [] next
      (false :: List.replicate (y + 1) true) [] [] ((encCNF cls).reverse) []⟩
  let C4 : (mach).Cfg := ⟨some Label.emitTrue, St.emitTrue, stk rest [] next
      (false :: List.replicate (y + 1) true) [] [] ((encCNF cls).reverse) []⟩
  let C5 : (mach).Cfg := ⟨some Label.copyOut, St.done, stk rest [] next [] [] []
      ((encCNF [[Literal.pos y]]).reverse ++ (encCNF cls).reverse) []⟩
  let C6 : (mach).Cfg := ⟨some Label.clearIn, St.init, stk rest [] next [] [] [] [] (C5.stk K.o).reverse⟩
  let C7 : (mach).Cfg := ⟨some Label.clearCnt, St.done, stk [] [] next [] [] [] [] (C5.stk K.o).reverse⟩
  let C8 : (mach).Cfg := ⟨some Label.done, St.init, stk [] [] 0 [] [] [] [] (C5.stk K.o).reverse⟩
  let C9 : (mach).Cfg := ⟨none, St.init, stk [] [] 0 [] [] [] [] (C5.stk K.o).reverse⟩
  have hcount : EvalsToInTime Sstep initC (some C1) (n + 1) := by
    refine ⟨⟨n + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[n + 1] (some initC) = some C1
    change (flip bind Sstep)^[n + 1]
        (some (⟨some Label.count, St.init, stk inp [] 0 [] [] [] [] []⟩ : (mach).Cfg))
        = some (⟨some Label.reorder, St.done, stk [] inp.reverse n [] [] [] [] []⟩ : (mach).Cfg)
    rw [count_phase St.init inp [] 0 [] [] [] [] []]
    simp [n, List.append_nil, Nat.zero_add]
  have hreorder : EvalsToInTime Sstep C1 (some C2) (n + 1) := by
    refine ⟨⟨n + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[n + 1] (some C1) = some C2
    change (flip bind Sstep)^[n + 1]
        (some (⟨some Label.reorder, St.done, stk [] inp.reverse n [] [] [] [] []⟩ : (mach).Cfg))
        = some (⟨some Label.rd, St.done, stk inp [] n [] [] [] [] []⟩ : (mach).Cfg)
    rw [show n + 1 = inp.reverse.length + 1 by simp [n, List.length_reverse]]
    rw [reorder_phase St.done [] inp.reverse n [] [] [] [] []]
    simp [n, List.reverse_reverse]
  have hparseE : EvalsToInTime Sstep C2 (some C3) (parseSteps f0 n) := by
    refine ⟨⟨parseSteps f0 n, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[parseSteps f0 n] (some C2) = some C3
    exact hparse
  have hreduce : EvalsToInTime Sstep C3 (some C4) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change (flip bind Sstep) (some C3) = some C4
    exact reduce_top_step v₁ rest [] next (false :: List.replicate (y + 1) true) [] ((encCNF cls).reverse) []
  have hemTrue : EvalsToInTime Sstep C4 (some C5) ((y + 1) + 2) := by
    refine ⟨⟨(y + 1) + 2, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[(y + 1) + 2] (some C4) = some C5
    exact emitTrue_phase y St.emitTrue rest [] next [] [] ((encCNF cls).reverse) []
  have hcopyOut : EvalsToInTime Sstep C5 (some C6) ((C5.stk K.o).length + 1) := by
    refine ⟨⟨(C5.stk K.o).length + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[((encCNF [[Literal.pos y]]).reverse ++ (encCNF cls).reverse).length + 1]
        (some (⟨some Label.copyOut, St.done, stk rest [] next [] [] []
            ((encCNF [[Literal.pos y]]).reverse ++ (encCNF cls).reverse) []⟩ : (mach).Cfg))
        = some (⟨some Label.clearIn, St.init, stk rest [] next [] [] [] []
            ((encCNF [[Literal.pos y]]).reverse ++ (encCNF cls).reverse).reverse⟩ : (mach).Cfg)
    rw [copyOut_phase St.done rest [] next [] [] []
        ((encCNF [[Literal.pos y]]).reverse ++ (encCNF cls).reverse) []]
    simp [List.append_nil]
  have hclearIn : EvalsToInTime Sstep C6 (some C7) (rest.length + 1) := by
    refine ⟨⟨rest.length + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[rest.length + 1]
        (some (⟨some Label.clearIn, St.init, stk rest [] next [] [] [] [] (C5.stk K.o).reverse⟩ : (mach).Cfg))
        = some (⟨some Label.clearCnt, St.done, stk [] [] next [] [] [] [] (C5.stk K.o).reverse⟩ : (mach).Cfg)
    rw [clearIn_phase St.init rest [] next [] [] [] [] (C5.stk K.o).reverse]
  have hclearCnt : EvalsToInTime Sstep C7 (some C8) (next + 1) := by
    refine ⟨⟨next + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[next + 1]
        (some (⟨some Label.clearCnt, St.done, stk [] [] next [] [] [] [] (C5.stk K.o).reverse⟩ : (mach).Cfg))
        = some (⟨some Label.done, St.init, stk [] [] 0 [] [] [] [] (C5.stk K.o).reverse⟩ : (mach).Cfg)
    rw [clearCnt_phase St.done [] [] next [] [] [] [] (C5.stk K.o).reverse]
  have hdone : EvalsToInTime Sstep C8 (some C9) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change (flip bind Sstep) (some C8) = some C9
    exact done_step [] [] 0 [] [] [] (C5.stk K.o).reverse
  have h12 : EvalsToInTime Sstep initC (some C2) ((n + 1) + (n + 1)) :=
    EvalsToInTime.trans Sstep (n + 1) (n + 1) initC C1 (some C2) hcount hreorder
  have h123 : EvalsToInTime Sstep initC (some C3) (parseSteps f0 n + ((n + 1) + (n + 1))) :=
    EvalsToInTime.trans Sstep ((n + 1) + (n + 1)) (parseSteps f0 n) initC C2 (some C3) h12 hparseE
  have h1234 : EvalsToInTime Sstep initC (some C4) (1 + (parseSteps f0 n + ((n + 1) + (n + 1)))) :=
    EvalsToInTime.trans Sstep (parseSteps f0 n + ((n + 1) + (n + 1))) 1 initC C3 (some C4) h123 hreduce
  have h12345 : EvalsToInTime Sstep initC (some C5) (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1))))) :=
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
    rw [hrev, htl]
    simp [encCNF]
  have hfinalCfg : C9 = _root_.Turing.haltList mach outList := by
    apply Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext k
      cases k <;> simp [C9, _root_.Turing.haltList, outList, hout]
  have hinit : _root_.Turing.initList mach inp = initC := by
    apply Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext k
      cases k <;> simp [initC, _root_.Turing.initList, stk]
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
    exact satTo3CNFTime_eval n
  have htotal_le :
      1 + (next + 1 + (rest.length + 1 + ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1))))))))
        ≤ satTo3CNFTime.eval n := by
    rw [hct]
    nlinarith [hparse_le, hy_le, hnext_le, hoLen, hrest_le]
  have hfull : EvalsToInTime Sstep initC (some (_root_.Turing.haltList mach outList))
      (1 + (next + 1 + (rest.length + 1 + ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1))))))))) := by
    simpa [hfinalCfg] using h123456789
  change EvalsToInTime Sstep (_root_.Turing.initList mach inp)
      (some (_root_.Turing.haltList mach outList))
      (satTo3CNFTime.eval inp.length)
  rw [hinit]
  exact ⟨hfull.toEvalsTo, le_trans hfull.steps_le_m htotal_le⟩

/-- The reduction machine computes the 3-CNF encoding in polynomial time. -/
noncomputable def satTo3CNFComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      (id : List FormulaSym → List FormulaSym) (id : List CNFSym → List CNFSym)
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
