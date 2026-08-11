import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CNFToClique

/-!
# 3-CNF-SAT → CLIQUE reduction machine

The TM2 machine computing `relabel x` for `x : List CNFSym`: it reads a CNF
encoding and emits the occurrence-graph encoding of CLRS Lemma 34.10 (a
`vertexMark` inserted before each literal).  A single linear scan relabels the
input onto a working stack `o`; `copyOut` transfers `o` to `out` (reversing it
back) and halts.

The semantic reduction `cnfSatisfiable_iff_hasClique` and the graph encoding
`GraphSym`/`relabel`/`undoRelabel`/`CLIQUE` live in `CNFToClique`; this file
assembles the machine, its `outputsFun`, and `PolyTimeReducible ThreeCNFSat
CLIQUE`.

**Status (2026-08-09).**  The scan/copyOut machine, the phase lemmas, the
`outputsFun`, and the assembled `PolyTimeReducible ThreeCNFSat CLIQUE` are
written.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TMClique

/-- The machine tapes: the input CNF, a working stack, and the output. -/
inductive K : Type
  | inK | o | out
deriving DecidableEq, Fintype, Inhabited

/-- The alphabet of each tape: the input is a CNF encoding, the working and
output tapes carry graph symbols. -/
abbrev Γk : K → Type
  | K.inK => CNFSym
  | K.o => GraphSym
  | K.out => GraphSym

/-- The program labels. -/
inductive Label : Type
  | scan | copyOut | done
deriving DecidableEq, Fintype, Inhabited

/-- The machine states: `rd s` after popping `s` from the input, `copySym s`
while moving a graph symbol to the output. -/
inductive St : Type
  | init
  | rd (s : CNFSym)
  | copySym (s : GraphSym)
deriving DecidableEq, Fintype, Inhabited

/-- The graph symbols contributed by one CNF symbol under `relabel`. -/
def transSym : CNFSym → List GraphSym
  | CNFSym.clauseMark => [GraphSym.clauseMark]
  | CNFSym.posMark => [GraphSym.vertexMark, GraphSym.posMark]
  | CNFSym.negMark => [GraphSym.vertexMark, GraphSym.negMark]
  | CNFSym.varMark => [GraphSym.varMark]
  | CNFSym.endMark => [GraphSym.endMark]

/-- The full stack contents. -/
abbrev stk (inp : List CNFSym) (O U : List GraphSym) : ∀ k : K, List (Γk k) :=
  fun k => match k with
  | K.inK => inp | K.o => O | K.out => U

def prog : Label → Turing.TM2.Stmt Γk Label St
  | Label.scan =>
      Turing.TM2.Stmt.pop K.inK (fun _ x => match x with
          | some s => St.rd s
          | none => St.init)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.rd CNFSym.clauseMark => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => GraphSym.clauseMark)
            (Turing.TM2.Stmt.goto (fun _ => Label.scan)))
          (Turing.TM2.Stmt.branch (fun v => match v with | St.rd CNFSym.posMark => true | _ => false)
            (Turing.TM2.Stmt.push K.o (fun _ => GraphSym.vertexMark)
              (Turing.TM2.Stmt.push K.o (fun _ => GraphSym.posMark)
                (Turing.TM2.Stmt.goto (fun _ => Label.scan))))
            (Turing.TM2.Stmt.branch (fun v => match v with | St.rd CNFSym.negMark => true | _ => false)
              (Turing.TM2.Stmt.push K.o (fun _ => GraphSym.vertexMark)
                (Turing.TM2.Stmt.push K.o (fun _ => GraphSym.negMark)
                  (Turing.TM2.Stmt.goto (fun _ => Label.scan))))
              (Turing.TM2.Stmt.branch (fun v => match v with | St.rd CNFSym.varMark => true | _ => false)
                (Turing.TM2.Stmt.push K.o (fun _ => GraphSym.varMark)
                  (Turing.TM2.Stmt.goto (fun _ => Label.scan)))
                (Turing.TM2.Stmt.branch (fun v => match v with | St.rd CNFSym.endMark => true | _ => false)
                  (Turing.TM2.Stmt.push K.o (fun _ => GraphSym.endMark)
                    (Turing.TM2.Stmt.goto (fun _ => Label.scan)))
                  (Turing.TM2.Stmt.goto (fun _ => Label.copyOut)))))))
  | Label.copyOut =>
      Turing.TM2.Stmt.pop K.o (fun _ x => match x with
          | some s => St.copySym s
          | none => St.init)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.copySym _ => true | _ => false)
          (Turing.TM2.Stmt.push K.out (fun v => match v with
              | St.copySym s => s
              | _ => default)
            (Turing.TM2.Stmt.goto (fun _ => Label.copyOut)))
          (Turing.TM2.Stmt.goto (fun _ => Label.done)))
  | Label.done => Turing.TM2.Stmt.halt

abbrev mach : FinTM2 :=
  @FinTM2.mk K (by infer_instance) (by infer_instance) K.inK K.out Γk Label Label.scan
    (by infer_instance) St St.init (by infer_instance) (by infer_instance) prog

def Sstep : (mach).Cfg → Option (mach).Cfg := mach.step

/-- One scan step: pop the head `s` of the input and push its graph symbols
(transposed) onto `o`, so the stack accumulates the reversed encoding. -/
lemma scan_step (s : CNFSym) (v : St) (rest : List CNFSym) (O U : List GraphSym) :
    Sstep (⟨some Label.scan, v, stk (s :: rest) O U⟩ : (mach).Cfg)
      = some (⟨some Label.scan, St.rd s, stk rest ((transSym s).reverse ++ O) U⟩ : (mach).Cfg) := by
  cases s <;> simp [stk, transSym, Function.update, prog, Sstep]

/-- `scan` with an empty input goes to `copyOut`. -/
lemma scan_empty (v : St) (O U : List GraphSym) :
    Sstep (⟨some Label.scan, v, stk [] O U⟩ : (mach).Cfg)
      = some (⟨some Label.copyOut, St.init, stk [] O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `relabel` splits at each symbol. -/
lemma relabel_cons (s : CNFSym) (rest : List CNFSym) :
    relabel (s :: rest) = transSym s ++ relabel rest := by
  cases s <;> simp [relabel, transSym]

/-- The scan phase: relabel `x` onto `o` (reversed), then go to `copyOut`. -/
lemma scan_phase (v : St) (x : List CNFSym) (O U : List GraphSym) :
    (flip bind Sstep)^[x.length + 1]
        (some (⟨some Label.scan, v, stk x O U⟩ : (mach).Cfg))
      = some (⟨some Label.copyOut, St.init, stk [] ((relabel x).reverse ++ O) U⟩ : (mach).Cfg) := by
  induction x generalizing O with
  | nil =>
      have h := scan_empty v O U
      change (flip bind Sstep) (some (⟨some Label.scan, v, stk [] O U⟩ : (mach).Cfg))
        = some (⟨some Label.copyOut, St.init, stk [] ((relabel []).reverse ++ O) U⟩ : (mach).Cfg)
      simpa [flip, relabel] using h
  | cons s rest ih =>
      have hstep := scan_step s v rest O U
      have hrev : (relabel (s :: rest)).reverse =
          (relabel rest).reverse ++ (transSym s).reverse := by
        rw [relabel_cons]
        rw [List.reverse_append]
      rw [show (s :: rest).length + 1 = (rest.length + 1) + 1 by simp [List.length_cons]]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[rest.length + 1]
          (Sstep (⟨some Label.scan, v, stk (s :: rest) O U⟩ : (mach).Cfg))
        = some (⟨some Label.copyOut, St.init, stk [] ((relabel (s :: rest)).reverse ++ O) U⟩ : (mach).Cfg)
      rw [hstep]
      have hih := ih (O := (transSym s).reverse ++ O)
      calc
        (flip bind Sstep)^[rest.length + 1]
            (some (⟨some Label.scan, St.rd s, stk rest ((transSym s).reverse ++ O) U⟩ : (mach).Cfg))
          = some (⟨some Label.copyOut, St.init, stk [] ((relabel rest).reverse ++ ((transSym s).reverse ++ O)) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.copyOut, St.init, stk [] ((relabel (s :: rest)).reverse ++ O) U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> try simp [stk]
              rw [hrev]
              simp [List.append_assoc]

/-- `copyOut` pops one graph symbol from `o` and pushes it onto `out`. -/
lemma copyOut_step (v : St) (s : GraphSym) (inp : List CNFSym) (O U : List GraphSym) :
    Sstep (⟨some Label.copyOut, v, stk inp (s :: O) U⟩ : (mach).Cfg)
      = some (⟨some Label.copyOut, St.copySym s, stk inp O (s :: U)⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `copyOut` with `o` empty goes to `done`, resetting the state to `init`. -/
lemma copyOut_done (v : St) (inp : List CNFSym) (U : List GraphSym) :
    Sstep (⟨some Label.copyOut, v, stk inp [] U⟩ : (mach).Cfg)
      = some (⟨some Label.done, St.init, stk inp [] U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- The `copyOut` phase: transfer `o` to `out` (reversing it back), then reach
`done` with the state reset to `init`. -/
lemma copyOut_phase (v : St) (inp : List CNFSym) (O U : List GraphSym) :
    (flip bind Sstep)^[O.length + 1]
        (some (⟨some Label.copyOut, v, stk inp O U⟩ : (mach).Cfg))
      = some (⟨some Label.done, St.init, stk inp [] (O.reverse ++ U)⟩ : (mach).Cfg) := by
  induction O generalizing v U with
  | nil =>
      have h := copyOut_done v inp U
      change (flip bind Sstep) (some (⟨some Label.copyOut, v, stk inp [] U⟩ : (mach).Cfg))
        = some (⟨some Label.done, St.init, stk inp [] U⟩ : (mach).Cfg)
      simpa [flip] using h
  | cons s rest ih =>
      have h := copyOut_step v s inp rest U
      rw [show (s :: rest).length + 1 = (rest.length + 1) + 1 by simp [List.length_cons]]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[rest.length + 1]
          (Sstep (⟨some Label.copyOut, v, stk inp (s :: rest) U⟩ : (mach).Cfg))
        = some (⟨some Label.done, St.init, stk inp [] ((s :: rest).reverse ++ U)⟩ : (mach).Cfg)
      rw [h]
      have hih := ih (St.copySym s) (s :: U)
      calc
        (flip bind Sstep)^[rest.length + 1]
            (some (⟨some Label.copyOut, St.copySym s, stk inp rest (s :: U)⟩ : (mach).Cfg))
          = some (⟨some Label.done, St.init, stk inp [] (rest.reverse ++ (s :: U))⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.done, St.init, stk inp [] ((s :: rest).reverse ++ U)⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stk, List.reverse_cons, List.append_assoc]

/-- The `done` label halts, leaving the state at `init`. -/
lemma done_step (inp : List CNFSym) (U : List GraphSym) :
    Sstep (⟨some Label.done, St.init, stk inp [] U⟩ : (mach).Cfg)
      = some (⟨none, St.init, stk inp [] U⟩ : (mach).Cfg) := by
  simp [Sstep, prog]

/-- Each CNF symbol contributes at most two graph symbols. -/
lemma relabel_length_le (x : List CNFSym) : (relabel x).length ≤ 2 * x.length := by
  induction x with
  | nil => simp [relabel]
  | cons s rest ih =>
      cases s <;> simp [relabel, transSym, Nat.mul_succ, Nat.succ_eq_add_one] <;> omega

noncomputable section

/-- The input alphabet of the machine is `CNFSym`. -/
def cliqueInputAlphabet : (mach).Γ (mach).k₀ ≃ CNFSym := Equiv.refl _

/-- The output alphabet of the machine is `GraphSym`. -/
def cliqueOutputAlphabet : (mach).Γ (mach).k₁ ≃ GraphSym := Equiv.refl _

/-- The polynomial time bound: scan `|x| + 1` steps, `copyOut` at most `2|x| +
1`, and one halting step. -/
def cliqueTime : Polynomial ℕ := 3 * Polynomial.X + 3

/-- The machine relabels `x` onto the output in `cliqueTime.eval x.length`
steps: scan onto `o`, then `copyOut` to `out`. -/
noncomputable def cliqueOutputsFun (x : List CNFSym) :
    TM2OutputsInTime mach x (some (relabel x)) (cliqueTime.eval x.length) := by
  let initC : (mach).Cfg := ⟨some Label.scan, St.init, stk x [] []⟩
  let C1 : (mach).Cfg := ⟨some Label.copyOut, St.init, stk [] (relabel x).reverse []⟩
  let C2 : (mach).Cfg := ⟨some Label.done, St.init, stk [] [] (relabel x)⟩
  let C3 : (mach).Cfg := haltList mach (relabel x)
  have hscan : EvalsToInTime Sstep initC (some C1) (x.length + 1) := by
    refine ⟨⟨x.length + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[x.length + 1]
        (some (⟨some Label.scan, St.init, stk x [] []⟩ : (mach).Cfg)) = some C1
    rw [scan_phase St.init x [] []]
    simpa [C1, List.append_nil]
  have hcopy : EvalsToInTime Sstep C1 (some C2) ((relabel x).length + 1) := by
    refine ⟨⟨(relabel x).length + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[(relabel x).length + 1]
        (some (⟨some Label.copyOut, St.init, stk [] (relabel x).reverse []⟩ : (mach).Cfg)) = some C2
    rw [copyOut_phase St.init [] (relabel x).reverse []]
    simpa [C2, List.reverse_reverse, List.append_nil]
  have hdone : EvalsToInTime Sstep C2 (some C3) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change (flip bind Sstep) (some (⟨some Label.done, St.init, stk [] [] (relabel x)⟩ : (mach).Cfg))
        = some C3
    have hC3 : C3 = (⟨none, St.init, stk [] [] (relabel x)⟩ : (mach).Cfg) := by
      apply Turing.TM2Comp.Cfg_ext
      · rfl
      · rfl
      · funext k
        cases k <;> simp [C3, haltList, stk]
    rw [hC3]
    exact done_step [] (relabel x)
  have htotal : EvalsToInTime Sstep initC (some C2)
      ((relabel x).length + 1 + (x.length + 1)) := by
    exact EvalsToInTime.trans Sstep (x.length + 1) ((relabel x).length + 1)
      initC C1 (some C2) hscan hcopy
  have htotal' : EvalsToInTime Sstep initC (some C3)
      (1 + ((relabel x).length + 1 + (x.length + 1))) := by
    exact EvalsToInTime.trans Sstep ((relabel x).length + 1 + (x.length + 1)) 1
      initC C2 (some C3) htotal hdone
  have hinit : initList mach x = initC := by
    apply Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext k
      cases k <;> simp [initC, initList, stk]
  have hfinal : C3 = haltList mach (relabel x) := by rfl
  have hct : cliqueTime.eval x.length = 3 * x.length + 3 := by
    simp [cliqueTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_natCast]
    ring
  have hsteps_le : 1 + ((relabel x).length + 1 + (x.length + 1)) ≤ cliqueTime.eval x.length := by
    rw [hct]
    nlinarith [relabel_length_le x]
  have hfull : EvalsToInTime Sstep initC (some (haltList mach (relabel x)))
      (1 + ((relabel x).length + 1 + (x.length + 1))) := by
    simpa [hfinal] using htotal'
  change EvalsToInTime Sstep (initList mach x) (some (haltList mach (relabel x)))
      (cliqueTime.eval x.length)
  rw [hinit]
  exact ⟨hfull.toEvalsTo, le_trans hfull.steps_le_m hsteps_le⟩

/-- The reduction machine computes `relabel` in polynomial time. -/
noncomputable def cliqueComputableInPolyTime :
    TM2ComputableInPolyTime (id : List CNFSym → List CNFSym) (id : List GraphSym → List GraphSym) relabel where
  tm := mach
  inputAlphabet := cliqueInputAlphabet
  outputAlphabet := cliqueOutputAlphabet
  time := cliqueTime
  outputsFun := fun x => by
    simpa [cliqueInputAlphabet, cliqueOutputAlphabet] using cliqueOutputsFun x

end

/--
**Theorem (3-CNF-SAT poly-reduces to CLIQUE, CLRS Lemma 34.10).**  A CNF is
satisfiable iff its occurrence graph has a clique of size equal to its number of
clauses; the reduction is the relabeling machine.
-/
theorem threeCNFSat_reducible_to_CLIQUE : PolyTimeReducible ThreeCNFSat CLIQUE := by
  refine ⟨relabel, ?comp, ?iff⟩
  · exact ⟨cliqueComputableInPolyTime⟩
  · intro x
    simp [CLIQUE, ThreeCNFSat, undoRelabel_relabel]
    exact cnfSatisfiable_iff_hasClique (decodeCNF x)

end TMClique

end Turing

end Chapter34

end CLRS
