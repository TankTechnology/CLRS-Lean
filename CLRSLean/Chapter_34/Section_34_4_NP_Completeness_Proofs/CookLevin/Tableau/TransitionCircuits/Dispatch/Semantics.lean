import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Dispatch.Core
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StatementCircuits.Semantics

/-!
# CLRS Section 34.4 - Finite-control dispatch semantics

Successful decoding of the source workspace row determines the selected
program arm.  The reserved {lit}`none` label keeps the widened source row, while an
actual finite label selects the complete row produced by its recursive
statement compiler.

Main result:

- Theorem {lit}`dispatchLabels_evalBundle`: complete dispatch evaluates to one
  exact stuttering TM2 step.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

open _root_.Turing.TM2

/-- Finite labels have a classical decidable equality for semantic list tests. -/
private noncomputable instance labelDecidableEq
    (tm : _root_.Turing.FinTM2) : DecidableEq tm.Λ :=
  Classical.decEq _

/-! ## Pure selected-row recurrence -/

/-- Pure value recurrence mirrored by serial whole-row dispatch. -/
def dispatchTarget (tm : _root_.Turing.FinTM2) (c : tm.Cfg) :
    List tm.Λ → tm.Cfg → tm.Cfg
  | [], fallback => fallback
  | label :: labels, fallback =>
      dispatchTarget tm c labels
        (if encodeOneHot (encodeLabel tm c.l)
            (Fin.castSucc (labelEquivFin tm label)) then
          _root_.Turing.TM2.stepAux (tm.m label) c.var c.stk
        else fallback)

/-- Equal evaluated row bits transport successful complete-row decoding. -/
private theorem dispatchEvalBundle_of_evalCfgBits_eq
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (leftBuilder rightBuilder : CircuitBuilder) (inputs : Nat → Bool)
    (left : CfgWires tm H) (hleft : left.ValidIn leftBuilder)
    (right : CfgWires tm H) (hright : right.ValidIn rightBuilder)
    {c : tm.Cfg}
    (heq : evalCfgBits leftBuilder inputs left =
      evalCfgBits rightBuilder inputs right)
    (hdecoded : evalBundle rightBuilder inputs right hright = some c) :
    evalBundle leftBuilder inputs left hleft = some c := by
  unfold evalBundle evalRawBundle at hdecoded ⊢
  rw [heq]
  exact hdecoded

/-! ## Serial dispatch semantics -/

/-- A finite serial dispatch list evaluates to its pure selected-row
recurrence.  Every statement arm receives capacity from the public source
height plus the uniform per-step workspace margin. -/
theorem dispatchLabelsList_evalBundle
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (inputs : Nat → Bool)
    (source fallback : CfgWires tm (workHeight tm H))
    (hsource : source.ValidIn base) (hfallback : fallback.ValidIn base)
    (labels : List tm.Λ) {c fallbackCfg : tm.Cfg}
    (hsourceDecoded : evalBundle base inputs source hsource = some c)
    (hfallbackDecoded :
      evalBundle base inputs fallback hfallback = some fallbackCfg)
    (hheight : ∀ k, (c.stk k).length ≤ H) :
    evalBundle
        (dispatchLabelsList tm H base pool source fallback hsource hfallback
          labels).builder
        inputs
        (dispatchLabelsList tm H base pool source fallback hsource hfallback
          labels).wires
        (dispatchLabelsList tm H base pool source fallback hsource hfallback
          labels).valid =
      some (dispatchTarget tm c labels fallbackCfg) := by
  induction labels generalizing base fallback fallbackCfg with
  | nil =>
      simpa [dispatchLabelsList, dispatchTarget] using hfallbackDecoded
  | cons label labels ih =>
      let compiled := compileStmt tm (workHeight tm H) base pool source hsource
        (tm.m label) (stmtPushSet_program_subset tm label)
      let selector := source.label (Fin.castSucc (labelEquivFin tm label))
      have hselector : compiled.builder.WireValid selector :=
        compiled.extension.wireValid (hsource.label _)
      let selected := cfgMux compiled.builder selector compiled.wires fallback
        hselector compiled.valid (hfallback.mono compiled.extension)
      let stepExtension := compiled.extension.trans selected.extension
      have hcapacity :
          ∀ k, (c.stk k).length + stmtMaxPushes tm k (tm.m label) ≤
            workHeight tm H := by
        intro k
        have hh := hheight k
        have hpush := stmtMaxPushes_le_maxPushesPerStep tm label k
        simp only [workHeight]
        omega
      have hcompiled :
          evalBundle compiled.builder inputs compiled.wires compiled.valid =
            some (_root_.Turing.TM2.stepAux (tm.m label) c.var c.stk) := by
        exact compileStmt_evalBundle tm (workHeight tm H) base pool inputs source
          hsource (tm.m label) (stmtPushSet_program_subset tm label)
          hsourceDecoded hcapacity
      have hfallbackCompiled :
          evalBundle compiled.builder inputs fallback
              (hfallback.mono compiled.extension) = some fallbackCfg := by
        rw [evalBundle_extends compiled.extension inputs fallback hfallback]
        exact hfallbackDecoded
      have hlabel := evalLabelBits_of_evalBundle base inputs source hsource c
        hsourceDecoded
      have hselectorEval : compiled.builder.evalWire inputs selector =
          encodeOneHot (encodeLabel tm c.l)
            (Fin.castSucc (labelEquivFin tm label)) := by
        rw [compiled.extension.evalWire_eq inputs (hsource.label _)]
        simpa [selector, evalLabelBits] using
          congrFun hlabel (Fin.castSucc (labelEquivFin tm label))
      let nextFallback :=
        if encodeOneHot (encodeLabel tm c.l)
            (Fin.castSucc (labelEquivFin tm label)) then
          _root_.Turing.TM2.stepAux (tm.m label) c.var c.stk
        else fallbackCfg
      have hselectedDecoded :
          evalBundle selected.builder inputs selected.wires selected.valid =
            some nextFallback := by
        cases hbit : encodeOneHot (encodeLabel tm c.l)
            (Fin.castSucc (labelEquivFin tm label)) with
        | false =>
            have hbits : evalCfgBits selected.builder inputs selected.wires =
                evalCfgBits compiled.builder inputs fallback := by
              rw [selected.eval, hselectorEval, hbit]
              rfl
            have hdecoded := dispatchEvalBundle_of_evalCfgBits_eq selected.builder
              compiled.builder inputs selected.wires selected.valid fallback
              (hfallback.mono compiled.extension) hbits hfallbackCompiled
            convert hdecoded using 1
            all_goals simp [nextFallback, hbit]
            all_goals rfl
        | true =>
            have hcompiledSelected :
                evalBundle selected.builder inputs compiled.wires
                    (compiled.valid.mono selected.extension) =
                  some (_root_.Turing.TM2.stepAux (tm.m label) c.var c.stk) := by
              rw [evalBundle_extends selected.extension inputs compiled.wires
                compiled.valid]
              exact hcompiled
            have hbits : evalCfgBits selected.builder inputs selected.wires =
                evalCfgBits compiled.builder inputs compiled.wires := by
              rw [selected.eval, hselectorEval, hbit]
              rfl
            have hdecoded := dispatchEvalBundle_of_evalCfgBits_eq selected.builder
              compiled.builder inputs selected.wires selected.valid
              compiled.wires compiled.valid hbits hcompiled
            convert hdecoded using 1
            all_goals simp [nextFallback, hbit]
            all_goals rfl
      have hsourceSelected :
          evalBundle selected.builder inputs source
              (hsource.mono stepExtension) = some c := by
        rw [evalBundle_extends stepExtension inputs source hsource]
        exact hsourceDecoded
      have hrest := ih (base := selected.builder)
        (pool := pool.mono stepExtension) (fallback := selected.wires)
        (hsource := hsource.mono stepExtension) (hfallback := selected.valid)
        (fallbackCfg := nextFallback)
        hsourceSelected hselectedDecoded
      convert hrest using 1 <;> rfl

/-! ## Complete-label recurrence -/

/-- A halted source leaves every finite label selector false. -/
private theorem dispatchTarget_halted (tm : _root_.Turing.FinTM2)
    (c fallback : tm.Cfg) (labels : List tm.Λ) (hhalted : c.l = none) :
    dispatchTarget tm c labels fallback = fallback := by
  induction labels generalizing fallback with
  | nil => rfl
  | cons label labels ih =>
      rw [dispatchTarget]
      have hne : Fin.castSucc (labelEquivFin tm label) ≠ encodeLabel tm none := by
        intro heq
        have hval := congrArg Fin.val heq
        simp only [Fin.val_castSucc, encodeLabel] at hval
        omega
      simp [hhalted, encodeOneHot, hne, ih]

/-- With an actual source label, dispatch returns its statement arm whenever
that label occurs in the finite list, and otherwise retains the fallback. -/
private theorem dispatchTarget_some (tm : _root_.Turing.FinTM2)
    (c fallback : tm.Cfg) (selected : tm.Λ) (labels : List tm.Λ)
    (hlabel : c.l = some selected) :
    dispatchTarget tm c labels fallback =
      if selected ∈ labels then
        _root_.Turing.TM2.stepAux (tm.m selected) c.var c.stk
      else fallback := by
  classical
  induction labels generalizing fallback with
  | nil => simp [dispatchTarget]
  | cons label labels ih =>
      rw [dispatchTarget, ih]
      rw [hlabel]
      by_cases heq : label = selected
      · subst label
        have hself : Fin.castSucc (labelEquivFin tm selected) =
            encodeLabel tm (some selected) := by
          apply Fin.ext
          rfl
        simp [encodeOneHot, hself]
      · have hcode : Fin.castSucc (labelEquivFin tm label) ≠
            encodeLabel tm (some selected) := by
          intro hsame
          have hval := congrArg
            (fun i : Fin (labelCount tm + 1) => i.val) hsame
          simp only [Fin.val_castSucc, encodeLabel, Fin.val_castLE] at hval
          have hfin : labelEquivFin tm label = labelEquivFin tm selected := by
            apply Fin.ext
            exact hval
          exact heq ((labelEquivFin tm).injective hfin)
        have hne : selected ≠ label := Ne.symm heq
        simp [encodeOneHot, hcode, hne]

/-- Every label occurs in the canonical finite label list. -/
private theorem mem_programLabels (tm : _root_.Turing.FinTM2) (label : tm.Λ) :
    label ∈ programLabels tm := by
  rw [programLabels, List.mem_ofFn]
  exact ⟨labelEquivFin tm label, (labelEquivFin tm).symm_apply_apply label⟩

/-- Complete finite-label value dispatch is exactly one total stuttering step. -/
theorem dispatchTarget_programLabels (tm : _root_.Turing.FinTM2) (c : tm.Cfg) :
    dispatchTarget tm c (programLabels tm) c = stutterStep tm c := by
  cases hlabel : c.l with
  | none =>
      rw [dispatchTarget_halted tm c c (programLabels tm) hlabel]
      exact (stutterStep_halted tm hlabel).symm
  | some label =>
      rw [dispatchTarget_some tm c c label (programLabels tm) hlabel]
      rw [if_pos (mem_programLabels tm label)]
      cases c with
      | mk currentLabel state stackFn =>
          simp only at hlabel
          subst currentLabel
          rfl

/-! ## Public complete-row theorem -/

/-- Successful source decoding makes complete finite-label dispatch evaluate
to exactly one total stuttering step.  The theorem identifies the whole row,
not merely its label or top stack cell. -/
theorem dispatchLabels_evalBundle
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (inputs : Nat → Bool) (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) {c : tm.Cfg}
    (hdecoded : evalBundle base inputs source hvalid = some c)
    (hheight : ∀ k, (c.stk k).length ≤ H) :
    evalBundle (dispatchLabels tm H base pool source hvalid).builder inputs
        (dispatchLabels tm H base pool source hvalid).wires
        (dispatchLabels tm H base pool source hvalid).valid =
      some (stutterStep tm c) := by
  have hdispatch := dispatchLabelsList_evalBundle tm H base pool inputs source
    source hvalid hvalid (programLabels tm) hdecoded hdecoded hheight
  rw [dispatchTarget_programLabels tm c] at hdispatch
  exact hdispatch

end

end CLRS.Chapter34.Turing.CookLevin
