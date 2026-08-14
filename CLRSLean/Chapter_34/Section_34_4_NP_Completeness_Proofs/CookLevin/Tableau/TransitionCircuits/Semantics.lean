import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Core
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Dispatch.Semantics

/-!
# CLRS Section 34.4 - Local transition-circuit semantics

The final internal wire is true exactly when the decoded next public row is
the total stuttering successor of the decoded current public row.  The reverse
direction derives workspace fit from the decoded next row; no additional
target-fit premise is exposed.

Main results:

- Theorem {lit}`transitionCircuit_eval_iff`: exact local transition semantics.
- Theorem {lit}`transitionCircuit_sound`: direct soundness projection.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Canonical complete-row bridges -/

/-- Equal evaluated row bits transport successful complete-row decoding. -/
private theorem evalBundle_of_evalCfgBits_eq
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

/-- Two successfully decoded canonical rows for the same configuration have
identical complete evaluated bit bundles. -/
private theorem evalCfgBits_eq_of_evalBundle_eq
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (builder : CircuitBuilder) (inputs : Nat → Bool)
    (left right : CfgWires tm H)
    (hleft : left.ValidIn builder) (hright : right.ValidIn builder)
    (c : tm.Cfg)
    (hleftDecoded : evalBundle builder inputs left hleft = some c)
    (hrightDecoded : evalBundle builder inputs right hright = some c) :
    evalCfgBits builder inputs left = evalCfgBits builder inputs right := by
  rcases evalBundle_eq_some_canonical builder inputs left hleft c hleftDecoded with
    ⟨hleftAlphabet, hleftHeight, hleftBits⟩
  rcases evalBundle_eq_some_canonical builder inputs right hright c hrightDecoded with
    ⟨hrightAlphabet, hrightHeight, hrightBits⟩
  have halphabet : hleftAlphabet = hrightAlphabet := Subsingleton.elim _ _
  subst hrightAlphabet
  have hheight : hleftHeight = hrightHeight := Subsingleton.elim _ _
  subst hrightHeight
  rw [hleftBits, hrightBits]

/-! ## Exact local semantics -/

/-- The final local transition wire is true exactly for one total stuttering
TM2 step between successfully decoded public rows. -/
theorem transitionCircuit_eval_iff
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (inputs : Nat → Bool)
    (current next : CfgWires tm H)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base)
    {c c' : tm.Cfg}
    (hcurrentDecoded : evalBundle base inputs current hcurrent = some c)
    (hnextDecoded : evalBundle base inputs next hnext = some c') :
    (transitionCircuit tm H base current next hcurrent hnext).builder.evalWire
        inputs (transitionCircuit tm H base current next hcurrent hnext).wire =
      true ↔ c' = stutterStep tm c := by
  let widened := widenCfg base current hcurrent
  let dispatched := dispatchLabels tm H widened.builder widened.constants
    widened.wires widened.valid
  let narrowed := narrowCfg dispatched.builder dispatched.wires dispatched.valid
  let prefixExtension := widened.extension.trans
    (dispatched.extension.trans narrowed.extension)
  have hnextNarrowed : next.ValidIn narrowed.builder :=
    hnext.mono prefixExtension
  let equal := cfgEq narrowed.builder narrowed.wires next narrowed.valid
    hnextNarrowed
  have hfitEqual : equal.builder.WireValid narrowed.fit :=
    equal.extension.wireValid narrowed.fitValid
  let final := equal.builder.and narrowed.fit equal.wire hfitEqual equal.valid
  rcases evalBundle_eq_some_canonical base inputs current hcurrent c
      hcurrentDecoded with ⟨_, hcurrentHeight, _⟩
  have hwidenedDecoded :
      evalBundle widened.builder inputs widened.wires widened.valid = some c := by
    exact widenCfg_decode_preserved base current hcurrent inputs c
      hcurrentDecoded
  have hdispatchedDecoded :
      evalBundle dispatched.builder inputs dispatched.wires dispatched.valid =
        some (stutterStep tm c) := by
    exact dispatchLabels_evalBundle tm H widened.builder widened.constants inputs
      widened.wires widened.valid hwidenedDecoded hcurrentHeight
  have hnextNarrowedDecoded :
      evalBundle narrowed.builder inputs next hnextNarrowed = some c' := by
    rw [evalBundle_extends prefixExtension inputs next hnext]
    exact hnextDecoded
  change final.1.evalWire inputs final.2 = true ↔ c' = stutterStep tm c
  rw [CircuitBuilder.and_eval equal.builder narrowed.fit equal.wire hfitEqual
    equal.valid inputs]
  constructor
  · intro hfinal
    have hand : equal.builder.evalWire inputs narrowed.fit = true ∧
        equal.builder.evalWire inputs equal.wire = true := by
      exact Bool.and_eq_true_iff.mp hfinal
    have hfit : narrowed.builder.evalWire inputs narrowed.fit = true := by
      rw [equal.extension.evalWire_eq inputs narrowed.fitValid] at hand
      exact hand.1
    have hnarrowedDecoded :
        evalBundle narrowed.builder inputs narrowed.wires narrowed.valid =
          some (stutterStep tm c) :=
      narrowCfg_decode_preserved dispatched.builder dispatched.wires
        dispatched.valid inputs (stutterStep tm c) hdispatchedDecoded hfit
    have hbits := (equal.eval inputs).mp hand.2
    have hnarrowedAsNext :
        evalBundle narrowed.builder inputs narrowed.wires narrowed.valid =
          some c' :=
      evalBundle_of_evalCfgBits_eq narrowed.builder narrowed.builder inputs
        narrowed.wires narrowed.valid next hnextNarrowed hbits
        hnextNarrowedDecoded
    rw [hnarrowedDecoded] at hnarrowedAsNext
    exact (Option.some.inj hnarrowedAsNext).symm
  · intro hstep
    rcases evalBundle_eq_some_canonical base inputs next hnext c'
        hnextDecoded with ⟨_, hnextHeight, _⟩
    have htargetHeight : ∀ k, ((stutterStep tm c).stk k).length ≤ H := by
      intro k
      rw [← hstep]
      exact hnextHeight k
    have hfit : narrowed.builder.evalWire inputs narrowed.fit = true := by
      apply (narrowed.fit_eval inputs).mpr
      rcases evalBundle_eq_some_canonical dispatched.builder inputs
          dispatched.wires dispatched.valid (stutterStep tm c)
          hdispatchedDecoded with ⟨htargetAlphabet, hworkspaceHeight, hbits⟩
      intro k offset
      let overflow : Fin (workHeight tm H + 1) :=
        ⟨H + 1 + offset.val, by simp only [workHeight]; omega⟩
      have hslot := congrFun hbits (CfgSlot.stackHeight k overflow)
      have hne : overflow ≠
          ((encodeCfg tm htargetAlphabet hworkspaceHeight).stack k).height := by
        intro heq
        have hval := congrArg Fin.val heq
        simp only [overflow, encodeCfg, encodeBoundedStack] at hval
        have hle := htargetHeight k
        omega
      change dispatched.builder.evalWire inputs
          (dispatched.wires.stackHeight k overflow) =
        encodeOneHot
          ((encodeCfg tm htargetAlphabet hworkspaceHeight).stack k).height
          overflow at hslot
      exact hslot.trans (by simp [encodeOneHot, hne])
    have hnarrowedDecoded :
        evalBundle narrowed.builder inputs narrowed.wires narrowed.valid =
          some (stutterStep tm c) :=
      narrowCfg_decode_preserved dispatched.builder dispatched.wires
        dispatched.valid inputs (stutterStep tm c) hdispatchedDecoded hfit
    have hnextTarget :
        evalBundle narrowed.builder inputs next hnextNarrowed =
          some (stutterStep tm c) := by
      rw [← hstep]
      exact hnextNarrowedDecoded
    have hbits : evalCfgBits narrowed.builder inputs narrowed.wires =
        evalCfgBits narrowed.builder inputs next :=
      evalCfgBits_eq_of_evalBundle_eq narrowed.builder inputs narrowed.wires
        next narrowed.valid hnextNarrowed (stutterStep tm c)
        hnarrowedDecoded hnextTarget
    have hequal : equal.builder.evalWire inputs equal.wire = true :=
      (equal.eval inputs).mpr hbits
    have hfitAtEqual : equal.builder.evalWire inputs narrowed.fit = true := by
      rw [equal.extension.evalWire_eq inputs narrowed.fitValid]
      exact hfit
    simp [hfitAtEqual, hequal]

/-- Direct soundness projection from exact local transition semantics. -/
theorem transitionCircuit_sound
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (inputs : Nat → Bool)
    (current next : CfgWires tm H)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base)
    {c c' : tm.Cfg}
    (hcurrentDecoded : evalBundle base inputs current hcurrent = some c)
    (hnextDecoded : evalBundle base inputs next hnext = some c')
    (htransition :
      (transitionCircuit tm H base current next hcurrent hnext).builder.evalWire
          inputs (transitionCircuit tm H base current next hcurrent hnext).wire =
        true) :
    c' = stutterStep tm c :=
  (transitionCircuit_eval_iff tm H base inputs current next hcurrent hnext
    hcurrentDecoded hnextDecoded).mp htransition

end

end CLRS.Chapter34.Turing.CookLevin
