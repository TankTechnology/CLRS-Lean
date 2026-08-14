import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly.Completeness

/-!
# Soundness of the assembled verifier circuit

From any satisfying tableau assignment, row-validity outputs recover decoded
configurations.  The remaining outputs recover a bounded certificate, the
initial row, the complete stuttering chain, and the exact accepting row.
-/

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing

noncomputable section

/-- A true final conjunction determines a semantic accepting verifier
tableau. -/
theorem verifierConjunction_sound {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) (inputs : Nat → Bool)
    (hfinal : (verifierConjunction W x).1.evalWire inputs
      (verifierConjunction W x).2 = true) :
    ∃ configs, IsVerifierTableau W x configs := by
  let H := (verifierHeight W).eval x.length
  let T := (verifierHorizon W).eval x.length
  let rows := verifierRows W x
  let pool := verifierPool W x
  let validity := verifierValidity W x
  let transitions := verifierTransitions W x
  let initial := verifierInitialBoundary W x
  let input := verifierInputBoundary W x

  have hvalidTrue := verifierConjunction_validity_true W x inputs hfinal
  have hexists : ∀ row, ∃ cfg : W.machine.tm.Cfg,
      evalBundle pool.builder inputs (rows.rows row)
          ((rows.rowValid row).mono pool.extension) = some cfg := by
    intro row
    have hsome := (validCfgCircuitFamily_eval_iff pool.builder rows.rows
      (fun r => (rows.rowValid r).mono pool.extension) inputs row).1
      (hvalidTrue row)
    exact Option.isSome_iff_exists.mp hsome
  let configs : Fin (tableauRowCount T) → W.machine.tm.Cfg :=
    fun row => Classical.choose (hexists row)
  have hdecodedPool : ∀ row,
      evalBundle pool.builder inputs (rows.rows row)
          ((rows.rowValid row).mono pool.extension) = some (configs row) :=
    fun row => Classical.choose_spec (hexists row)

  let hrowsValidity := fun row =>
    (rows.rowValid row).mono (pool.extension.trans validity.extension)
  have hdecodedValidity : ∀ row,
      evalBundle validity.builder inputs (rows.rows row)
          (hrowsValidity row) = some (configs row) := by
    intro row
    rw [evalBundle_extends validity.extension inputs (rows.rows row)
      ((rows.rowValid row).mono pool.extension)]
    exact hdecodedPool row
  have htransitionTrue :=
    verifierConjunction_transitions_true W x inputs hfinal
  have hchain : ∀ step : Fin T,
      configs step.succ = stutterStep W.machine.tm
        (configs step.castSucc) := by
    exact transitionCircuitFamily_stutter_chain W.machine.tm H
      validity.builder rows.rows hrowsValidity inputs configs hdecodedValidity
      htransitionTrue

  let first := verifierFirstRow T
  let hextTransitions := pool.extension.trans
    (validity.extension.trans transitions.extension)
  let hfirstTransitions := (rows.rowValid first).mono hextTransitions
  have hdecodedFirstTransitions :
      evalBundle transitions.builder inputs (rows.rows first)
          hfirstTransitions = some (configs first) := by
    rw [evalBundle_extends transitions.extension inputs (rows.rows first)
      (hrowsValidity first)]
    exact hdecodedValidity first
  let ys := (configs first).stk W.machine.tm.k₀
  have hrepTransitions : (evalStackBits transitions.builder inputs
      ((rows.rows first).stack W.machine.tm.k₀)).Represents ys := by
    simpa [ys, evalStackBits_cfgStack] using
      evalBundle_stack_represents transitions.builder inputs
        (rows.rows first) hfirstTransitions hdecodedFirstTransitions
        W.machine.tm.k₀
  have hinitialTrue := verifierConjunction_initial_true W x inputs hfinal
  have hdecodedInitialTarget :
      evalBundle transitions.builder inputs (rows.rows first)
          hfirstTransitions = some (_root_.Turing.initList W.machine.tm ys) := by
    exact (symbolicInitialCfgCircuit_eval_iff W.machine.tm H
      transitions.builder
      (pool.pool.mono (validity.extension.trans transitions.extension)) inputs
      (rows.rows first) hfirstTransitions
      ((rows.rows first).stack W.machine.tm.k₀)
      (hfirstTransitions.stack _) ys hrepTransitions).1 hinitialTrue
  have hfirst : configs first = _root_.Turing.initList W.machine.tm ys := by
    rw [hdecodedFirstTransitions] at hdecodedInitialTarget
    exact Option.some.inj hdecodedInitialTarget

  let hextInitial := hextTransitions.trans initial.extension
  let hfirstInitial := (rows.rowValid first).mono hextInitial
  have hdecodedFirstInitial : evalBundle initial.builder inputs
      (rows.rows first) hfirstInitial = some (configs first) := by
    rw [evalBundle_extends initial.extension inputs (rows.rows first)
      hfirstTransitions]
    exact hdecodedFirstTransitions
  have hrepInitial : (evalStackBits initial.builder inputs
      ((rows.rows first).stack W.machine.tm.k₀)).Represents ys := by
    simpa [ys, evalStackBits_cfgStack] using
      evalBundle_stack_represents initial.builder inputs
        (rows.rows first) hfirstInitial hdecodedFirstInitial W.machine.tm.k₀
  have hinputTrue := verifierConjunction_input_true W x inputs hfinal
  have hinputShape : IsVerifierInput W x ys :=
    (verifierInputShapeCircuit_eval_iff W H initial.builder
      (pool.pool.mono (validity.extension.trans
        (transitions.extension.trans initial.extension)))
      ((rows.rows first).stack W.machine.tm.k₀) (hfirstInitial.stack _) x
      inputs ys hrepInitial).1 hinputTrue
  rcases hinputShape with ⟨c, hc, hys⟩
  have hinitial : configs first = verifierInitialCfg W c x := by
    rw [hfirst, hys]
    rfl

  let last := Fin.last T
  let hextInput := hextInitial.trans input.extension
  let hlastInput := (rows.rowValid last).mono hextInput
  have hdecodedLastInput : evalBundle input.builder inputs
      (rows.rows last) hlastInput = some (configs last) := by
    rw [evalBundle_extends input.extension inputs (rows.rows last)
      ((rows.rowValid last).mono hextInitial)]
    rw [evalBundle_extends initial.extension inputs (rows.rows last)
      ((rows.rowValid last).mono hextTransitions)]
    rw [evalBundle_extends transitions.extension inputs (rows.rows last)
      (hrowsValidity last)]
    exact hdecodedValidity last
  have hacceptingTrue :=
    verifierConjunction_accepting_true W x inputs hfinal
  have hdecodedAcceptingTarget : evalBundle input.builder inputs
      (rows.rows last) hlastInput = some (verifierAcceptingCfg W) := by
    exact (acceptingOutputCircuit_eval_iff W.machine.tm H input.builder
      (pool.pool.mono (validity.extension.trans
        (transitions.extension.trans
          (initial.extension.trans input.extension)))) inputs
      (rows.rows last) hlastInput
      (List.map W.machine.outputAlphabet.invFun (boolEncoding true))).1
        hacceptingTrue
  have haccepting : configs last = verifierAcceptingCfg W := by
    rw [hdecodedLastInput] at hdecodedAcceptingTarget
    exact Option.some.inj hdecodedAcceptingTarget

  refine ⟨configs, c, hc, ?_, hchain, ?_⟩
  · simpa [first, verifierFirstRow, tableauRowCount] using hinitial
  · simpa [last] using haccepting

end

end CLRS.Chapter34.Turing.CookLevin
