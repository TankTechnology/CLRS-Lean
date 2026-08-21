import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementInitialAffine

/-!
# Exact remainder after the affine initial statement block

The raw-input compiler now emits a complete first primitive block for every
program statement.  This file removes that block from the semantic statement
script and records the exact residual recursion.  In particular, the only
variable-width phase left by a branch is its final whole-row mux; `pop` has no
half-primitive residue because its pair lookup belongs to the initial block.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- The literal suffix of a statement script after its complete initial
primitive block. -/
def transitionStmtRemainderScript
    (tm : _root_.Turing.FinTM2) (height start : Nat)
    (falseWire trueWire : Nat) (source : CfgWires tm height)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    List PolyBuilder.AffineStmtPhase :=
  (transitionStmtScript tm height falseWire trueWire start source q
      hsupport).drop
    (transitionStmtInitialPhaseBlock tm height start falseWire trueWire source
      q hsupport).length

/-- The generated initial block and the residual suffix reconstruct the real
statement script byte-for-byte at the phase level. -/
theorem transitionStmtInitialPhaseBlock_append_remainder
    (tm : _root_.Turing.FinTM2) (height start : Nat)
    (falseWire trueWire : Nat) (source : CfgWires tm height)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    transitionStmtInitialPhaseBlock tm height start falseWire trueWire source q
        hsupport ++
      transitionStmtRemainderScript tm height start falseWire trueWire source q
        hsupport =
      transitionStmtScript tm height falseWire trueWire start source q
        hsupport := by
  let initial := transitionStmtInitialPhaseBlock tm height start falseWire
    trueWire source q hsupport
  let script := transitionStmtScript tm height falseWire trueWire start source q
    hsupport
  have hprefix : initial <+: script :=
    transitionStmtInitialPhaseBlock_prefix tm height start falseWire trueWire
      source q hsupport
  have htake : initial = script.take initial.length :=
    List.prefix_iff_eq_take.mp hprefix
  rw [transitionStmtRemainderScript]
  change initial ++ script.drop initial.length = script
  nth_rw 1 [htake]
  exact List.take_append_drop initial.length script

/-! ## Constructor-level residual equations -/

@[simp] theorem transitionStmtRemainderScript_halt
    (tm : _root_.Turing.FinTM2) (height start falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (hsupport : ∀ k, stmtPushSet tm (.halt :
      _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) k ⊆ reachableAlphabet tm k) :
    transitionStmtRemainderScript tm height start falseWire trueWire source
      .halt hsupport = [] := by
  rfl

@[simp] theorem transitionStmtRemainderScript_goto
    (tm : _root_.Turing.FinTM2) (height start falseWire trueWire : Nat)
    (source : CfgWires tm height) (jump : tm.σ → tm.Λ)
    (hsupport : ∀ k, stmtPushSet tm (.goto jump) k ⊆
      reachableAlphabet tm k) :
    transitionStmtRemainderScript tm height start falseWire trueWire source
      (.goto jump) hsupport = [] := by
  simp [transitionStmtRemainderScript, transitionStmtInitialPhaseBlock,
    transitionStmtHeadPhase, transitionStmtScript]

@[simp] theorem transitionStmtRemainderScript_load
    (tm : _root_.Turing.FinTM2) (height start falseWire trueWire : Nat)
    (source : CfgWires tm height) (update : tm.σ → tm.σ)
    (continuation : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm (.load update continuation) k ⊆
      reachableAlphabet tm k) :
    transitionStmtRemainderScript tm height start falseWire trueWire source
        (.load update continuation) hsupport =
      transitionStmtScript tm height falseWire trueWire
        (start + stateCount tm + stateCount tm)
        (source.replaceState
          (oneHotMapGateTrace start source.state
            (stmtStateTable tm update)).wires)
        continuation (by simpa [stmtPushSet] using hsupport) := by
  simp [transitionStmtRemainderScript, transitionStmtInitialPhaseBlock,
    transitionStmtHeadPhase, transitionStmtScript]

@[simp] theorem transitionStmtRemainderScript_push
    (tm : _root_.Turing.FinTM2) (height start falseWire trueWire : Nat)
    (source : CfgWires tm height) (k : tm.K)
    (emit : tm.σ → tm.Γ k)
    (continuation : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ j, stmtPushSet tm (.push k emit continuation) j ⊆
      reachableAlphabet tm j) :
    transitionStmtRemainderScript tm height start falseWire trueWire source
        (.push k emit continuation) hsupport =
      transitionStmtScript tm height falseWire trueWire
        (start + stateCount tm + (reachableAlphabet tm k).card)
        (arithmeticPushCfgWires tm height k falseWire
          (oneHotMapGateTrace start source.state
            (fun code => encodeSupportedSymbol
              ⟨emit ((stateEquivFin tm).symm code), by
                apply hsupport k
                simp [stmtPushSet]⟩)).wires source)
        continuation (by
          intro j symbol hsymbol
          apply hsupport j
          simp only [stmtPushSet]
          exact Finset.mem_union_right _ hsymbol) := by
  simp [transitionStmtRemainderScript, transitionStmtInitialPhaseBlock,
    transitionStmtHeadPhase, transitionStmtScript]

@[simp] theorem transitionStmtRemainderScript_peek
    (tm : _root_.Turing.FinTM2) (height start falseWire trueWire : Nat)
    (source : CfgWires tm height) (k : tm.K)
    (update : tm.σ → Option (tm.Γ k) → tm.σ)
    (continuation : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ j, stmtPushSet tm (.peek k update continuation) j ⊆
      reachableAlphabet tm j) :
    transitionStmtRemainderScript tm height start falseWire trueWire source
        (.peek k update continuation) hsupport =
      transitionStmtScript tm height falseWire trueWire
        (start + 2 * stateCount tm *
          ((reachableAlphabet tm k).card + 1) + stateCount tm)
        (source.replaceState
          (oneHotPairMapGateTrace start source.state
            (arithmeticPeekCfgWires tm height falseWire trueWire source k)
            (stmtHeadStateTable tm k update)).wires)
        continuation (by simpa [stmtPushSet] using hsupport) := by
  simp [transitionStmtRemainderScript, transitionStmtInitialPhaseBlock,
    transitionStmtHeadPhase, transitionStmtScript]

@[simp] theorem transitionStmtRemainderScript_pop
    (tm : _root_.Turing.FinTM2) (height start falseWire trueWire : Nat)
    (source : CfgWires tm height) (k : tm.K)
    (update : tm.σ → Option (tm.Γ k) → tm.σ)
    (continuation : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ j, stmtPushSet tm (.pop k update continuation) j ⊆
      reachableAlphabet tm j) :
    transitionStmtRemainderScript tm height start falseWire trueWire source
        (.pop k update continuation) hsupport =
      let popped := arithmeticPopCfgWires tm height k falseWire trueWire
        start source
      let head := arithmeticPopHeadWires tm k falseWire trueWire height
        (source.stack k)
      let pairStart := start + popStackWireGateCost height
      let mapped := (oneHotPairMapGateTrace pairStart popped.state head
        (stmtHeadStateTable tm k update)).wires
      transitionStmtScript tm height falseWire trueWire
        (pairStart +
          (2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
            stateCount tm))
        (popped.replaceState mapped) continuation
        (by simpa [stmtPushSet] using hsupport) := by
  simp [transitionStmtRemainderScript, transitionStmtInitialPhaseBlock,
    transitionStmtScript]

@[simp] theorem transitionStmtRemainderScript_branch
    (tm : _root_.Turing.FinTM2) (height start falseWire trueWire : Nat)
    (source : CfgWires tm height) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
      reachableAlphabet tm k) :
    transitionStmtRemainderScript tm height start falseWire trueWire source
        (.branch test whenTrue whenFalse) hsupport =
      let htrueSupport :
          ∀ k, stmtPushSet tm whenTrue k ⊆ reachableAlphabet tm k := by
        intro k symbol hsymbol
        apply hsupport k
        simp only [stmtPushSet]
        exact Finset.mem_union_left _ hsymbol
      let hfalseSupport :
          ∀ k, stmtPushSet tm whenFalse k ⊆ reachableAlphabet tm k := by
        intro k symbol hsymbol
        apply hsupport k
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let predicateWire :=
        (CircuitBuilder.disjunctionGateTrace start
          (oneHotPredicateWires source.state
            (stmtPredicateTable tm test))).wire
      let trueStart := start +
        ((oneHotTruePreimage (stmtPredicateTable tm test)).card + 1)
      let trueScript := transitionStmtScript tm height falseWire trueWire
        trueStart source whenTrue htrueSupport
      let trueWires := transitionStmtOutputWires tm height falseWire trueWire
        trueStart source whenTrue htrueSupport
      let falseStart := trueStart + compileStmtGateCost tm height whenTrue
      let falseScript := transitionStmtScript tm height falseWire trueWire
        falseStart source whenFalse hfalseSupport
      let falseWires := transitionStmtOutputWires tm height falseWire trueWire
        falseStart source whenFalse hfalseSupport
      let muxStart := falseStart + compileStmtGateCost tm height whenFalse
      trueScript ++ falseScript ++
        [.mux predicateWire
          (affineMuxFinCanonicalFrames muxStart predicateWire _
            (fun i => trueWires ((cfgSlotEquivFin tm height).symm i))
            (fun i => falseWires ((cfgSlotEquivFin tm height).symm i)))] := by
  simp [transitionStmtRemainderScript, transitionStmtInitialPhaseBlock,
    transitionStmtHeadPhase, transitionStmtScript, Nat.add_assoc]

end CLRS.Chapter34.Turing.CookLevin
