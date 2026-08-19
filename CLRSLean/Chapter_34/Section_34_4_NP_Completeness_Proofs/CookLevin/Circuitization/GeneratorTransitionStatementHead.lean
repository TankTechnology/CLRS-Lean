import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchLayout

/-!
# Seed-derived leading phases of transition statements

Each fixed program-label arm begins with the outer constructor of its bundled
statement.  This file removes builders and proof terms from that first phase,
then proves that the complete label-order family of leading phases is computed
solely from one transition row seed.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Builder-free peek wires.  Positive height reads physical cell zero;
height zero uses the seed's shared Boolean constants for the legal blank
head. -/
def arithmeticPeekCfgWires (tm : _root_.Turing.FinTM2) (height : Nat)
    (falseWire trueWire : Nat) (source : CfgWires tm height)
    (k : tm.K) : HeadWires tm k :=
  match height with
  | 0 => fun code =>
      if code = encodeHeadCode none then trueWire else falseWire
  | _ + 1 => fun code => (source.stack k).cell 0 code

/-- The builder-free definition is extensionally the ordinary pool-backed
zero-gate peek. -/
theorem arithmeticPeekCfgWires_eq_peekCfgWires
    {tm : _root_.Turing.FinTM2} {height : Nat}
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm height) (k : tm.K) :
    arithmeticPeekCfgWires tm height pool.falseWire pool.trueWire source k =
      peekCfgWires k pool source := by
  cases height with
  | zero =>
      funext code
      simp [arithmeticPeekCfgWires, peekCfgWires, peekStackWires,
        encodeHeadWires]
  | succ height => rfl

/-- The first runtime phase determined by a statement's outer constructor.
All wire operands are explicit; neither a builder nor wire-validity proofs
remain.  The support proof is fixed machine metadata. -/
def transitionStmtHeadPhase (tm : _root_.Turing.FinTM2) (height start : Nat)
    (falseWire trueWire : Nat) (source : CfgWires tm height)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    Option AffineStmtPhase :=
  match q with
  | halt => none
  | goto jump =>
      some (.oneHotMap (affineOneHotMapCanonicalGroups start source.state
        (stmtLabelTable tm jump)))
  | load update _ =>
      some (.oneHotMap (affineOneHotMapCanonicalGroups start source.state
        (stmtStateTable tm update)))
  | push k emit _ =>
      let symbolAt : Fin (stateCount tm) → SupportedSymbol tm k := fun code =>
        ⟨emit ((stateEquivFin tm).symm code),
          by
            apply hsupport k
            simp [stmtPushSet]⟩
      some (.oneHotMap (affineOneHotMapCanonicalGroups start source.state
        (fun code => encodeSupportedSymbol (symbolAt code))))
  | peek k update _ =>
      let head := arithmeticPeekCfgWires tm height falseWire trueWire source k
      some (.oneHotPairMap
        (affineOneHotPairMapAndFrames source.state head)
        (affineOneHotPairMapOrGroups start source.state head
          (stmtHeadStateTable tm k update)))
  | pop k _ _ => some (.pop (affinePopFrames source k))
  | branch test _ _ =>
      some (.oneHotPredicate
        (affineOneHotPredicateCanonicalFrames start source.state
          (stmtPredicateTable tm test)))

/-- The actual recursive statement script has exactly the builder-free leading
phase dictated by its outer syntax. -/
theorem compileStmtScript_head?_eq_transitionStmtHeadPhase
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm height) (hvalid : source.ValidIn base)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    (compileStmtScript tm height base pool source hvalid q hsupport).head? =
      transitionStmtHeadPhase tm height base.gates.length
        pool.falseWire pool.trueWire source q hsupport := by
  cases q <;> simp [compileStmtScript, transitionStmtHeadPhase]
  case peek =>
    rw [arithmeticPeekCfgWires_eq_peekCfgWires]
    simp

/-- Pure recursion for the leading phase of every label arm.  Starts advance
by the exact fixed statement cost and the following whole-row mux cost. -/
def transitionDispatchStatementHeads (tm : _root_.Turing.FinTM2)
    (height falseWire trueWire : Nat)
    (source : CfgWires tm (workHeight tm height)) :
    Nat → List tm.Λ → List (Option AffineStmtPhase)
  | _, [] => []
  | start, label :: labels =>
      transitionStmtHeadPhase tm (workHeight tm height) start
          falseWire trueWire source (tm.m label)
          (stmtPushSet_program_subset tm label) ::
        transitionDispatchStatementHeads tm height falseWire trueWire source
          (start + compileStmtGateCost tm (workHeight tm height) (tm.m label) +
            (3 * cfgBitCount tm (workHeight tm height) + 1)) labels

/-- Artifact recursion agrees exactly with the builder-free leading-phase
recursion for any dispatch suffix. -/
theorem compileDispatchLabelsListArtifacts_statementHeads_eq
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source fallback : CfgWires tm (workHeight tm height))
    (hsource : source.ValidIn base) (hfallback : fallback.ValidIn base)
    (labels : List tm.Λ) :
    (compileDispatchLabelsListArtifacts tm height base pool source fallback
        hsource hfallback labels).map (fun artifact => artifact.statement.head?) =
      transitionDispatchStatementHeads tm height pool.falseWire pool.trueWire
        source base.gates.length labels := by
  induction labels generalizing base fallback with
  | nil => rfl
  | cons label labels ih =>
      simp only [compileDispatchLabelsListArtifacts, List.map_cons,
        transitionDispatchStatementHeads]
      rw [compileStmtScript_head?_eq_transitionStmtHeadPhase]
      rw [ih]
      congr 2
      rw [cfgMux_gate_delta, compileStmt_gate_delta]

/-- Leading statement phases of the complete fixed-label dispatch, decoded
directly from one transition seed. -/
def transitionDispatchStatementHeadsFromSeed
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (Option AffineStmtPhase) :=
  transitionDispatchStatementHeads tm seed.height seed.start (seed.start + 1)
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
    (seed.start + 2) (programLabels tm)

/-- The proof-carrying dispatch artifacts' leading statement phases are
exactly the seed-derived family. -/
theorem arithmeticWidening_dispatchArtifact_statementHeads_eq_seed
    (tm : _root_.Turing.FinTM2) (height rowBase : Nat)
    (base : CircuitBuilder)
    (hvalid : (arithmeticCfgWires tm height rowBase).ValidIn base) :
    let widened := widenCfg base (arithmeticCfgWires tm height rowBase) hvalid
    (compileDispatchArtifacts tm height widened.builder widened.constants
        widened.wires widened.valid).map
        (fun artifact => artifact.statement.head?) =
      transitionDispatchStatementHeadsFromSeed tm
        { height := height, start := base.gates.length, rowBase := rowBase } := by
  dsimp only [compileDispatchArtifacts]
  rw [compileDispatchLabelsListArtifacts_statementHeads_eq]
  unfold transitionDispatchStatementHeadsFromSeed
  rw [widenCfg_falseWire_eq, widenCfg_trueWire_eq,
    widenCfg_arithmetic_wires_eq, widenCfg_gate_delta]

/-! ## Static phase schedule -/

/-- The five controller phase tags, with every numeric operand erased. -/
inductive TransitionStmtPhaseKind
  | oneHotMap
  | oneHotPredicate
  | oneHotPairMap
  | pop
  | mux
deriving DecidableEq, Repr

/-- Erase one concrete phase to its controller tag. -/
def transitionStmtPhaseKind : AffineStmtPhase → TransitionStmtPhaseKind
  | .oneHotMap _ => .oneHotMap
  | .oneHotPredicate _ => .oneHotPredicate
  | .oneHotPairMap _ _ => .oneHotPairMap
  | .pop _ => .pop
  | .mux _ _ => .mux

/-- Complete phase-tag schedule determined solely by statement syntax. -/
def transitionStmtPhaseKinds (tm : _root_.Turing.FinTM2) :
    _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ → List TransitionStmtPhaseKind
  | halt => []
  | goto _ => [.oneHotMap]
  | load _ continuation => .oneHotMap :: transitionStmtPhaseKinds tm continuation
  | push _ _ continuation =>
      .oneHotMap :: transitionStmtPhaseKinds tm continuation
  | peek _ _ continuation =>
      .oneHotPairMap :: transitionStmtPhaseKinds tm continuation
  | pop _ _ continuation =>
      .pop :: .oneHotPairMap :: transitionStmtPhaseKinds tm continuation
  | branch _ whenTrue whenFalse =>
      .oneHotPredicate ::
        (transitionStmtPhaseKinds tm whenTrue ++
          transitionStmtPhaseKinds tm whenFalse ++ [.mux])

/-- Erasing operands from the actual recursive statement script yields the
syntax-only phase schedule. -/
theorem compileStmtScript_phaseKinds_eq
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm height) (hvalid : source.ValidIn base)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    (compileStmtScript tm height base pool source hvalid q hsupport).map
        transitionStmtPhaseKind =
      transitionStmtPhaseKinds tm q := by
  induction q generalizing base source with
  | halt => rfl
  | goto jump => rfl
  | load update continuation ih =>
      simp only [compileStmtScript, List.map_cons, transitionStmtPhaseKind,
        transitionStmtPhaseKinds]
      rw [ih]
  | push k emit continuation ih =>
      simp only [compileStmtScript, List.map_cons, transitionStmtPhaseKind,
        transitionStmtPhaseKinds]
      rw [ih]
  | peek k update continuation ih =>
      simp only [compileStmtScript, List.map_cons, transitionStmtPhaseKind,
        transitionStmtPhaseKinds]
      rw [ih]
  | pop k update continuation ih =>
      simp only [compileStmtScript, List.map_cons, transitionStmtPhaseKind,
        transitionStmtPhaseKinds]
      rw [ih]
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      simp only [compileStmtScript, List.map_cons, List.map_append,
        transitionStmtPhaseKind, transitionStmtPhaseKinds]
      rw [ihTrue, ihFalse]
      simp

/-- Static phase schedule for a suffix of the fixed program labels, including
the whole-row mux that follows every statement arm. -/
def transitionDispatchPhaseKindsForLabels
    (tm : _root_.Turing.FinTM2) : List tm.Λ → List TransitionStmtPhaseKind
  | [] => []
  | label :: labels =>
      transitionStmtPhaseKinds tm (tm.m label) ++ [.mux] ++
        transitionDispatchPhaseKindsForLabels tm labels

/-- The complete verifier-specific dispatch schedule. -/
def transitionDispatchPhaseKinds (tm : _root_.Turing.FinTM2) :
    List TransitionStmtPhaseKind :=
  transitionDispatchPhaseKindsForLabels tm (programLabels tm)

/-- Every dynamic dispatch script has the same fixed phase schedule. -/
theorem compileDispatchLabelsListScript_phaseKinds_eq
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source fallback : CfgWires tm (workHeight tm height))
    (hsource : source.ValidIn base) (hfallback : fallback.ValidIn base)
    (labels : List tm.Λ) :
    (compileDispatchLabelsListScript tm height base pool source fallback
        hsource hfallback labels).map transitionStmtPhaseKind =
      transitionDispatchPhaseKindsForLabels tm labels := by
  induction labels generalizing base fallback with
  | nil => rfl
  | cons label labels ih =>
      simp only [compileDispatchLabelsListScript,
        transitionDispatchPhaseKindsForLabels, List.map_append,
        List.map_cons, List.map_nil, transitionStmtPhaseKind]
      rw [compileStmtScript_phaseKinds_eq]
      rw [ih]

/-- In particular, the complete canonical-label dispatch has a phase-tag
stream that can be hard-coded for the fixed verifier machine. -/
theorem compileDispatchScript_phaseKinds_eq
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm (workHeight tm height))
    (hvalid : source.ValidIn base) :
    (compileDispatchScript tm height base pool source hvalid).map
        transitionStmtPhaseKind =
      transitionDispatchPhaseKinds tm := by
  exact compileDispatchLabelsListScript_phaseKinds_eq tm height base pool
    source source hvalid hvalid (programLabels tm)

end CLRS.Chapter34.Turing.CookLevin
