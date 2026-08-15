import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OneHotMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OneHotPredicate
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OneHotPairMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Pop
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.MuxFin

/-!
# Runtime script for recursive Cook--Levin statements

The primitive serializers already execute every gate family used by a bundled
statement.  This module freezes their exact recursive phase order in a tagged
runtime script.  The tags are the future controller's phase boundaries; the
script contains unary wire operands, never a pre-serialized target gate list.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin
open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- The five executable phase kinds needed by recursive statement compilation. -/
inductive AffineStmtPhase
  | oneHotMap (groups : List AffineOrFinGroup)
  | oneHotPredicate (frames : List AffineOrFinPairFrame)
  | oneHotPairMap (andFrames : List AffineAndFinPairFrame)
      (orGroups : List AffineOrFinGroup)
  | pop (frames : List AffineOrFinPairFrame)
  | mux (selector : Nat) (frames : List AffineMuxFinPairFrame)
deriving Repr

/-- Gate bytes emitted by one script phase. -/
def affineStmtPhaseGateStream : AffineStmtPhase → List CircuitSym
  | .oneHotMap groups => affineOrFinFamilyGateStream groups
  | .oneHotPredicate frames => affineOrFinGateStream frames
  | .oneHotPairMap andFrames orGroups =>
      affineAndThenOrGateStream andFrames orGroups
  | .pop frames => affineOrFinNoSeedGateStream frames
  | .mux selector frames => affineMuxFinGateStream selector frames

/-- Gate bytes emitted by a complete recursive statement script. -/
def affineStmtScriptGateStream (script : List AffineStmtPhase) :
    List CircuitSym :=
  script.flatMap affineStmtPhaseGateStream

@[simp] theorem affineStmtScriptGateStream_nil :
    affineStmtScriptGateStream [] = [] := rfl

@[simp] theorem affineStmtScriptGateStream_cons
    (phase : AffineStmtPhase) (script : List AffineStmtPhase) :
    affineStmtScriptGateStream (phase :: script) =
      affineStmtPhaseGateStream phase ++ affineStmtScriptGateStream script := by
  simp [affineStmtScriptGateStream]

@[simp] theorem affineStmtScriptGateStream_append
    (left right : List AffineStmtPhase) :
    affineStmtScriptGateStream (left ++ right) =
      affineStmtScriptGateStream left ++ affineStmtScriptGateStream right := by
  simp [affineStmtScriptGateStream, List.flatMap_append]

/-- Tags distinguish adjacent component inputs without storing target gates. -/
inductive AffineStmtScriptSym
  | oneHotMap
  | oneHotPredicate
  | oneHotPairMap
  | pop
  | mux
  | data (symbol : UnaryFrameSym)
deriving DecidableEq, Fintype, Repr

/-- Exact tagged unary input of one phase. -/
def encodeAffineStmtPhase : AffineStmtPhase → List AffineStmtScriptSym
  | .oneHotMap groups =>
      .oneHotMap :: (encodeAffineOrFinGroups groups).map .data
  | .oneHotPredicate frames =>
      .oneHotPredicate :: (encodeAffineOrFinFrames frames).map .data
  | .oneHotPairMap andFrames orGroups =>
      .oneHotPairMap ::
        (encodeAffineAndThenOrInput andFrames orGroups).map .data
  | .pop frames =>
      .pop :: (encodeAffineOrFinFrames frames).map .data
  | .mux selector frames =>
      .mux :: (encodeAffineMuxFinFrames selector frames).map .data

/-- Exact tagged unary input of a complete statement script. -/
def encodeAffineStmtScript (script : List AffineStmtPhase) :
    List AffineStmtScriptSym :=
  script.flatMap encodeAffineStmtPhase

@[simp] theorem encodeAffineStmtPhase_length (phase : AffineStmtPhase) :
    (encodeAffineStmtPhase phase).length =
      match phase with
      | .oneHotMap groups => (encodeAffineOrFinGroups groups).length + 1
      | .oneHotPredicate frames => (encodeAffineOrFinFrames frames).length + 1
      | .oneHotPairMap andFrames orGroups =>
          (encodeAffineAndThenOrInput andFrames orGroups).length + 1
      | .pop frames => (encodeAffineOrFinFrames frames).length + 1
      | .mux selector frames =>
          (encodeAffineMuxFinFrames selector frames).length + 1 := by
  cases phase <;> simp [encodeAffineStmtPhase]

/-- Sum of the already-proved standalone component runtimes.  The future
continuous controller removes intermediate halts, so this is a conservative
phase-composition budget rather than an execution claim. -/
def affineStmtPhaseStandaloneSteps : AffineStmtPhase → Nat
  | .oneHotMap groups => affineOrFinFamilyRevSteps groups
  | .oneHotPredicate frames => affineOrFinRevSteps frames
  | .oneHotPairMap andFrames orGroups =>
      affineAndThenOrRevSteps andFrames orGroups
  | .pop frames => affineOrFinNoSeedRevSteps frames
  | .mux selector frames => affineMuxFinRevSteps selector frames

def affineStmtScriptStandaloneSteps (script : List AffineStmtPhase) : Nat :=
  (script.map affineStmtPhaseStandaloneSteps).sum

/-- Every tagged phase inherits a uniform linear budget from its concrete
primitive serializer. -/
theorem affineStmtPhaseStandaloneSteps_le (phase : AffineStmtPhase) :
    affineStmtPhaseStandaloneSteps phase ≤
      200 * (encodeAffineStmtPhase phase).length := by
  cases phase with
  | oneHotMap groups =>
      have h := affineOrFinFamilyRev_steps_le groups
      simp [affineStmtPhaseStandaloneSteps, encodeAffineStmtPhase]
      omega
  | oneHotPredicate frames =>
      have h := affineOrFinRev_steps_le frames
      simp [affineStmtPhaseStandaloneSteps, encodeAffineStmtPhase]
      omega
  | oneHotPairMap andFrames orGroups =>
      have h := affineAndThenOrRev_steps_le andFrames orGroups
      simp [affineStmtPhaseStandaloneSteps, encodeAffineStmtPhase]
      omega
  | pop frames =>
      have h := affineOrFinNoSeedRev_steps_le frames
      simp [affineStmtPhaseStandaloneSteps, encodeAffineStmtPhase]
      omega
  | mux selector frames =>
      have h := affineMuxFinRev_steps_le selector frames
      simp [affineStmtPhaseStandaloneSteps, encodeAffineStmtPhase]
      omega

/-- The complete recursive script has a linear aggregate component budget in
its exact tagged unary encoding. -/
theorem affineStmtScriptStandaloneSteps_le (script : List AffineStmtPhase) :
    affineStmtScriptStandaloneSteps script ≤
      200 * (encodeAffineStmtScript script).length := by
  induction script with
  | nil => rfl
  | cons phase rest ih =>
      have hphase := affineStmtPhaseStandaloneSteps_le phase
      simp only [affineStmtScriptStandaloneSteps, List.map_cons, List.sum_cons,
        encodeAffineStmtScript, List.flatMap_cons, List.length_append]
      simp only [affineStmtScriptStandaloneSteps, encodeAffineStmtScript] at ih
      omega

/-- Canonical primitive script produced by one fixed bundled statement. -/
def compileStmtScript (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm H) (hvalid : source.ValidIn base)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    List AffineStmtPhase :=
  match q with
  | halt => []
  | goto jump =>
      [.oneHotMap (affineOneHotMapCanonicalGroups base.gates.length
        source.state (stmtLabelTable tm jump))]
  | load update continuation =>
      let hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      let mapped := oneHotMap base source.state (stmtStateTable tm update)
        hvalid.state
      let wires := source.replaceState mapped.wires
      let hwires : CfgWires.ValidIn wires mapped.builder :=
        (hvalid.mono mapped.extension).replaceState mapped.valid
      .oneHotMap (affineOneHotMapCanonicalGroups base.gates.length
          source.state (stmtStateTable tm update)) ::
        compileStmtScript tm H mapped.builder (pool.mono mapped.extension)
          wires hwires continuation hcontinuation
  | push k emit continuation =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        intro j symbol hsymbol
        apply hsupport j
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let symbolAt : Fin (stateCount tm) → SupportedSymbol tm k := fun code =>
        ⟨emit ((stateEquivFin tm).symm code), by
          apply hsupport k
          simp [stmtPushSet]⟩
      let mapped := oneHotMap base source.state
        (fun code => encodeSupportedSymbol (symbolAt code)) hvalid.state
      let nextPool := pool.mono mapped.extension
      let wires := pushCfgWires nextPool mapped.wires source
      let hwires : CfgWires.ValidIn wires mapped.builder :=
        pushCfgWires_valid nextPool mapped.wires source mapped.valid
          (hvalid.mono mapped.extension)
      .oneHotMap (affineOneHotMapCanonicalGroups base.gates.length source.state
          (fun code => encodeSupportedSymbol (symbolAt code))) ::
        compileStmtScript tm H mapped.builder nextPool wires hwires
          continuation hcontinuation
  | peek k update continuation =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      let head := peekCfgWires k pool source
      let mapped := oneHotPairMap base source.state head
        (stmtHeadStateTable tm k update) hvalid.state
        (peekCfgWires_valid k pool source hvalid)
      let wires := source.replaceState mapped.wires
      let hwires : CfgWires.ValidIn wires mapped.builder :=
        (hvalid.mono mapped.extension).replaceState mapped.valid
      .oneHotPairMap (affineOneHotPairMapAndFrames source.state head)
          (affineOneHotPairMapOrGroups base.gates.length source.state head
            (stmtHeadStateTable tm k update)) ::
        compileStmtScript tm H mapped.builder (pool.mono mapped.extension)
          wires hwires continuation hcontinuation
  | pop k update continuation =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      let popped := popCfgWires base pool source hvalid k
      let mapped := oneHotPairMap popped.builder popped.wires.state popped.head
        (stmtHeadStateTable tm k update) popped.valid.state popped.headValid
      let wires := popped.wires.replaceState mapped.wires
      let hwires : CfgWires.ValidIn wires mapped.builder :=
        (popped.valid.mono mapped.extension).replaceState mapped.valid
      let hext := popped.extension.trans mapped.extension
      .pop (affinePopFrames source k) ::
        .oneHotPairMap
            (affineOneHotPairMapAndFrames popped.wires.state popped.head)
            (affineOneHotPairMapOrGroups popped.builder.gates.length
              popped.wires.state popped.head (stmtHeadStateTable tm k update)) ::
          compileStmtScript tm H mapped.builder (pool.mono hext) wires hwires
            continuation hcontinuation
  | branch test whenTrue whenFalse =>
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
      let predicate := oneHotPredicate base source.state
        (stmtPredicateTable tm test) hvalid.state
      let trueScript := compileStmtScript tm H predicate.builder
        (pool.mono predicate.extension) source
        (hvalid.mono predicate.extension) whenTrue htrueSupport
      let trueResult := compileStmt tm H predicate.builder
        (pool.mono predicate.extension) source
        (hvalid.mono predicate.extension) whenTrue htrueSupport
      let hbaseFalse := predicate.extension.trans trueResult.extension
      let falseScript := compileStmtScript tm H trueResult.builder
        (pool.mono hbaseFalse) source (hvalid.mono hbaseFalse)
        whenFalse hfalseSupport
      let falseResult := compileStmt tm H trueResult.builder
        (pool.mono hbaseFalse) source (hvalid.mono hbaseFalse)
        whenFalse hfalseSupport
      .oneHotPredicate (affineOneHotPredicateCanonicalFrames base.gates.length
          source.state (stmtPredicateTable tm test)) ::
        trueScript ++ falseScript ++
          [.mux predicate.wire
            (affineMuxFinCanonicalFrames falseResult.builder.gates.length
              predicate.wire _
              (fun i => trueResult.wires ((cfgSlotEquivFin tm H).symm i))
              (fun i => falseResult.wires ((cfgSlotEquivFin tm H).symm i)))]

/-- Interpreting the canonical runtime script yields the exact structural
statement trace, byte for byte and in recursive compiler order. -/
theorem compileStmtScript_gateStream_eq_trace
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm H) (hvalid : source.ValidIn base)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    affineStmtScriptGateStream
        (compileStmtScript tm H base pool source hvalid q hsupport) =
      (compileStmtGateTrace tm H base pool source hvalid q hsupport).flatMap
        encodeCircuitGate := by
  induction q generalizing base source with
  | halt => rfl
  | goto jump =>
      simp [compileStmtScript, compileStmtGateTrace,
        affineStmtScriptGateStream,
        affineStmtPhaseGateStream, affineOneHotMapGateStream_eq_trace]
  | load update continuation ih =>
      classical
      simp only [compileStmtScript, compileStmtGateTrace,
        affineStmtScriptGateStream_cons,
        affineStmtPhaseGateStream]
      rw [affineOneHotMapGateStream_eq_trace]
      rw [ih]
      simp [List.flatMap_append]
  | push k emit continuation ih =>
      classical
      simp only [compileStmtScript, compileStmtGateTrace,
        affineStmtScriptGateStream_cons,
        affineStmtPhaseGateStream]
      rw [affineOneHotMapGateStream_eq_trace]
      rw [ih]
      simp [List.flatMap_append]
  | peek k update continuation ih =>
      classical
      simp only [compileStmtScript, compileStmtGateTrace,
        affineStmtScriptGateStream_cons,
        affineStmtPhaseGateStream]
      rw [affineOneHotPairMapGateStream_eq_trace]
      rw [ih]
      simp [List.flatMap_append]
  | pop k update continuation ih =>
      classical
      simp only [compileStmtScript, compileStmtGateTrace,
        affineStmtScriptGateStream_cons,
        affineStmtPhaseGateStream]
      rw [affinePopGateStream_eq_trace]
      rw [affineOneHotPairMapGateStream_eq_trace]
      rw [ih]
      simp [List.flatMap_append]
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      classical
      simp only [compileStmtScript, compileStmtGateTrace,
        affineStmtScriptGateStream_cons, affineStmtScriptGateStream_append,
        affineStmtScriptGateStream_nil, affineStmtPhaseGateStream,
        List.flatMap_append, List.append_nil]
      rw [affineOneHotPredicateGateStream_eq_trace]
      rw [ihTrue]
      rw [ihFalse]
      rw [affineMuxFinCanonicalGateStream_eq_trace]

end CLRS.Chapter34.Turing.PolyBuilder
