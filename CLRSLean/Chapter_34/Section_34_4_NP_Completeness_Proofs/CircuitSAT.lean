import Mathlib.Tactic
import CLRSLean.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility

/-!
# CIRCUIT-SAT poly-reduces to SAT

The reduction of CLRS Lemma 34.6: a boolean circuit is satisfiable iff the
boolean formula obtained by asserting the consistency of every gate (and the
output) is satisfiable.  The construction introduces a variable per wire and
one `↔`-formula per gate.

Main results:

- Model `Formula` (variables, constants, `not`/`and`/`or`/`iff`) with
  evaluation `Formula.eval` and `satisfiable`.
- Model `Gate` (input, constant, `not`/`and`/`or`) and a circuit as a list of
  gates, with wire evaluation `evalWire` and `circuitSatisfiable`.
- The reduction `circuitToFormula`, and the correctness theorem
  `circuitSatisfiable_iff_satisfiable_circuitToFormula` (Lemma 34.6, the
  semantic half).

**Current status**: the semantic equivalence, the list encoding, the machine
program, and the first two phase lemmas (count, reorder) are in place.  The
machine's `copyCnt` loops (header/gate-loop variable emission) have a known
design bug — they pop a counter unit and push it back (restoring the counter,
so the loop never terminates).  The fix is to add a scratch stack and use a
move-then-restore copy (counter → scratch → output+counter).  The
`outputsFun` (phase simulations, time bound, `TM2ComputableInPolyTime`
instance, and the assembled `PolyTimeReducible CIRCUIT_SAT SAT`) is pending
that fix.

Design (offset wires so every gate has two predecessors):

- Wire `0` and wire `1` are the circuit's input wires (their value is chosen
  by the assignment `σ`).
- Gate `i` (0-indexed) produces wire `i + 2`, whose inputs are wires
  `i + 1` and `i`.  So a circuit with `n` gates has wires `0..n+1`, and the
  output is the last wire `n + 1`.
- `circuitToFormula gates` is `x_{n+1} ∧ ⋀ᵢ (x_{i+2} ↔ gateExprᵢ)`, where
  `gateExprᵢ` is the value of gate `i` in terms of wires `i+1` and `i`.

With this offset, every wire referenced by a gate exists, so the equivalence
holds for **every** gate list (no well-formedness side condition).
-/

namespace CLRS

namespace Chapter34

/-- A boolean formula: variables indexed by `Nat`, constants, and the standard
connectives (including `↔`, used by the reduction). -/
inductive Formula : Type
  | var (i : Nat)
  | const (b : Bool)
  | not (f : Formula)
  | and (f g : Formula)
  | or (f g : Formula)
  | iff (f g : Formula)
deriving Repr, DecidableEq

namespace Formula

/-- Evaluate a formula under an assignment `σ : Nat → Bool` of its variables. -/
def eval : Formula → (Nat → Bool) → Bool
  | var i, σ => σ i
  | const b, σ => b
  | not f, σ => !eval f σ
  | and f g, σ => eval f σ && eval g σ
  | or f g, σ => eval f σ || eval g σ
  | iff f g, σ => eval f σ == eval g σ

/-- A formula is **satisfiable** when some assignment makes it true. -/
def Satisfiable (f : Formula) : Prop :=
  ∃ σ : Nat → Bool, eval f σ = true

end Formula

/-- A boolean circuit gate: an input wire, a constant, or a `not`/`and`/`or`
gate.  A circuit is a list of gates; gate `i` produces wire `i + 2`. -/
inductive Gate : Type
  | input
  | const (b : Bool)
  | not
  | and
  | or
deriving DecidableEq, Repr, Fintype, Inhabited

/-- The value of a circuit's gate `i` expressed as a formula in the two
predecessor wires `i + 1` and `i` (the wires feeding gate `i`). -/
def gateExpr (i : Nat) (g : Gate) : Formula :=
  match g with
  | Gate.input => Formula.var (i + 2)
  | Gate.const b => Formula.const b
  | Gate.not => Formula.not (Formula.var (i + 1))
  | Gate.and => Formula.and (Formula.var (i + 1)) (Formula.var i)
  | Gate.or => Formula.or (Formula.var (i + 1)) (Formula.var i)

/-- The value of wire `i` of a circuit, given an assignment `σ` to the input
wires `0` and `1`.  Wires `0`/`1` are the inputs; wire `i + 2` is gate `i`'s
output (and `false` when `i` is past the end of the gate list). -/
def evalWire (gates : List Gate) (σ : Nat → Bool) : Nat → Bool
  | 0 => σ 0
  | 1 => σ 1
  | i + 2 =>
      match gates[i]? with
      | none => false
      | some Gate.input => σ (i + 2)
      | some (Gate.const b) => b
      | some Gate.not => !evalWire gates σ (i + 1)
      | some Gate.and => evalWire gates σ (i + 1) && evalWire gates σ i
      | some Gate.or => evalWire gates σ (i + 1) || evalWire gates σ i

/-- The consistency formula for a gate: the gate's output wire equals the
value of its expression in the predecessor wires. -/
def gateFormula (i : Nat) (g : Gate) : Formula :=
  Formula.iff (Formula.var (i + 2)) (gateExpr i g)

/-- The conjunction of the consistency formulas of all gates, in gate order,
tracking the wire index. -/
def gateFormulasAux : Nat → List Gate → Formula
  | _, [] => Formula.const true
  | i, g :: rest => Formula.and (gateFormula i g) (gateFormulasAux (i + 1) rest)

/-- The conjunction of the consistency formulas of all gates, in gate order. -/
def gateFormulas (gates : List Gate) : Formula :=
  gateFormulasAux 0 gates

/-- A circuit is **satisfiable** when some assignment to the input wires makes
the output wire (the last wire, `gates.length + 1`) true. -/
def CircuitSatisfiable (gates : List Gate) : Prop :=
  ∃ σ : Nat → Bool, evalWire gates σ (gates.length + 1) = true

/--
**The CIRCUIT-SAT → SAT reduction** (CLRS Lemma 34.6).  Assert the output wire
and the consistency of every gate.
-/
def circuitToFormula (gates : List Gate) : Formula :=
  Formula.and (Formula.var (gates.length + 1)) (gateFormulas gates)

/-- The value of gate `i`'s output wire equals the evaluation of its
expression formula under the wire-value assignment. -/
lemma evalWire_eq_gateExpr (g : Gate) {gates : List Gate} {σ : Nat → Bool} {i : Nat}
    (h : gates[i]? = some g) :
    evalWire gates σ (i + 2) = Formula.eval (gateExpr i g) (evalWire gates σ) := by
  cases g with
  | input => simp [evalWire, gateExpr, Formula.eval, h]
  | const b => simp [evalWire, gateExpr, Formula.eval, h]
  | not => simp [evalWire, gateExpr, Formula.eval, h]
  | and => simp [evalWire, gateExpr, Formula.eval, h]
  | or => simp [evalWire, gateExpr, Formula.eval, h]

/-- For a wire that is actually produced by gate `i`, its value equals the
evaluation of the gate's expression formula under the wire-value assignment. -/
lemma evalWire_eq_gateExpr' {gates : List Gate} {σ : Nat → Bool} {i : Nat}
    (hi : i < gates.length) :
    evalWire gates σ (i + 2) = Formula.eval (gateExpr i (gates.get ⟨i, hi⟩)) (evalWire gates σ) := by
  exact evalWire_eq_gateExpr (gates.get ⟨i, hi⟩) (List.getElem?_eq_getElem hi)

/-- `Bool` equality reflected as `==` is true exactly when the values are equal. -/
lemma beq_true_eq {a b : Bool} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> simp at h ⊢

/-- The `getElem?` at the boundary of `pre ++ g :: rest` is `g`. -/
lemma getElem?_append_cons (pre : List Gate) (g : Gate) (rest : List Gate) :
    (pre ++ g :: rest)[pre.length]? = some g := by
  rw [List.getElem?_append_right (Nat.le_refl pre.length)]
  simpa [Nat.sub_self]

/-- The conjunction of all gate-consistency formulas, from a suffix of the gate
list, evaluates to true under the wire-value assignment. -/
lemma eval_gateFormulasAux (pre rest : List Gate) (σ : Nat → Bool) :
    Formula.eval (gateFormulasAux pre.length rest) (evalWire (pre ++ rest) σ) = true := by
  induction rest generalizing pre with
  | nil => simp [gateFormulasAux, Formula.eval]
  | cons g rest' ih =>
      have hfirst : Formula.eval (gateFormula pre.length g) (evalWire (pre ++ g :: rest') σ) = true := by
        rw [gateFormula]
        simp [Formula.eval]
        rw [evalWire_eq_gateExpr g]
        · exact getElem?_append_cons pre g rest'
      have hrest : Formula.eval (gateFormulasAux (pre.length + 1) rest') (evalWire (pre ++ g :: rest') σ) = true := by
        have hih := ih (pre := pre ++ [g])
        simpa [List.length_append, List.append_assoc] using hih
      simp [gateFormulasAux, Formula.eval, hfirst, hrest]

/-- The conjunction of the consistency formulas of all gates evaluates to true
under the wire-value assignment. -/
lemma eval_gateFormulas (gates : List Gate) (σ : Nat → Bool) :
    Formula.eval (gateFormulas gates) (evalWire gates σ) = true := by
  simpa [gateFormulas] using (eval_gateFormulasAux [] gates σ)

/-- If the conjunction of gate formulas evaluates to true, then every individual
gate's consistency formula evaluates to true. -/
lemma eval_gateFormulasAux_true {τ : Nat → Bool} (i : Nat) : ∀ rest : List Gate,
    Formula.eval (gateFormulasAux i rest) τ = true →
      ∀ j : Nat, (hj : j < rest.length) → Formula.eval (gateFormula (i + j) (rest.get ⟨j, hj⟩)) τ = true := by
  intro rest
  induction rest generalizing i with
  | nil =>
      intro h j hj
      exfalso
      simpa using hj
  | cons g rest' ih =>
      intro h j hj
      cases j with
      | zero =>
          simp [gateFormulasAux, Formula.eval, Bool.and_eq_true] at h
          simpa using h.1
      | succ j' =>
          have hrest : Formula.eval (gateFormulasAux (i + 1) rest') τ = true := by
            simp [gateFormulasAux, Formula.eval, Bool.and_eq_true] at h
            exact h.2
          have hj' : j' < rest'.length := by simpa using hj
          have hgoal := ih (i := i + 1) hrest j' hj'
          have hidx : i + (j' + 1) = (i + 1) + j' := by omega
          have helt : (g :: rest').get ⟨j' + 1, hj⟩ = rest'.get ⟨j', hj'⟩ := by
            simpa [List.getElem_cons_succ]
          rw [hidx, helt]
          exact hgoal

/-- Under a satisfying assignment of `circuitToFormula gates`, every wire's value
matches the assignment's value for that variable. -/
lemma evalWire_eq_tau (gates : List Gate) (τ : Nat → Bool)
    (hτ : Formula.eval (circuitToFormula gates) τ = true) :
    ∀ j : Nat, j ≤ gates.length + 1 → evalWire gates τ j = τ j := by
  have hgf : Formula.eval (gateFormulas gates) τ = true := by
    rw [circuitToFormula] at hτ
    simp [Formula.eval, Bool.and_eq_true] at hτ
    exact hτ.2
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hj
      match j with
      | 0 => simp [evalWire]
      | 1 => simp [evalWire]
      | i + 2 =>
          by_cases hi : i < gates.length
          · have hcons := eval_gateFormulasAux_true (τ := τ) 0 gates hgf i hi
            have hτi1 : evalWire gates τ (i + 1) = τ (i + 1) := ih (i + 1) (by omega) (by omega)
            have hτi : evalWire gates τ i = τ i := ih i (by omega) (by omega)
            cases g : gates.get ⟨i, hi⟩ with
            | input =>
                have hget : gates[i] = Gate.input := by simpa using g
                simp [evalWire, hget, List.getElem?_eq_getElem hi]
            | const b =>
                have hget : gates[i] = Gate.const b := by simpa using g
                have hgate : τ (i + 2) = b := by
                  rw [gateFormula] at hcons
                  simp [Formula.eval, gateExpr, hget] at hcons
                  exact hcons
                simp [evalWire, hget, hgate, List.getElem?_eq_getElem hi]
            | not =>
                have hget : gates[i] = Gate.not := by simpa using g
                have hgate : τ (i + 2) = !τ (i + 1) := by
                  rw [gateFormula] at hcons
                  simp [Formula.eval, gateExpr, hget] at hcons
                  exact hcons
                simp [evalWire, hget, hτi1, hgate, List.getElem?_eq_getElem hi]
            | and =>
                have hget : gates[i] = Gate.and := by simpa using g
                have hgate : τ (i + 2) = (τ (i + 1) && τ i) := by
                  rw [gateFormula] at hcons
                  simp [Formula.eval, gateExpr, hget] at hcons
                  exact hcons
                simp [evalWire, hget, hτi1, hτi, hgate, List.getElem?_eq_getElem hi]
            | or =>
                have hget : gates[i] = Gate.or := by simpa using g
                have hgate : τ (i + 2) = (τ (i + 1) || τ i) := by
                  rw [gateFormula] at hcons
                  simp [Formula.eval, gateExpr, hget] at hcons
                  exact hcons
                simp [evalWire, hget, hτi1, hτi, hgate, List.getElem?_eq_getElem hi]
          · exfalso
            omega

/--
**Theorem (CIRCUIT-SAT poly-reduces to SAT, semantic half, Lemma 34.6).**  A
circuit is satisfiable iff the formula asserting the output wire and the
consistency of every gate is satisfiable.
-/
theorem circuitSatisfiable_iff_satisfiable_circuitToFormula (gates : List Gate) :
    CircuitSatisfiable gates ↔ Formula.Satisfiable (circuitToFormula gates) := by
  constructor
  · intro ⟨σ, hσ⟩
    refine ⟨evalWire gates σ, ?_⟩
    rw [circuitToFormula]
    simp [Formula.eval, hσ, eval_gateFormulas]
  · intro ⟨τ, hτ⟩
    refine ⟨τ, ?_⟩
    have hwire := evalWire_eq_tau gates τ hτ (gates.length + 1) (by omega)
    rw [hwire]
    rw [circuitToFormula] at hτ
    simp [Formula.eval, Bool.and_eq_true] at hτ
    exact hτ.1

/-- The output alphabet of the reduction: prefix-polish formula symbols. -/
inductive FormulaSym : Type
  | lit (b : Bool)
  | varMark | endMark
  | notMark | andMark | orMark | iffMark
deriving DecidableEq, Repr, Fintype, Inhabited

/-- Encode a variable as `varMark` followed by `i + 1` `endMark`s (unary index). -/
def varEnc (i : Nat) : List FormulaSym :=
  FormulaSym.varMark :: List.replicate (i + 1) FormulaSym.endMark

/-- Encode a formula in prefix-polish form. -/
def enc : Formula → List FormulaSym
  | Formula.var i => varEnc i
  | Formula.const b => [FormulaSym.lit b]
  | Formula.not f => FormulaSym.notMark :: enc f
  | Formula.and f g => FormulaSym.andMark :: (enc f ++ enc g)
  | Formula.or f g => FormulaSym.orMark :: (enc f ++ enc g)
  | Formula.iff f g => FormulaSym.iffMark :: (enc f ++ enc g)

/-- Encode a gate's expression formula (in terms of the wire index) as a list. -/
def gateExprEnc (i : Nat) (g : Gate) : List FormulaSym :=
  match g with
  | Gate.input => varEnc (i + 2)
  | Gate.const b => [FormulaSym.lit b]
  | Gate.not => FormulaSym.notMark :: varEnc (i + 1)
  | Gate.and => FormulaSym.andMark :: (varEnc (i + 1) ++ varEnc i)
  | Gate.or => FormulaSym.orMark :: (varEnc (i + 1) ++ varEnc i)

/-- Encode the consistency formula of gate `i`. -/
def gateFormulaEnc (i : Nat) (g : Gate) : List FormulaSym :=
  FormulaSym.iffMark :: (varEnc (i + 2) ++ gateExprEnc i g)

/-- The list of gate-consistency encodings, each prefixed by `andMark`. -/
def gateFormulasList : Nat → List Gate → List FormulaSym
  | _, [] => []
  | i, g :: rest => (FormulaSym.andMark :: gateFormulaEnc i g) ++ gateFormulasList (i + 1) rest

/-- The reduction `circuitToFormula` at the list-encoding level: the header
(`andMark`, the output variable), each gate's consistency formula in order, and
the trailing `lit true`. -/
def circuitToFormulaList (gates : List Gate) : List FormulaSym :=
  FormulaSym.andMark :: (varEnc (gates.length + 1) ++ gateFormulasList 0 gates ++ [FormulaSym.lit true])

/-- The gate-consistency encoding agrees with `enc` on `gateFormula`. -/
lemma gateFormulaEnc_eq_enc (i : Nat) (g : Gate) :
    gateFormulaEnc i g = enc (gateFormula i g) := by
  cases g <;> simp [gateFormulaEnc, gateExprEnc, enc, gateFormula, gateExpr, varEnc]

/-- The list of gate-consistency encodings (plus the trailing `lit true`) agrees
with `enc` on the folded `gateFormulasAux`. -/
lemma gateFormulasList_eq_enc (i : Nat) (rest : List Gate) :
    gateFormulasList i rest ++ [FormulaSym.lit true] = enc (gateFormulasAux i rest) := by
  induction rest generalizing i with
  | nil => simp [gateFormulasList, gateFormulasAux, enc]
  | cons g rest' ih =>
      simp [gateFormulasList]
      rw [gateFormulaEnc_eq_enc i g]
      simp [gateFormulasAux, enc]
      rw [← ih]

/-- The list encoding agrees with `enc` on `circuitToFormula`. -/
lemma circuitToFormulaList_eq_enc (gates : List Gate) :
    circuitToFormulaList gates = enc (circuitToFormula gates) := by
  simp [circuitToFormulaList, circuitToFormula, enc, gateFormulas, gateFormulasList_eq_enc, List.append_assoc]

end Chapter34

end CLRS

namespace Turing

namespace TM2CS

open CLRS.Chapter34

inductive K : Type
  | inK | temp | buf | cnt | o | out
deriving DecidableEq, Fintype, Inhabited

abbrev Γk : K → Type
  | K.inK => Gate
  | K.temp => Gate
  | K.buf => Gate
  | K.cnt => Unit
  | K.o => FormulaSym
  | K.out => FormulaSym

inductive St : Type
  | init | done | cp
  | sym (s : FormulaSym)
  | gate (g : Gate)
  | gf (g : Gate)
  | emit (g : Gate)
deriving DecidableEq, Fintype, Inhabited

inductive Label : Type
  | count | reorder | header | copyHeader | reset
  | loop | copyGF | emitDispatch
  | emitInput | copyInput | emitConst | emitNot | copyNot
  | emitAnd | copyAnd1 | copyAnd2 | emitOr | copyOr1 | copyOr2
  | dec | emitTrue | copyOut | done
deriving DecidableEq, Fintype, Inhabited

def prog : Label → Turing.TM2.Stmt Γk Label St
  | Label.count =>
      Turing.TM2.Stmt.pop K.inK (fun _ x => match x with | some g => St.gate g | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.gate _ => true | _ => false)
          (Turing.TM2.Stmt.push K.temp (fun v => match v with | St.gate g => g | _ => default)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.count))))
          (Turing.TM2.Stmt.goto (fun _ => Label.reorder)))
  | Label.reorder =>
      Turing.TM2.Stmt.pop K.temp (fun _ x => match x with | some g => St.gate g | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.gate _ => true | _ => false)
          (Turing.TM2.Stmt.push K.buf (fun v => match v with | St.gate g => g | _ => default)
            (Turing.TM2.Stmt.goto (fun _ => Label.reorder)))
          (Turing.TM2.Stmt.goto (fun _ => Label.header)))
  | Label.header =>
      Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.andMark)
        (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.varMark)
          (Turing.TM2.Stmt.goto (fun _ => Label.copyHeader)))
  | Label.copyHeader =>
      Turing.TM2.Stmt.pop K.cnt (fun _ x => match x with | some () => St.cp | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.cp => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.copyHeader))))
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
              (Turing.TM2.Stmt.goto (fun _ => Label.reset)))))
  | Label.reset =>
      Turing.TM2.Stmt.pop K.cnt (fun _ x => match x with | some () => St.cp | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.cp => true | _ => false)
          (Turing.TM2.Stmt.goto (fun _ => Label.reset))
          (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.loop))))
  | Label.loop =>
      Turing.TM2.Stmt.pop K.buf (fun _ x => match x with | some g => St.gf g | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.gf _ => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.andMark)
            (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.iffMark)
              (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.varMark)
                (Turing.TM2.Stmt.goto (fun _ => Label.copyGF)))))
          (Turing.TM2.Stmt.goto (fun _ => Label.emitTrue)))
  | Label.copyGF =>
      Turing.TM2.Stmt.pop K.cnt (fun v x => match x with | some () => St.cp | none => match v with | St.gf g => St.emit g | _ => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.cp => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.copyGF))))
          (Turing.TM2.Stmt.goto (fun _ => Label.emitDispatch)))
  | Label.emitDispatch =>
      Turing.TM2.Stmt.branch (fun v => match v with | St.emit Gate.input => true | _ => false)
        (Turing.TM2.Stmt.goto (fun _ => Label.emitInput))
        (Turing.TM2.Stmt.branch (fun v => match v with | St.emit (Gate.const _) => true | _ => false)
          (Turing.TM2.Stmt.goto (fun _ => Label.emitConst))
          (Turing.TM2.Stmt.branch (fun v => match v with | St.emit Gate.not => true | _ => false)
            (Turing.TM2.Stmt.goto (fun _ => Label.emitNot))
            (Turing.TM2.Stmt.branch (fun v => match v with | St.emit Gate.and => true | _ => false)
              (Turing.TM2.Stmt.goto (fun _ => Label.emitAnd))
              (Turing.TM2.Stmt.goto (fun _ => Label.emitOr)))))
  | Label.emitInput =>
      Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.varMark)
        (Turing.TM2.Stmt.goto (fun _ => Label.copyInput))
  | Label.copyInput =>
      Turing.TM2.Stmt.pop K.cnt (fun _ x => match x with | some () => St.cp | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.cp => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.copyInput))))
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
              (Turing.TM2.Stmt.goto (fun _ => Label.dec)))))
  | Label.emitConst =>
      Turing.TM2.Stmt.push K.o (fun v => match v with | St.emit (Gate.const b) => FormulaSym.lit b | _ => default)
        (Turing.TM2.Stmt.goto (fun _ => Label.dec))
  | Label.emitNot =>
      Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.notMark)
        (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.varMark)
          (Turing.TM2.Stmt.goto (fun _ => Label.copyNot)))
  | Label.copyNot =>
      Turing.TM2.Stmt.pop K.cnt (fun _ x => match x with | some () => St.cp | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.cp => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.copyNot))))
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.goto (fun _ => Label.dec))))
  | Label.emitAnd =>
      Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.andMark)
        (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.varMark)
          (Turing.TM2.Stmt.goto (fun _ => Label.copyAnd1)))
  | Label.copyAnd1 =>
      Turing.TM2.Stmt.pop K.cnt (fun _ x => match x with | some () => St.cp | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.cp => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.copyAnd1))))
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.varMark)
            (Turing.TM2.Stmt.goto (fun _ => Label.copyAnd2))))
  | Label.copyAnd2 =>
      Turing.TM2.Stmt.pop K.cnt (fun _ x => match x with | some () => St.cp | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.cp => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.copyAnd2))))
          (Turing.TM2.Stmt.goto (fun _ => Label.dec)))
  | Label.emitOr =>
      Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.orMark)
        (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.varMark)
          (Turing.TM2.Stmt.goto (fun _ => Label.copyOr1)))
  | Label.copyOr1 =>
      Turing.TM2.Stmt.pop K.cnt (fun _ x => match x with | some () => St.cp | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.cp => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.copyOr1))))
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.varMark)
            (Turing.TM2.Stmt.goto (fun _ => Label.copyOr2))))
  | Label.copyOr2 =>
      Turing.TM2.Stmt.pop K.cnt (fun _ x => match x with | some () => St.cp | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.cp => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.copyOr2))))
          (Turing.TM2.Stmt.goto (fun _ => Label.dec)))
  | Label.dec =>
      Turing.TM2.Stmt.pop K.cnt (fun v _ => v) (Turing.TM2.Stmt.goto (fun _ => Label.loop))
  | Label.emitTrue =>
      Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.lit true)
        (Turing.TM2.Stmt.goto (fun _ => Label.copyOut))
  | Label.copyOut =>
      Turing.TM2.Stmt.pop K.o (fun _ x => match x with | some s => St.sym s | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.sym _ => true | _ => false)
          (Turing.TM2.Stmt.push K.out (fun v => match v with | St.sym s => s | _ => default)
            (Turing.TM2.Stmt.goto (fun _ => Label.copyOut)))
          (Turing.TM2.Stmt.goto (fun _ => Label.done)))
  | Label.done => Turing.TM2.Stmt.halt

abbrev mach : FinTM2 :=
  @FinTM2.mk K (by infer_instance) (by infer_instance) K.inK K.out Γk Label Label.count
    (by infer_instance) St St.init (by infer_instance) (by infer_instance) prog

def Sstep : (mach).Cfg → Option (mach).Cfg := mach.step

abbrev stk (gates T : List Gate) (c : Nat) (B : List Gate) (O U : List FormulaSym) :
    ∀ k : K, List (Γk k) :=
  fun k => match k with
  | K.inK => gates | K.temp => T | K.cnt => List.replicate c ()
  | K.buf => B | K.o => O | K.out => U

-- one count step on a nonempty `in`
lemma count_step (g : Gate) (rest : List Gate) (T : List Gate) (c : Nat)
    (B : List Gate) (O U : List FormulaSym) (v : St) :
    Sstep (⟨some Label.count, v, stk (g :: rest) T c B O U⟩ : (mach).Cfg)
      = some (⟨some Label.count, St.gate g, stk rest (g :: T) (c + 1) B O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, Nat.add_comm, Nat.add_assoc, prog, Sstep, List.replicate_succ]

-- count phase: move all gates from `in` to `temp` (reversed), counting into `cnt`
lemma count_phase_aux (v : St) (gates : List Gate) (T : List Gate) (c : Nat)
    (B : List Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[gates.length + 1]
        (some (⟨some Label.count, v, stk gates T c B O U⟩ : (mach).Cfg))
      = some (⟨some Label.reorder, St.done, stk [] (gates.reverse ++ T) (c + gates.length) B O U⟩ : (mach).Cfg) := by
  induction gates generalizing T c v with
  | nil =>
      have hhead : (stk [] T c B O U K.inK).head? = none := by simp [stk]
      have htail : (stk [] T c B O U K.inK).tail = [] := by simp [stk]
      have hc : (c + 0) = c := by omega
      have hrev : ([] : List Gate).reverse ++ T = T := by simp
      simp [Sstep, mach, prog, stk, flip, hhead, htail, hc, hrev]
  | cons g rest ih =>
      have hone := count_step g rest T c B O U v
      rw [show (g :: rest).length + 1 = (rest.length + 1) + 1 by simp [List.length_cons]]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[rest.length + 1]
          (Sstep (⟨some Label.count, v, stk (g :: rest) T c B O U⟩ : (mach).Cfg))
        = some (⟨some Label.reorder, St.done, stk [] ((g :: rest).reverse ++ T) (c + (g :: rest).length) B O U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (v := St.gate g) (T := g :: T) (c := c + 1)
      calc
        (flip bind Sstep)^[rest.length + 1]
            (some (⟨some Label.count, St.gate g, stk rest (g :: T) (c + 1) B O U⟩ : (mach).Cfg))
          = some (⟨some Label.reorder, St.done, stk [] (rest.reverse ++ (g :: T)) ((c + 1) + rest.length) B O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.reorder, St.done, stk [] ((g :: rest).reverse ++ T) (c + (g :: rest).length) B O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stk, List.reverse_cons, List.cons_append, List.append_assoc, List.length_cons, Nat.add_comm, Nat.add_assoc] <;> try omega

abbrev stkR (temp B : List Gate) (c : Nat) (O U : List FormulaSym) :
    ∀ k : K, List (Γk k) :=
  fun k => match k with
  | K.inK => [] | K.temp => temp | K.cnt => List.replicate c ()
  | K.buf => B | K.o => O | K.out => U

-- one reorder step on a nonempty temp
lemma reorder_step (g : Gate) (rest : List Gate) (B : List Gate) (c : Nat)
    (O U : List FormulaSym) (v : St) :
    Sstep (⟨some Label.reorder, v, stkR (g :: rest) B c O U⟩ : (mach).Cfg)
      = some (⟨some Label.reorder, St.gate g, stkR rest (g :: B) c O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkR, Function.update, prog, Sstep, List.replicate_succ]

-- reorder phase: move temp back onto buf (restoring the order)
lemma reorder_phase_aux (v : St) (temp : List Gate) (B : List Gate) (c : Nat)
    (O U : List FormulaSym) :
    (flip bind Sstep)^[temp.length + 1]
        (some (⟨some Label.reorder, v, stkR temp B c O U⟩ : (mach).Cfg))
      = some (⟨some Label.header, St.done, stkR [] (temp.reverse ++ B) c O U⟩ : (mach).Cfg) := by
  induction temp generalizing B v with
  | nil =>
      have hhead : (stkR [] B c O U K.temp).head? = none := by simp [stkR]
      have htail : (stkR [] B c O U K.temp).tail = [] := by simp [stkR]
      have hrev : ([] : List Gate).reverse ++ B = B := by simp
      simp [Sstep, mach, prog, stkR, flip, hhead, htail, hrev]
  | cons g rest ih =>
      have hone := reorder_step g rest B c O U v
      rw [show (g :: rest).length + 1 = (rest.length + 1) + 1 by simp [List.length_cons]]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[rest.length + 1]
          (Sstep (⟨some Label.reorder, v, stkR (g :: rest) B c O U⟩ : (mach).Cfg))
        = some (⟨some Label.header, St.done, stkR [] ((g :: rest).reverse ++ B) c O U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (v := St.gate g) (B := g :: B)
      calc
        (flip bind Sstep)^[rest.length + 1]
            (some (⟨some Label.reorder, St.gate g, stkR rest (g :: B) c O U⟩ : (mach).Cfg))
          = some (⟨some Label.header, St.done, stkR [] (rest.reverse ++ (g :: B)) c O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.header, St.done, stkR [] ((g :: rest).reverse ++ B) c O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkR, List.reverse_cons, List.cons_append, List.append_assoc, List.length_cons, Nat.add_comm, Nat.add_assoc] <;> try omega


end TM2CS

end Turing
