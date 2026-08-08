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
- The prefix-polish list encoding `enc`/`circuitToFormulaList`, the decoder
  `decode` (with `decode_enc`), and the languages `CIRCUIT_SAT` and `SAT`.
- The reduction TM2 machine `Turing.TM2CS.mach`, its phase simulation
  `csOutputsFun`, the polynomial time bound `csTime`, and the
  `csComputableInPolyTime` instance.
- The assembled **`circuitSAT_reducible_to_SAT`**: `CIRCUIT_SAT ≤_P SAT`
  (CLRS Lemma 34.6).

**Current status**: complete and kernel-clean.  The semantic equivalence, the
list encoding and decoding, the machine program (count/reorder/header/
loop/emitTrue/copyOut phases), the `outputsFun` phase simulation, the
polynomial time bound, and the assembled `PolyTimeReducible CIRCUIT_SAT SAT`
are all in place.

The machine emits each gate's clause in a move-then-restore pattern (counter →
scratch → output + counter), with the emit labels setting the carried state
via `load` so the move/restore phases stay uniform.

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

/-- Decode a unary variable index: after a `varMark`, `i + 1` `endMark`s encode
wire `i`.  This helper consumes the run of `endMark`s, adding their count to the
running index. -/
def decodeVarIdx : Nat → List FormulaSym → Formula × List FormulaSym
  | i, FormulaSym.endMark :: rest => decodeVarIdx (i + 1) rest
  | i, rest => (Formula.var i, rest)

/-- Decode the unary variable that starts with a `varMark` (already consumed). -/
def decodeVar : List FormulaSym → Formula × List FormulaSym
  | FormulaSym.endMark :: rest => decodeVarIdx 0 rest
  | rest => (Formula.const false, rest)

/-- Decode a single prefix-polish formula, returning it and the unconsumed
suffix.  The first argument is a budget of remaining connective levels; it only
needs to exceed the formula depth and equals the encoding length in `decode`.
Malformed or over-budget input yields the junk formula `const false`. -/
def decodeAux : Nat → List FormulaSym → Formula × List FormulaSym
  | 0, _ => (Formula.const false, [])
  | n + 1, [] => (Formula.const false, [])
  | n + 1, FormulaSym.lit b :: rest => (Formula.const b, rest)
  | n + 1, FormulaSym.varMark :: rest => decodeVar rest
  | n + 1, FormulaSym.notMark :: rest =>
      let (f, rest') := decodeAux n rest
      (Formula.not f, rest')
  | n + 1, FormulaSym.andMark :: rest =>
      let (f, rest') := decodeAux n rest
      let (g, rest'') := decodeAux n rest'
      (Formula.and f g, rest'')
  | n + 1, FormulaSym.orMark :: rest =>
      let (f, rest') := decodeAux n rest
      let (g, rest'') := decodeAux n rest'
      (Formula.or f g, rest'')
  | n + 1, FormulaSym.iffMark :: rest =>
      let (f, rest') := decodeAux n rest
      let (g, rest'') := decodeAux n rest'
      (Formula.iff f g, rest'')
  | n + 1, FormulaSym.endMark :: rest => (Formula.const false, rest)

/-- Decode a formula from its prefix-polish encoding (junk on malformed input). -/
def decode (syms : List FormulaSym) : Formula := (decodeAux syms.length syms).1

/-- A list that does not begin with an `endMark`, so that a variable's unary
index run cannot run into it.  The continuation after any formula encoding
satisfies this. -/
def ValidSuffix (syms : List FormulaSym) : Prop :=
  syms.head? ≠ some FormulaSym.endMark

/-- The empty continuation is valid. -/
lemma validSuffix_nil : ValidSuffix [] := by
  simp [ValidSuffix]

/-- The continuation after an encoded formula never begins with `endMark`. -/
lemma validSuffix_enc (f : Formula) (rest : List FormulaSym) : ValidSuffix (enc f ++ rest) := by
  cases f <;> simp [enc, varEnc, ValidSuffix]

/-- `decodeVarIdx` on a valid continuation leaves it untouched. -/
lemma decodeVarIdx_valid (i : Nat) {rest : List FormulaSym} (hv : ValidSuffix rest) :
    decodeVarIdx i rest = (Formula.var i, rest) := by
  cases rest with
  | nil => simp [decodeVarIdx]
  | cons s rest' =>
      have hsne : s ≠ FormulaSym.endMark := by
        intro hse
        apply hv
        rw [hse]
        rfl
      by_cases hse : s = FormulaSym.endMark
      · exfalso
        exact hsne hse
      · simp [decodeVarIdx, hse]

/-- `decodeVarIdx` consumes `j` `endMark`s, raising the index by `j` (leaving a
valid continuation untouched). -/
lemma decodeVarIdx_replicate (i j : Nat) {rest : List FormulaSym} (hv : ValidSuffix rest) :
    decodeVarIdx i (List.replicate j FormulaSym.endMark ++ rest) = (Formula.var (i + j), rest) := by
  induction j generalizing i with
  | zero => simpa using decodeVarIdx_valid i hv
  | succ j ih =>
      rw [List.replicate_succ, List.cons_append, decodeVarIdx]
      have h := ih (i + 1)
      rw [h]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- `decodeVar` recovers wire `j` from its `j + 1` `endMark`s (leaving a valid
continuation untouched). -/
lemma decodeVar_enc (j : Nat) {rest : List FormulaSym} (hv : ValidSuffix rest) :
    decodeVar (List.replicate (j + 1) FormulaSym.endMark ++ rest) = (Formula.var j, rest) := by
  have hrep : List.replicate (j + 1) FormulaSym.endMark =
      FormulaSym.endMark :: List.replicate j FormulaSym.endMark := by
    rw [show j + 1 = Nat.succ j by omega]
    simp [List.replicate_succ]
  rw [hrep, List.cons_append, decodeVar]
  rw [decodeVarIdx_replicate 0 j hv]
  simp

/-- Every formula encoding has length at least one. -/
lemma enc_length_pos (f : Formula) : 1 ≤ (enc f).length := by
  cases f <;> simp [enc, varEnc]

/-- `decodeAux` with a sufficient budget consumes exactly the encoding of a
formula, leaving a valid continuation untouched. -/
lemma decodeAux_enc_len (f : Formula) : ∀ m {rest : List FormulaSym}, ValidSuffix rest →
    (enc f).length ≤ m → decodeAux m (enc f ++ rest) = (f, rest) := by
  induction f with
  | var i =>
      intro m rest hv hm
      cases m with
      | zero => exfalso; have hpos := enc_length_pos (Formula.var i); omega
      | succ m =>
          simp [enc, decodeAux]
          exact decodeVar_enc i hv
  | const b =>
      intro m rest hv hm
      cases m with
      | zero => exfalso; have hpos := enc_length_pos (Formula.const b); omega
      | succ m => simp [enc, decodeAux]
  | not f ih =>
      intro m rest hv hm
      cases m with
      | zero => exfalso; have hpos := enc_length_pos (Formula.not f); omega
      | succ m =>
          have hlen : (enc (Formula.not f)).length = 1 + (enc f).length := by
            change (FormulaSym.notMark :: enc f).length = 1 + (enc f).length
            simp
            omega
          have hsub : (enc f).length ≤ m := by
            rw [hlen] at hm
            omega
          change (let (f', rest') := decodeAux m (enc f ++ rest); (Formula.not f', rest')) = (Formula.not f, rest)
          rw [ih m hv hsub]
  | and f g ihf ihg =>
      intro m rest hv hm
      cases m with
      | zero => exfalso; have hpos := enc_length_pos (Formula.and f g); omega
      | succ m =>
          have hlen : (enc (Formula.and f g)).length = 1 + (enc f).length + (enc g).length := by
            change (FormulaSym.andMark :: (enc f ++ enc g)).length = 1 + (enc f).length + (enc g).length
            simp [List.length_append]
            omega
          have hm' : 1 + (enc f).length + (enc g).length ≤ m + 1 := by
            rw [hlen] at hm
            exact hm
          have hf : (enc f).length ≤ m := by omega
          have hg : (enc g).length ≤ m := by omega
          change (let (f', rest') := decodeAux m (enc f ++ enc g ++ rest);
                  let (g', rest'') := decodeAux m rest'; (Formula.and f' g', rest'')) = (Formula.and f g, rest)
          have h1 : decodeAux m (enc f ++ enc g ++ rest) = (f, enc g ++ rest) := by
            simpa [List.append_assoc] using ihf m (validSuffix_enc g rest) hf
          rw [h1]
          simpa [ihg m hv hg]
  | or f g ihf ihg =>
      intro m rest hv hm
      cases m with
      | zero => exfalso; have hpos := enc_length_pos (Formula.or f g); omega
      | succ m =>
          have hlen : (enc (Formula.or f g)).length = 1 + (enc f).length + (enc g).length := by
            change (FormulaSym.orMark :: (enc f ++ enc g)).length = 1 + (enc f).length + (enc g).length
            simp [List.length_append]
            omega
          have hm' : 1 + (enc f).length + (enc g).length ≤ m + 1 := by
            rw [hlen] at hm
            exact hm
          have hf : (enc f).length ≤ m := by omega
          have hg : (enc g).length ≤ m := by omega
          change (let (f', rest') := decodeAux m (enc f ++ enc g ++ rest);
                  let (g', rest'') := decodeAux m rest'; (Formula.or f' g', rest'')) = (Formula.or f g, rest)
          have h1 : decodeAux m (enc f ++ enc g ++ rest) = (f, enc g ++ rest) := by
            simpa [List.append_assoc] using ihf m (validSuffix_enc g rest) hf
          rw [h1]
          simpa [ihg m hv hg]
  | iff f g ihf ihg =>
      intro m rest hv hm
      cases m with
      | zero => exfalso; have hpos := enc_length_pos (Formula.iff f g); omega
      | succ m =>
          have hlen : (enc (Formula.iff f g)).length = 1 + (enc f).length + (enc g).length := by
            change (FormulaSym.iffMark :: (enc f ++ enc g)).length = 1 + (enc f).length + (enc g).length
            simp [List.length_append]
            omega
          have hm' : 1 + (enc f).length + (enc g).length ≤ m + 1 := by
            rw [hlen] at hm
            exact hm
          have hf : (enc f).length ≤ m := by omega
          have hg : (enc g).length ≤ m := by omega
          change (let (f', rest') := decodeAux m (enc f ++ enc g ++ rest);
                  let (g', rest'') := decodeAux m rest'; (Formula.iff f' g', rest'')) = (Formula.iff f g, rest)
          have h1 : decodeAux m (enc f ++ enc g ++ rest) = (f, enc g ++ rest) := by
            simpa [List.append_assoc] using ihf m (validSuffix_enc g rest) hf
          rw [h1]
          simpa [ihg m hv hg]

/-- Decoding an encoding recovers the formula. -/
lemma decode_enc (f : Formula) : decode (enc f) = f := by
  have h := decodeAux_enc_len f (enc f).length (rest := []) validSuffix_nil le_rfl
  simpa [decode] using congrArg Prod.fst h

/-- **CIRCUIT-SAT**: the language of satisfiable circuits, encoded as gate
lists. -/
def CIRCUIT_SAT : Language Gate :=
  { gates | CircuitSatisfiable gates }

/-- **SAT**: the language of satisfiable boolean formulas, encoded as
prefix-polish symbol lists. -/
def SAT : Language FormulaSym :=
  { syms | ∃ f : Formula, enc f = syms ∧ Formula.Satisfiable f }

end Chapter34

end CLRS

namespace Turing

namespace TM2CS

open CLRS.Chapter34
open Computability StateTransition

inductive K : Type
  | inK | temp | buf | cnt | o | tmp | out
deriving DecidableEq, Fintype, Inhabited

abbrev Γk : K → Type
  | K.inK => Gate
  | K.temp => Gate
  | K.buf => Gate
  | K.cnt => Unit
  | K.o => FormulaSym
  | K.tmp => Unit
  | K.out => FormulaSym

inductive St : Type
  | init | done
  | gate (g : Gate)
  | mv (g : Option Gate)
  | rs (g : Option Gate)
  | emit (g : Gate)
  | sym (s : FormulaSym)
deriving DecidableEq, Fintype, Inhabited

inductive Label : Type
  | count | reorder | header | reset | loop | emitDispatch
  | emitInput | emitConst | emitNot | emitAnd | emitOr | dec | emitTrue | copyOut | done
  | moveHeader | restoreHeader
  | moveGF | restoreGF
  | moveInput | restoreInput
  | moveNot | restoreNot
  | moveAnd1 | restoreAnd1 | moveAnd2 | restoreAnd2
  | moveOr1 | restoreOr1 | moveOr2 | restoreOr2
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
          (Turing.TM2.Stmt.load (fun _ => St.mv none)
            (Turing.TM2.Stmt.goto (fun _ => Label.moveHeader))))
  | Label.moveHeader =>
      Turing.TM2.Stmt.pop K.cnt (fun v x => match x with
          | some () => (match v with | St.mv g => St.mv g | _ => St.mv none)
          | none => (match v with | St.mv g => St.rs g | _ => St.rs none))
        (Turing.TM2.Stmt.branch (fun v => match v with | St.mv _ => true | _ => false)
          (Turing.TM2.Stmt.push K.tmp (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.moveHeader)))
          (Turing.TM2.Stmt.goto (fun _ => Label.restoreHeader)))
  | Label.restoreHeader =>
      Turing.TM2.Stmt.pop K.tmp (fun v x => match x with
          | some () => (match v with | St.rs g => St.rs g | _ => St.rs none)
          | none => St.mv none)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.rs _ => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.restoreHeader))))
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
              (Turing.TM2.Stmt.goto (fun _ => Label.reset)))))
  | Label.reset =>
      Turing.TM2.Stmt.pop K.cnt (fun v x => match x with | some () => (St.mv none) | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.mv _ => true | _ => false)
          (Turing.TM2.Stmt.goto (fun _ => Label.reset))
          (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.loop))))
  | Label.loop =>
      Turing.TM2.Stmt.pop K.buf (fun _ x => match x with | some g => St.mv (some g) | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.mv (some _) => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.andMark)
            (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.iffMark)
              (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.varMark)
                (Turing.TM2.Stmt.goto (fun _ => Label.moveGF)))))
          (Turing.TM2.Stmt.goto (fun _ => Label.emitTrue)))
  | Label.moveGF =>
      Turing.TM2.Stmt.pop K.cnt (fun v x => match x with
          | some () => (match v with | St.mv g => St.mv g | _ => St.mv none)
          | none => (match v with | St.mv g => St.rs g | _ => St.rs none))
        (Turing.TM2.Stmt.branch (fun v => match v with | St.mv _ => true | _ => false)
          (Turing.TM2.Stmt.push K.tmp (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.moveGF)))
          (Turing.TM2.Stmt.goto (fun _ => Label.restoreGF)))
  | Label.restoreGF =>
      Turing.TM2.Stmt.pop K.tmp (fun v x => match x with
          | some () => (match v with | St.rs g => St.rs g | _ => St.rs none)
          | none => (match v with | St.rs (some g) => St.emit g | _ => St.done))
        (Turing.TM2.Stmt.branch (fun v => match v with | St.rs _ => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.restoreGF))))
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
              (Turing.TM2.Stmt.goto (fun _ => Label.emitDispatch)))))
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
        (Turing.TM2.Stmt.load (fun _ => St.mv (some Gate.input))
          (Turing.TM2.Stmt.goto (fun _ => Label.moveInput)))
  | Label.moveInput =>
      Turing.TM2.Stmt.pop K.cnt (fun v x => match x with
          | some () => (match v with | St.mv g => St.mv g | _ => St.mv none)
          | none => (match v with | St.mv g => St.rs g | _ => St.rs none))
        (Turing.TM2.Stmt.branch (fun v => match v with | St.mv _ => true | _ => false)
          (Turing.TM2.Stmt.push K.tmp (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.moveInput)))
          (Turing.TM2.Stmt.goto (fun _ => Label.restoreInput)))
  | Label.restoreInput =>
      Turing.TM2.Stmt.pop K.tmp (fun v x => match x with
          | some () => (match v with | St.rs g => St.rs g | _ => St.rs none)
          | none => (match v with | St.rs (some g) => St.emit g | _ => St.done))
        (Turing.TM2.Stmt.branch (fun v => match v with | St.rs _ => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.restoreInput))))
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
              (Turing.TM2.Stmt.goto (fun _ => Label.dec)))))
  | Label.emitConst =>
      Turing.TM2.Stmt.push K.o (fun v => match v with | St.emit (Gate.const b) => FormulaSym.lit b | _ => default)
        (Turing.TM2.Stmt.goto (fun _ => Label.dec))
  | Label.emitNot =>
      Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.notMark)
        (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.varMark)
          (Turing.TM2.Stmt.load (fun _ => St.mv (some Gate.not))
            (Turing.TM2.Stmt.goto (fun _ => Label.moveNot))))
  | Label.moveNot =>
      Turing.TM2.Stmt.pop K.cnt (fun v x => match x with
          | some () => (match v with | St.mv g => St.mv g | _ => St.mv none)
          | none => (match v with | St.mv g => St.rs g | _ => St.rs none))
        (Turing.TM2.Stmt.branch (fun v => match v with | St.mv _ => true | _ => false)
          (Turing.TM2.Stmt.push K.tmp (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.moveNot)))
          (Turing.TM2.Stmt.goto (fun _ => Label.restoreNot)))
  | Label.restoreNot =>
      Turing.TM2.Stmt.pop K.tmp (fun v x => match x with
          | some () => (match v with | St.rs g => St.rs g | _ => St.rs none)
          | none => (match v with | St.rs (some g) => St.emit g | _ => St.done))
        (Turing.TM2.Stmt.branch (fun v => match v with | St.rs _ => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.restoreNot))))
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.goto (fun _ => Label.dec))))
  | Label.emitAnd =>
      Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.andMark)
        (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.varMark)
          (Turing.TM2.Stmt.load (fun _ => St.mv (some Gate.and))
            (Turing.TM2.Stmt.goto (fun _ => Label.moveAnd1))))
  | Label.moveAnd1 =>
      Turing.TM2.Stmt.pop K.cnt (fun v x => match x with
          | some () => (match v with | St.mv g => St.mv g | _ => St.mv none)
          | none => (match v with | St.mv g => St.rs g | _ => St.rs none))
        (Turing.TM2.Stmt.branch (fun v => match v with | St.mv _ => true | _ => false)
          (Turing.TM2.Stmt.push K.tmp (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.moveAnd1)))
          (Turing.TM2.Stmt.goto (fun _ => Label.restoreAnd1)))
  | Label.restoreAnd1 =>
      Turing.TM2.Stmt.pop K.tmp (fun v x => match x with
          | some () => (match v with | St.rs g => St.rs g | _ => St.rs none)
          | none => (match v with | St.rs (some g) => St.mv (some g) | _ => St.done))
        (Turing.TM2.Stmt.branch (fun v => match v with | St.rs _ => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.restoreAnd1))))
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.varMark)
              (Turing.TM2.Stmt.goto (fun _ => Label.moveAnd2)))))
  | Label.moveAnd2 =>
      Turing.TM2.Stmt.pop K.cnt (fun v x => match x with
          | some () => (match v with | St.mv g => St.mv g | _ => St.mv none)
          | none => (match v with | St.mv g => St.rs g | _ => St.rs none))
        (Turing.TM2.Stmt.branch (fun v => match v with | St.mv _ => true | _ => false)
          (Turing.TM2.Stmt.push K.tmp (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.moveAnd2)))
          (Turing.TM2.Stmt.goto (fun _ => Label.restoreAnd2)))
  | Label.restoreAnd2 =>
      Turing.TM2.Stmt.pop K.tmp (fun v x => match x with
          | some () => (match v with | St.rs g => St.rs g | _ => St.rs none)
          | none => (match v with | St.rs (some g) => St.emit g | _ => St.done))
        (Turing.TM2.Stmt.branch (fun v => match v with | St.rs _ => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.restoreAnd2))))
          (Turing.TM2.Stmt.goto (fun _ => Label.dec)))
  | Label.emitOr =>
      Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.orMark)
        (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.varMark)
          (Turing.TM2.Stmt.load (fun _ => St.mv (some Gate.or))
            (Turing.TM2.Stmt.goto (fun _ => Label.moveOr1))))
  | Label.moveOr1 =>
      Turing.TM2.Stmt.pop K.cnt (fun v x => match x with
          | some () => (match v with | St.mv g => St.mv g | _ => St.mv none)
          | none => (match v with | St.mv g => St.rs g | _ => St.rs none))
        (Turing.TM2.Stmt.branch (fun v => match v with | St.mv _ => true | _ => false)
          (Turing.TM2.Stmt.push K.tmp (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.moveOr1)))
          (Turing.TM2.Stmt.goto (fun _ => Label.restoreOr1)))
  | Label.restoreOr1 =>
      Turing.TM2.Stmt.pop K.tmp (fun v x => match x with
          | some () => (match v with | St.rs g => St.rs g | _ => St.rs none)
          | none => (match v with | St.rs (some g) => St.mv (some g) | _ => St.done))
        (Turing.TM2.Stmt.branch (fun v => match v with | St.rs _ => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.restoreOr1))))
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.varMark)
              (Turing.TM2.Stmt.goto (fun _ => Label.moveOr2)))))
  | Label.moveOr2 =>
      Turing.TM2.Stmt.pop K.cnt (fun v x => match x with
          | some () => (match v with | St.mv g => St.mv g | _ => St.mv none)
          | none => (match v with | St.mv g => St.rs g | _ => St.rs none))
        (Turing.TM2.Stmt.branch (fun v => match v with | St.mv _ => true | _ => false)
          (Turing.TM2.Stmt.push K.tmp (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.moveOr2)))
          (Turing.TM2.Stmt.goto (fun _ => Label.restoreOr2)))
  | Label.restoreOr2 =>
      Turing.TM2.Stmt.pop K.tmp (fun v x => match x with
          | some () => (match v with | St.rs g => St.rs g | _ => St.rs none)
          | none => (match v with | St.rs (some g) => St.emit g | _ => St.done))
        (Turing.TM2.Stmt.branch (fun v => match v with | St.rs _ => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.endMark)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.restoreOr2))))
          (Turing.TM2.Stmt.goto (fun _ => Label.dec)))
  | Label.dec =>
      Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.loop))
  | Label.emitTrue =>
      Turing.TM2.Stmt.pop K.cnt (fun v x => match x with | some () => St.mv none | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.mv _ => true | _ => false)
          (Turing.TM2.Stmt.goto (fun _ => Label.emitTrue))
          (Turing.TM2.Stmt.push K.o (fun _ => FormulaSym.lit true)
            (Turing.TM2.Stmt.goto (fun _ => Label.copyOut))))
  | Label.copyOut =>
      Turing.TM2.Stmt.pop K.o (fun _ x => match x with | some s => St.sym s | none => St.init)
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
  | K.buf => B | K.o => O | K.tmp => [] | K.out => U

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
  | K.buf => B | K.o => O | K.tmp => [] | K.out => U

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


abbrev stkM (cnt Tmp : Nat) (O U : List FormulaSym) :
    ∀ k : K, List (Γk k) :=
  fun k => match k with
  | K.inK => [] | K.temp => [] | K.cnt => List.replicate cnt ()
  | K.buf => [] | K.o => O | K.tmp => List.replicate Tmp () | K.out => U

-- stk for the header/reset/gate configs: buf holds gates, counter c, output-build O
abbrev stkH (gates B : List Gate) (c : Nat) (O U : List FormulaSym) :
    ∀ k : K, List (Γk k) :=
  fun k => match k with
  | K.inK => [] | K.temp => [] | K.cnt => List.replicate c ()
  | K.buf => gates | K.o => O | K.tmp => [] | K.out => U

lemma replicate_cons_append {α : Type} (n : Nat) (a : α) (l : List α) :
    List.replicate n a ++ (a :: l) = List.replicate (n + 1) a ++ l := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, List.append_assoc]

lemma replicate_append_one {α : Type} (n : Nat) (a : α) :
    List.replicate n a ++ [a] = List.replicate (n + 1) a := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

-- move: counter (cnt+1 units) → tmp, one step
lemma moveHeader_step' (cnt Tmp : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.moveHeader, St.mv none, stkM (cnt + 1) Tmp O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveHeader, St.mv none, stkM cnt (Tmp + 1) O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkM, Function.update, prog, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
-- move: counter empty → restore
lemma moveHeader_done (Tmp : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.moveHeader, St.mv none, stkM 0 Tmp O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreHeader, St.rs none, stkM 0 Tmp O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkM, Function.update, prog]

-- move phase: transfer all `cnt` units from counter to tmp
lemma moveHeader_phase' (cnt Tmp : Nat) (O U : List FormulaSym) :
    (flip bind Sstep)^[cnt + 1]
        (some (⟨some Label.moveHeader, St.mv none, stkM cnt Tmp O U⟩ : (mach).Cfg))
      = some (⟨some Label.restoreHeader, St.rs none, stkM 0 (Tmp + cnt) O U⟩ : (mach).Cfg) := by
  induction cnt generalizing Tmp O U with
  | zero =>
      have h := moveHeader_done Tmp O U
      change (flip bind Sstep) (some (⟨some Label.moveHeader, St.mv none, stkM 0 Tmp O U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreHeader, St.rs none, stkM 0 (Tmp + 0) O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ cnt ih =>
      have hone := moveHeader_step' cnt Tmp O U
      rw [show Nat.succ cnt + 1 = cnt + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[cnt + 1]
          (Sstep (⟨some Label.moveHeader, St.mv none, stkM (cnt + 1) Tmp O U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreHeader, St.rs none, stkM 0 (Tmp + (cnt + 1)) O U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (Tmp + 1) O U
      calc
        (flip bind Sstep)^[cnt + 1]
            (some (⟨some Label.moveHeader, St.mv none, stkM cnt (Tmp + 1) O U⟩ : (mach).Cfg))
          = some (⟨some Label.restoreHeader, St.rs none, stkM 0 ((Tmp + 1) + cnt) O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.restoreHeader, St.rs none, stkM 0 (Tmp + (cnt + 1)) O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkM, Nat.add_comm, Nat.add_assoc] <;> try omega

-- restore: pop tmp, push endMark to o and () to cnt, one step
lemma restoreHeader_step (cnt Tmp : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.restoreHeader, St.rs none, stkM cnt (Tmp + 1) O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreHeader, St.rs none, stkM (cnt + 1) Tmp (FormulaSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkM, Function.update, prog, List.replicate_succ, Nat.add_comm, Nat.add_assoc]

-- restore: tmp empty → done, push 2 endMarks, goto reset
lemma restoreHeader_done (cnt : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.restoreHeader, St.rs none, stkM cnt 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.reset, St.mv none, stkM cnt 0 (FormulaSym.endMark :: FormulaSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkM, Function.update, prog]

-- restore phase: transfer all `Tmp` units from tmp to o (as endMarks) and cnt
lemma restoreHeader_phase' (Tmp cnt : Nat) (O U : List FormulaSym) :
    (flip bind Sstep)^[Tmp + 1]
        (some (⟨some Label.restoreHeader, St.rs none, stkM cnt Tmp O U⟩ : (mach).Cfg))
      = some (⟨some Label.reset, St.mv none, stkM (cnt + Tmp) 0 (List.replicate 2 FormulaSym.endMark ++ List.replicate Tmp FormulaSym.endMark ++ O) U⟩ : (mach).Cfg) := by
  induction Tmp generalizing cnt O U with
  | zero =>
      have h := restoreHeader_done cnt O U
      change (flip bind Sstep) (some (⟨some Label.restoreHeader, St.rs none, stkM cnt 0 O U⟩ : (mach).Cfg))
        = some (⟨some Label.reset, St.mv none, stkM (cnt + 0) 0 (List.replicate 2 FormulaSym.endMark ++ List.replicate 0 FormulaSym.endMark ++ O) U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ Tmp ih =>
      have hone := restoreHeader_step cnt Tmp O U
      rw [show Nat.succ Tmp + 1 = Tmp + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[Tmp + 1]
          (Sstep (⟨some Label.restoreHeader, St.rs none, stkM cnt (Tmp + 1) O U⟩ : (mach).Cfg))
        = some (⟨some Label.reset, St.mv none, stkM (cnt + (Tmp + 1)) 0 (List.replicate 2 FormulaSym.endMark ++ List.replicate (Tmp + 1) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (cnt + 1) (FormulaSym.endMark :: O) U
      calc
        (flip bind Sstep)^[Tmp + 1]
            (some (⟨some Label.restoreHeader, St.rs none, stkM (cnt + 1) Tmp (FormulaSym.endMark :: O) U⟩ : (mach).Cfg))
          = some (⟨some Label.reset, St.mv none, stkM ((cnt + 1) + Tmp) 0 (List.replicate 2 FormulaSym.endMark ++ List.replicate Tmp FormulaSym.endMark ++ (FormulaSym.endMark :: O)) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.reset, St.mv none, stkM (cnt + (Tmp + 1)) 0 (List.replicate 2 FormulaSym.endMark ++ List.replicate (Tmp + 1) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkM, List.replicate_succ, List.cons_append, List.append_assoc, replicate_append_one, replicate_cons_append, Nat.add_comm, Nat.add_assoc] <;> try omega

-- reset: pop a counter unit, one step
lemma reset_step (v : St) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.reset, v, stkH [] [] (c + 1) O U⟩ : (mach).Cfg)
      = some (⟨some Label.reset, St.mv none, stkH [] [] c O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkH, Function.update, prog, List.replicate_succ, Nat.add_comm, Nat.add_assoc]

-- reset: counter empty → push 1, goto loop
lemma reset_done (v : St) (O U : List FormulaSym) :
    Sstep (⟨some Label.reset, v, stkH [] [] 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.loop, St.done, stkH [] [] 1 O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkH, Function.update, prog]

-- reset phase: clear the counter, push 1, goto loop
lemma reset_phase (v : St) (c : Nat) (O U : List FormulaSym) :
    (flip bind Sstep)^[c + 1]
        (some (⟨some Label.reset, v, stkH [] [] c O U⟩ : (mach).Cfg))
      = some (⟨some Label.loop, St.done, stkH [] [] 1 O U⟩ : (mach).Cfg) := by
  induction c generalizing v O U with
  | zero =>
      have h := reset_done v O U
      change (flip bind Sstep) (some (⟨some Label.reset, v, stkH [] [] 0 O U⟩ : (mach).Cfg))
        = some (⟨some Label.loop, St.done, stkH [] [] 1 O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ c ih =>
      have hone := reset_step v c O U
      rw [show Nat.succ c + 1 = c + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[c + 1]
          (Sstep (⟨some Label.reset, v, stkH [] [] (c + 1) O U⟩ : (mach).Cfg))
        = some (⟨some Label.loop, St.done, stkH [] [] 1 O U⟩ : (mach).Cfg)
      rw [hone]
      exact ih (St.mv none) O U

-- ============================================================
-- Gate loop: move/restore copies with a carried gate
-- ============================================================

-- stk for the gate loop: `buf` holds the remaining gates, the counter is
-- `cnt`, the scratch stack holds `Tmp` units, and `O` is the output under
-- construction.  (This extends `stkH` with the scratch count `Tmp`.)
abbrev stkL (gates : List Gate) (cnt Tmp : Nat) (O U : List FormulaSym) :
    ∀ k : K, List (Γk k) :=
  fun k => match k with
  | K.inK => [] | K.temp => [] | K.cnt => List.replicate cnt ()
  | K.buf => gates | K.o => O | K.tmp => List.replicate Tmp () | K.out => U

-- move: counter (cnt+1 units) → tmp, one step (state carries the gate)
lemma moveGF_step (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.moveGF, St.mv (some g), stkL gates (cnt + 1) Tmp O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveGF, St.mv (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
-- move: counter empty → restore, state becomes rs
lemma moveGF_done (gates : List Gate) (Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.moveGF, St.mv (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreGF, St.rs (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog]

-- move phase: transfer all `cnt` counter units to the scratch stack
lemma moveGF_phase (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[cnt + 1]
      (some (⟨some Label.moveGF, St.mv (some g), stkL gates cnt Tmp O U⟩ : (mach).Cfg))
    = some (⟨some Label.restoreGF, St.rs (some g), stkL gates 0 (Tmp + cnt) O U⟩ : (mach).Cfg) := by
  induction cnt generalizing Tmp O U with
  | zero =>
      have h := moveGF_done gates Tmp g O U
      change (flip bind Sstep) (some (⟨some Label.moveGF, St.mv (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreGF, St.rs (some g), stkL gates 0 (Tmp + 0) O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ cnt ih =>
      have hone := moveGF_step gates cnt Tmp g O U
      rw [show Nat.succ cnt + 1 = cnt + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[cnt + 1]
          (Sstep (⟨some Label.moveGF, St.mv (some g), stkL gates (cnt + 1) Tmp O U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreGF, St.rs (some g), stkL gates 0 (Tmp + (cnt + 1)) O U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (Tmp + 1) O U
      calc
        (flip bind Sstep)^[cnt + 1]
            (some (⟨some Label.moveGF, St.mv (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg))
          = some (⟨some Label.restoreGF, St.rs (some g), stkL gates 0 ((Tmp + 1) + cnt) O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.restoreGF, St.rs (some g), stkL gates 0 (Tmp + (cnt + 1)) O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkL, Nat.add_comm, Nat.add_assoc] <;> try omega

-- move: input expression (wire i+2), one step
lemma moveInput_step (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.moveInput, St.mv (some g), stkL gates (cnt + 1) Tmp O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveInput, St.mv (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
lemma moveInput_done (gates : List Gate) (Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.moveInput, St.mv (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreInput, St.rs (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog]
lemma moveInput_phase (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[cnt + 1]
      (some (⟨some Label.moveInput, St.mv (some g), stkL gates cnt Tmp O U⟩ : (mach).Cfg))
    = some (⟨some Label.restoreInput, St.rs (some g), stkL gates 0 (Tmp + cnt) O U⟩ : (mach).Cfg) := by
  induction cnt generalizing Tmp O U with
  | zero =>
      have h := moveInput_done gates Tmp g O U
      change (flip bind Sstep) (some (⟨some Label.moveInput, St.mv (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreInput, St.rs (some g), stkL gates 0 (Tmp + 0) O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ cnt ih =>
      have hone := moveInput_step gates cnt Tmp g O U
      rw [show Nat.succ cnt + 1 = cnt + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[cnt + 1]
          (Sstep (⟨some Label.moveInput, St.mv (some g), stkL gates (cnt + 1) Tmp O U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreInput, St.rs (some g), stkL gates 0 (Tmp + (cnt + 1)) O U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (Tmp + 1) O U
      calc
        (flip bind Sstep)^[cnt + 1]
            (some (⟨some Label.moveInput, St.mv (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg))
          = some (⟨some Label.restoreInput, St.rs (some g), stkL gates 0 ((Tmp + 1) + cnt) O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.restoreInput, St.rs (some g), stkL gates 0 (Tmp + (cnt + 1)) O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkL, Nat.add_comm, Nat.add_assoc] <;> try omega

-- move: not expression (wire i+1)
lemma moveNot_step (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.moveNot, St.mv (some g), stkL gates (cnt + 1) Tmp O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveNot, St.mv (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
lemma moveNot_done (gates : List Gate) (Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.moveNot, St.mv (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreNot, St.rs (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog]
lemma moveNot_phase (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[cnt + 1]
      (some (⟨some Label.moveNot, St.mv (some g), stkL gates cnt Tmp O U⟩ : (mach).Cfg))
    = some (⟨some Label.restoreNot, St.rs (some g), stkL gates 0 (Tmp + cnt) O U⟩ : (mach).Cfg) := by
  induction cnt generalizing Tmp O U with
  | zero =>
      have h := moveNot_done gates Tmp g O U
      change (flip bind Sstep) (some (⟨some Label.moveNot, St.mv (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreNot, St.rs (some g), stkL gates 0 (Tmp + 0) O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ cnt ih =>
      have hone := moveNot_step gates cnt Tmp g O U
      rw [show Nat.succ cnt + 1 = cnt + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[cnt + 1]
          (Sstep (⟨some Label.moveNot, St.mv (some g), stkL gates (cnt + 1) Tmp O U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreNot, St.rs (some g), stkL gates 0 (Tmp + (cnt + 1)) O U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (Tmp + 1) O U
      calc
        (flip bind Sstep)^[cnt + 1]
            (some (⟨some Label.moveNot, St.mv (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg))
          = some (⟨some Label.restoreNot, St.rs (some g), stkL gates 0 ((Tmp + 1) + cnt) O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.restoreNot, St.rs (some g), stkL gates 0 (Tmp + (cnt + 1)) O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkL, Nat.add_comm, Nat.add_assoc] <;> try omega

-- move: and first operand (wire i+1)
lemma moveAnd1_step (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.moveAnd1, St.mv (some g), stkL gates (cnt + 1) Tmp O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveAnd1, St.mv (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
lemma moveAnd1_done (gates : List Gate) (Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.moveAnd1, St.mv (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreAnd1, St.rs (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog]
lemma moveAnd1_phase (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[cnt + 1]
      (some (⟨some Label.moveAnd1, St.mv (some g), stkL gates cnt Tmp O U⟩ : (mach).Cfg))
    = some (⟨some Label.restoreAnd1, St.rs (some g), stkL gates 0 (Tmp + cnt) O U⟩ : (mach).Cfg) := by
  induction cnt generalizing Tmp O U with
  | zero =>
      have h := moveAnd1_done gates Tmp g O U
      change (flip bind Sstep) (some (⟨some Label.moveAnd1, St.mv (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreAnd1, St.rs (some g), stkL gates 0 (Tmp + 0) O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ cnt ih =>
      have hone := moveAnd1_step gates cnt Tmp g O U
      rw [show Nat.succ cnt + 1 = cnt + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[cnt + 1]
          (Sstep (⟨some Label.moveAnd1, St.mv (some g), stkL gates (cnt + 1) Tmp O U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreAnd1, St.rs (some g), stkL gates 0 (Tmp + (cnt + 1)) O U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (Tmp + 1) O U
      calc
        (flip bind Sstep)^[cnt + 1]
            (some (⟨some Label.moveAnd1, St.mv (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg))
          = some (⟨some Label.restoreAnd1, St.rs (some g), stkL gates 0 ((Tmp + 1) + cnt) O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.restoreAnd1, St.rs (some g), stkL gates 0 (Tmp + (cnt + 1)) O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkL, Nat.add_comm, Nat.add_assoc] <;> try omega

-- move: and second operand (wire i)
lemma moveAnd2_step (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.moveAnd2, St.mv (some g), stkL gates (cnt + 1) Tmp O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveAnd2, St.mv (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
lemma moveAnd2_done (gates : List Gate) (Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.moveAnd2, St.mv (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreAnd2, St.rs (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog]
lemma moveAnd2_phase (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[cnt + 1]
      (some (⟨some Label.moveAnd2, St.mv (some g), stkL gates cnt Tmp O U⟩ : (mach).Cfg))
    = some (⟨some Label.restoreAnd2, St.rs (some g), stkL gates 0 (Tmp + cnt) O U⟩ : (mach).Cfg) := by
  induction cnt generalizing Tmp O U with
  | zero =>
      have h := moveAnd2_done gates Tmp g O U
      change (flip bind Sstep) (some (⟨some Label.moveAnd2, St.mv (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreAnd2, St.rs (some g), stkL gates 0 (Tmp + 0) O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ cnt ih =>
      have hone := moveAnd2_step gates cnt Tmp g O U
      rw [show Nat.succ cnt + 1 = cnt + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[cnt + 1]
          (Sstep (⟨some Label.moveAnd2, St.mv (some g), stkL gates (cnt + 1) Tmp O U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreAnd2, St.rs (some g), stkL gates 0 (Tmp + (cnt + 1)) O U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (Tmp + 1) O U
      calc
        (flip bind Sstep)^[cnt + 1]
            (some (⟨some Label.moveAnd2, St.mv (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg))
          = some (⟨some Label.restoreAnd2, St.rs (some g), stkL gates 0 ((Tmp + 1) + cnt) O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.restoreAnd2, St.rs (some g), stkL gates 0 (Tmp + (cnt + 1)) O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkL, Nat.add_comm, Nat.add_assoc] <;> try omega

-- move: or first operand (wire i+1)
lemma moveOr1_step (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.moveOr1, St.mv (some g), stkL gates (cnt + 1) Tmp O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveOr1, St.mv (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
lemma moveOr1_done (gates : List Gate) (Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.moveOr1, St.mv (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreOr1, St.rs (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog]
lemma moveOr1_phase (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[cnt + 1]
      (some (⟨some Label.moveOr1, St.mv (some g), stkL gates cnt Tmp O U⟩ : (mach).Cfg))
    = some (⟨some Label.restoreOr1, St.rs (some g), stkL gates 0 (Tmp + cnt) O U⟩ : (mach).Cfg) := by
  induction cnt generalizing Tmp O U with
  | zero =>
      have h := moveOr1_done gates Tmp g O U
      change (flip bind Sstep) (some (⟨some Label.moveOr1, St.mv (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreOr1, St.rs (some g), stkL gates 0 (Tmp + 0) O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ cnt ih =>
      have hone := moveOr1_step gates cnt Tmp g O U
      rw [show Nat.succ cnt + 1 = cnt + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[cnt + 1]
          (Sstep (⟨some Label.moveOr1, St.mv (some g), stkL gates (cnt + 1) Tmp O U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreOr1, St.rs (some g), stkL gates 0 (Tmp + (cnt + 1)) O U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (Tmp + 1) O U
      calc
        (flip bind Sstep)^[cnt + 1]
            (some (⟨some Label.moveOr1, St.mv (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg))
          = some (⟨some Label.restoreOr1, St.rs (some g), stkL gates 0 ((Tmp + 1) + cnt) O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.restoreOr1, St.rs (some g), stkL gates 0 (Tmp + (cnt + 1)) O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkL, Nat.add_comm, Nat.add_assoc] <;> try omega

-- move: or second operand (wire i)
lemma moveOr2_step (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.moveOr2, St.mv (some g), stkL gates (cnt + 1) Tmp O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveOr2, St.mv (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
lemma moveOr2_done (gates : List Gate) (Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.moveOr2, St.mv (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreOr2, St.rs (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog]
lemma moveOr2_phase (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[cnt + 1]
      (some (⟨some Label.moveOr2, St.mv (some g), stkL gates cnt Tmp O U⟩ : (mach).Cfg))
    = some (⟨some Label.restoreOr2, St.rs (some g), stkL gates 0 (Tmp + cnt) O U⟩ : (mach).Cfg) := by
  induction cnt generalizing Tmp O U with
  | zero =>
      have h := moveOr2_done gates Tmp g O U
      change (flip bind Sstep) (some (⟨some Label.moveOr2, St.mv (some g), stkL gates 0 Tmp O U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreOr2, St.rs (some g), stkL gates 0 (Tmp + 0) O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ cnt ih =>
      have hone := moveOr2_step gates cnt Tmp g O U
      rw [show Nat.succ cnt + 1 = cnt + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[cnt + 1]
          (Sstep (⟨some Label.moveOr2, St.mv (some g), stkL gates (cnt + 1) Tmp O U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreOr2, St.rs (some g), stkL gates 0 (Tmp + (cnt + 1)) O U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (Tmp + 1) O U
      calc
        (flip bind Sstep)^[cnt + 1]
            (some (⟨some Label.moveOr2, St.mv (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg))
          = some (⟨some Label.restoreOr2, St.rs (some g), stkL gates 0 ((Tmp + 1) + cnt) O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.restoreOr2, St.rs (some g), stkL gates 0 (Tmp + (cnt + 1)) O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkL, Nat.add_comm, Nat.add_assoc] <;> try omega

-- restore: pop a scratch unit, emit an endMark to o and restore the counter
lemma restoreGF_step (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.restoreGF, St.rs (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreGF, St.rs (some g), stkL gates (cnt + 1) Tmp (FormulaSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
-- restore: scratch empty → dispatch, emit 2 endMarks (wire i+2's tail)
lemma restoreGF_done (gates : List Gate) (cnt : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.restoreGF, St.rs (some g), stkL gates cnt 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitDispatch, St.emit g,
          stkL gates cnt 0 (FormulaSym.endMark :: FormulaSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog]
-- restore phase: transfer all `Tmp` scratch units back to o and cnt
lemma restoreGF_phase (gates : List Gate) (Tmp cnt : Nat) (g : Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[Tmp + 1]
      (some (⟨some Label.restoreGF, St.rs (some g), stkL gates cnt Tmp O U⟩ : (mach).Cfg))
    = some (⟨some Label.emitDispatch, St.emit g, stkL gates (cnt + Tmp) 0
        (List.replicate (Tmp + 2) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg) := by
  induction Tmp generalizing cnt O U with
  | zero =>
      have h := restoreGF_done gates cnt g O U
      change (flip bind Sstep) (some (⟨some Label.restoreGF, St.rs (some g), stkL gates cnt 0 O U⟩ : (mach).Cfg))
        = some (⟨some Label.emitDispatch, St.emit g, stkL gates (cnt + 0) 0
            (List.replicate (0 + 2) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ Tmp ih =>
      have hone := restoreGF_step gates cnt Tmp g O U
      rw [show Nat.succ Tmp + 1 = Tmp + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[Tmp + 1]
          (Sstep (⟨some Label.restoreGF, St.rs (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg))
        = some (⟨some Label.emitDispatch, St.emit g, stkL gates (cnt + (Tmp + 1)) 0
            (List.replicate ((Tmp + 1) + 2) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (cnt + 1) (FormulaSym.endMark :: O) U
      calc
        (flip bind Sstep)^[Tmp + 1]
            (some (⟨some Label.restoreGF, St.rs (some g), stkL gates (cnt + 1) Tmp (FormulaSym.endMark :: O) U⟩ : (mach).Cfg))
          = some (⟨some Label.emitDispatch, St.emit g, stkL gates ((cnt + 1) + Tmp) 0
              (List.replicate (Tmp + 2) FormulaSym.endMark ++ (FormulaSym.endMark :: O)) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.emitDispatch, St.emit g, stkL gates (cnt + (Tmp + 1)) 0
            (List.replicate ((Tmp + 1) + 2) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkL, replicate_cons_append, List.append_assoc] <;> try omega

-- restore: input expression (wire i+2)
lemma restoreInput_step (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.restoreInput, St.rs (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreInput, St.rs (some g), stkL gates (cnt + 1) Tmp (FormulaSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
lemma restoreInput_done (gates : List Gate) (cnt : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.restoreInput, St.rs (some g), stkL gates cnt 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.dec, St.emit g,
          stkL gates cnt 0 (FormulaSym.endMark :: FormulaSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog]
lemma restoreInput_phase (gates : List Gate) (Tmp cnt : Nat) (g : Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[Tmp + 1]
      (some (⟨some Label.restoreInput, St.rs (some g), stkL gates cnt Tmp O U⟩ : (mach).Cfg))
    = some (⟨some Label.dec, St.emit g, stkL gates (cnt + Tmp) 0
        (List.replicate (Tmp + 2) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg) := by
  induction Tmp generalizing cnt O U with
  | zero =>
      have h := restoreInput_done gates cnt g O U
      change (flip bind Sstep) (some (⟨some Label.restoreInput, St.rs (some g), stkL gates cnt 0 O U⟩ : (mach).Cfg))
        = some (⟨some Label.dec, St.emit g, stkL gates (cnt + 0) 0
            (List.replicate (0 + 2) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ Tmp ih =>
      have hone := restoreInput_step gates cnt Tmp g O U
      rw [show Nat.succ Tmp + 1 = Tmp + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[Tmp + 1]
          (Sstep (⟨some Label.restoreInput, St.rs (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg))
        = some (⟨some Label.dec, St.emit g, stkL gates (cnt + (Tmp + 1)) 0
            (List.replicate ((Tmp + 1) + 2) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (cnt + 1) (FormulaSym.endMark :: O) U
      calc
        (flip bind Sstep)^[Tmp + 1]
            (some (⟨some Label.restoreInput, St.rs (some g), stkL gates (cnt + 1) Tmp (FormulaSym.endMark :: O) U⟩ : (mach).Cfg))
          = some (⟨some Label.dec, St.emit g, stkL gates ((cnt + 1) + Tmp) 0
              (List.replicate (Tmp + 2) FormulaSym.endMark ++ (FormulaSym.endMark :: O)) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.dec, St.emit g, stkL gates (cnt + (Tmp + 1)) 0
            (List.replicate ((Tmp + 1) + 2) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkL, replicate_cons_append, List.append_assoc] <;> try omega

-- restore: not expression (wire i+1), only 1 extra endMark
lemma restoreNot_step (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.restoreNot, St.rs (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreNot, St.rs (some g), stkL gates (cnt + 1) Tmp (FormulaSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
lemma restoreNot_done (gates : List Gate) (cnt : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.restoreNot, St.rs (some g), stkL gates cnt 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.dec, St.emit g,
          stkL gates cnt 0 (FormulaSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog]
lemma restoreNot_phase (gates : List Gate) (Tmp cnt : Nat) (g : Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[Tmp + 1]
      (some (⟨some Label.restoreNot, St.rs (some g), stkL gates cnt Tmp O U⟩ : (mach).Cfg))
    = some (⟨some Label.dec, St.emit g, stkL gates (cnt + Tmp) 0
        (List.replicate (Tmp + 1) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg) := by
  induction Tmp generalizing cnt O U with
  | zero =>
      have h := restoreNot_done gates cnt g O U
      change (flip bind Sstep) (some (⟨some Label.restoreNot, St.rs (some g), stkL gates cnt 0 O U⟩ : (mach).Cfg))
        = some (⟨some Label.dec, St.emit g, stkL gates (cnt + 0) 0
            (List.replicate (0 + 1) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ Tmp ih =>
      have hone := restoreNot_step gates cnt Tmp g O U
      rw [show Nat.succ Tmp + 1 = Tmp + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[Tmp + 1]
          (Sstep (⟨some Label.restoreNot, St.rs (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg))
        = some (⟨some Label.dec, St.emit g, stkL gates (cnt + (Tmp + 1)) 0
            (List.replicate ((Tmp + 1) + 1) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (cnt + 1) (FormulaSym.endMark :: O) U
      calc
        (flip bind Sstep)^[Tmp + 1]
            (some (⟨some Label.restoreNot, St.rs (some g), stkL gates (cnt + 1) Tmp (FormulaSym.endMark :: O) U⟩ : (mach).Cfg))
          = some (⟨some Label.dec, St.emit g, stkL gates ((cnt + 1) + Tmp) 0
              (List.replicate (Tmp + 1) FormulaSym.endMark ++ (FormulaSym.endMark :: O)) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.dec, St.emit g, stkL gates (cnt + (Tmp + 1)) 0
            (List.replicate ((Tmp + 1) + 1) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkL, replicate_cons_append, List.append_assoc] <;> try omega

-- restore: and first operand (wire i+1): endMark, then a fresh varMark, onto moveAnd2
lemma restoreAnd1_step (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.restoreAnd1, St.rs (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreAnd1, St.rs (some g), stkL gates (cnt + 1) Tmp (FormulaSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
lemma restoreAnd1_done (gates : List Gate) (cnt : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.restoreAnd1, St.rs (some g), stkL gates cnt 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveAnd2, St.mv (some g),
          stkL gates cnt 0 (FormulaSym.varMark :: FormulaSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog]
lemma restoreAnd1_phase (gates : List Gate) (Tmp cnt : Nat) (g : Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[Tmp + 1]
      (some (⟨some Label.restoreAnd1, St.rs (some g), stkL gates cnt Tmp O U⟩ : (mach).Cfg))
    = some (⟨some Label.moveAnd2, St.mv (some g), stkL gates (cnt + Tmp) 0
        (FormulaSym.varMark :: (List.replicate (Tmp + 1) FormulaSym.endMark ++ O)) U⟩ : (mach).Cfg) := by
  induction Tmp generalizing cnt O U with
  | zero =>
      have h := restoreAnd1_done gates cnt g O U
      change (flip bind Sstep) (some (⟨some Label.restoreAnd1, St.rs (some g), stkL gates cnt 0 O U⟩ : (mach).Cfg))
        = some (⟨some Label.moveAnd2, St.mv (some g), stkL gates (cnt + 0) 0
            (FormulaSym.varMark :: (List.replicate (0 + 1) FormulaSym.endMark ++ O)) U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ Tmp ih =>
      have hone := restoreAnd1_step gates cnt Tmp g O U
      rw [show Nat.succ Tmp + 1 = Tmp + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[Tmp + 1]
          (Sstep (⟨some Label.restoreAnd1, St.rs (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg))
        = some (⟨some Label.moveAnd2, St.mv (some g), stkL gates (cnt + (Tmp + 1)) 0
            (FormulaSym.varMark :: (List.replicate ((Tmp + 1) + 1) FormulaSym.endMark ++ O)) U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (cnt + 1) (FormulaSym.endMark :: O) U
      calc
        (flip bind Sstep)^[Tmp + 1]
            (some (⟨some Label.restoreAnd1, St.rs (some g), stkL gates (cnt + 1) Tmp (FormulaSym.endMark :: O) U⟩ : (mach).Cfg))
          = some (⟨some Label.moveAnd2, St.mv (some g), stkL gates ((cnt + 1) + Tmp) 0
              (FormulaSym.varMark :: (List.replicate (Tmp + 1) FormulaSym.endMark ++ (FormulaSym.endMark :: O))) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.moveAnd2, St.mv (some g), stkL gates (cnt + (Tmp + 1)) 0
            (FormulaSym.varMark :: (List.replicate ((Tmp + 1) + 1) FormulaSym.endMark ++ O)) U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkL, replicate_cons_append, List.append_assoc] <;> try omega

-- restore: and second operand (wire i)
lemma restoreAnd2_step (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.restoreAnd2, St.rs (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreAnd2, St.rs (some g), stkL gates (cnt + 1) Tmp (FormulaSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
lemma restoreAnd2_done (gates : List Gate) (cnt : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.restoreAnd2, St.rs (some g), stkL gates cnt 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.dec, St.emit g, stkL gates cnt 0 O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog]
lemma restoreAnd2_phase (gates : List Gate) (Tmp cnt : Nat) (g : Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[Tmp + 1]
      (some (⟨some Label.restoreAnd2, St.rs (some g), stkL gates cnt Tmp O U⟩ : (mach).Cfg))
    = some (⟨some Label.dec, St.emit g, stkL gates (cnt + Tmp) 0
        (List.replicate Tmp FormulaSym.endMark ++ O) U⟩ : (mach).Cfg) := by
  induction Tmp generalizing cnt O U with
  | zero =>
      have h := restoreAnd2_done gates cnt g O U
      change (flip bind Sstep) (some (⟨some Label.restoreAnd2, St.rs (some g), stkL gates cnt 0 O U⟩ : (mach).Cfg))
        = some (⟨some Label.dec, St.emit g, stkL gates (cnt + 0) 0
            (List.replicate 0 FormulaSym.endMark ++ O) U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ Tmp ih =>
      have hone := restoreAnd2_step gates cnt Tmp g O U
      rw [show Nat.succ Tmp + 1 = Tmp + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[Tmp + 1]
          (Sstep (⟨some Label.restoreAnd2, St.rs (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg))
        = some (⟨some Label.dec, St.emit g, stkL gates (cnt + (Tmp + 1)) 0
            (List.replicate (Tmp + 1) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (cnt + 1) (FormulaSym.endMark :: O) U
      calc
        (flip bind Sstep)^[Tmp + 1]
            (some (⟨some Label.restoreAnd2, St.rs (some g), stkL gates (cnt + 1) Tmp (FormulaSym.endMark :: O) U⟩ : (mach).Cfg))
          = some (⟨some Label.dec, St.emit g, stkL gates ((cnt + 1) + Tmp) 0
              (List.replicate Tmp FormulaSym.endMark ++ (FormulaSym.endMark :: O)) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.dec, St.emit g, stkL gates (cnt + (Tmp + 1)) 0
            (List.replicate (Tmp + 1) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkL, replicate_cons_append, List.append_assoc] <;> try omega

-- restore: or first operand (wire i+1)
lemma restoreOr1_step (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.restoreOr1, St.rs (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreOr1, St.rs (some g), stkL gates (cnt + 1) Tmp (FormulaSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
lemma restoreOr1_done (gates : List Gate) (cnt : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.restoreOr1, St.rs (some g), stkL gates cnt 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveOr2, St.mv (some g),
          stkL gates cnt 0 (FormulaSym.varMark :: FormulaSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog]
lemma restoreOr1_phase (gates : List Gate) (Tmp cnt : Nat) (g : Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[Tmp + 1]
      (some (⟨some Label.restoreOr1, St.rs (some g), stkL gates cnt Tmp O U⟩ : (mach).Cfg))
    = some (⟨some Label.moveOr2, St.mv (some g), stkL gates (cnt + Tmp) 0
        (FormulaSym.varMark :: (List.replicate (Tmp + 1) FormulaSym.endMark ++ O)) U⟩ : (mach).Cfg) := by
  induction Tmp generalizing cnt O U with
  | zero =>
      have h := restoreOr1_done gates cnt g O U
      change (flip bind Sstep) (some (⟨some Label.restoreOr1, St.rs (some g), stkL gates cnt 0 O U⟩ : (mach).Cfg))
        = some (⟨some Label.moveOr2, St.mv (some g), stkL gates (cnt + 0) 0
            (FormulaSym.varMark :: (List.replicate (0 + 1) FormulaSym.endMark ++ O)) U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ Tmp ih =>
      have hone := restoreOr1_step gates cnt Tmp g O U
      rw [show Nat.succ Tmp + 1 = Tmp + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[Tmp + 1]
          (Sstep (⟨some Label.restoreOr1, St.rs (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg))
        = some (⟨some Label.moveOr2, St.mv (some g), stkL gates (cnt + (Tmp + 1)) 0
            (FormulaSym.varMark :: (List.replicate ((Tmp + 1) + 1) FormulaSym.endMark ++ O)) U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (cnt + 1) (FormulaSym.endMark :: O) U
      calc
        (flip bind Sstep)^[Tmp + 1]
            (some (⟨some Label.restoreOr1, St.rs (some g), stkL gates (cnt + 1) Tmp (FormulaSym.endMark :: O) U⟩ : (mach).Cfg))
          = some (⟨some Label.moveOr2, St.mv (some g), stkL gates ((cnt + 1) + Tmp) 0
              (FormulaSym.varMark :: (List.replicate (Tmp + 1) FormulaSym.endMark ++ (FormulaSym.endMark :: O))) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.moveOr2, St.mv (some g), stkL gates (cnt + (Tmp + 1)) 0
            (FormulaSym.varMark :: (List.replicate ((Tmp + 1) + 1) FormulaSym.endMark ++ O)) U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkL, replicate_cons_append, List.append_assoc] <;> try omega

-- restore: or second operand (wire i)
lemma restoreOr2_step (gates : List Gate) (cnt Tmp : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.restoreOr2, St.rs (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreOr2, St.rs (some g), stkL gates (cnt + 1) Tmp (FormulaSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
lemma restoreOr2_done (gates : List Gate) (cnt : Nat) (g : Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.restoreOr2, St.rs (some g), stkL gates cnt 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.dec, St.emit g, stkL gates cnt 0 O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog]
lemma restoreOr2_phase (gates : List Gate) (Tmp cnt : Nat) (g : Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[Tmp + 1]
      (some (⟨some Label.restoreOr2, St.rs (some g), stkL gates cnt Tmp O U⟩ : (mach).Cfg))
    = some (⟨some Label.dec, St.emit g, stkL gates (cnt + Tmp) 0
        (List.replicate Tmp FormulaSym.endMark ++ O) U⟩ : (mach).Cfg) := by
  induction Tmp generalizing cnt O U with
  | zero =>
      have h := restoreOr2_done gates cnt g O U
      change (flip bind Sstep) (some (⟨some Label.restoreOr2, St.rs (some g), stkL gates cnt 0 O U⟩ : (mach).Cfg))
        = some (⟨some Label.dec, St.emit g, stkL gates (cnt + 0) 0
            (List.replicate 0 FormulaSym.endMark ++ O) U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ Tmp ih =>
      have hone := restoreOr2_step gates cnt Tmp g O U
      rw [show Nat.succ Tmp + 1 = Tmp + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[Tmp + 1]
          (Sstep (⟨some Label.restoreOr2, St.rs (some g), stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg))
        = some (⟨some Label.dec, St.emit g, stkL gates (cnt + (Tmp + 1)) 0
            (List.replicate (Tmp + 1) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (cnt + 1) (FormulaSym.endMark :: O) U
      calc
        (flip bind Sstep)^[Tmp + 1]
            (some (⟨some Label.restoreOr2, St.rs (some g), stkL gates (cnt + 1) Tmp (FormulaSym.endMark :: O) U⟩ : (mach).Cfg))
          = some (⟨some Label.dec, St.emit g, stkL gates ((cnt + 1) + Tmp) 0
              (List.replicate Tmp FormulaSym.endMark ++ (FormulaSym.endMark :: O)) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.dec, St.emit g, stkL gates (cnt + (Tmp + 1)) 0
            (List.replicate (Tmp + 1) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkL, replicate_cons_append, List.append_assoc] <;> try omega

-- ============================================================
-- Gate loop: per-gate clause emission
-- ============================================================

-- exact number of steps to emit the clause of gate `g` at index `i`
def gateSteps (i : Nat) (g : Gate) : Nat :=
  match g with
  | Gate.input => 4 * i + 12
  | Gate.const _ => 2 * i + 8
  | Gate.not => 4 * i + 12
  | Gate.and => 6 * i + 16
  | Gate.or => 6 * i + 16

-- total steps of the loop phase for `gates` starting at index `i` (the final
-- empty-buffer pop to `emitTrue` contributes one step)
def loopSteps (i : Nat) : List Gate → Nat
  | [] => 1
  | g :: rest => gateSteps i g + loopSteps (i + 1) rest

-- compose two `flip bind` iterations (m steps, then n steps)
private lemma iter_compose {a b c : Option (mach).Cfg} (m n : Nat)
    (h1 : (flip bind Sstep)^[m] a = b) (h2 : (flip bind Sstep)^[n] b = c) :
    (flip bind Sstep)^[m + n] a = c := by
  rw [show m + n = n + m by omega]
  rw [Function.iterate_add_apply, h1]
  exact h2

-- (varEnc i).reverse is the endMarks (unary index) followed by the var mark
lemma reverse_varEnc (i : Nat) :
    (varEnc i).reverse = List.replicate (i + 1) FormulaSym.endMark ++ [FormulaSym.varMark] := by
  unfold varEnc
  rw [List.reverse_cons, List.reverse_replicate]

-- the reversed gate-consistency encoding splits into expression, output wire, iff
lemma reverse_gateFormulaEnc (i : Nat) (g : Gate) :
    (gateFormulaEnc i g).reverse =
      (gateExprEnc i g).reverse ++ (varEnc (i + 2)).reverse ++ [FormulaSym.iffMark] := by
  unfold gateFormulaEnc
  rw [List.reverse_cons, List.reverse_append, List.append_assoc]

lemma reverse_gateExprEnc_input (i : Nat) :
    (gateExprEnc i Gate.input).reverse = (varEnc (i + 2)).reverse := by
  simp [gateExprEnc]
lemma reverse_gateExprEnc_const (i : Nat) (b : Bool) :
    (gateExprEnc i (Gate.const b)).reverse = [FormulaSym.lit b] := by
  simp [gateExprEnc]
lemma reverse_gateExprEnc_not (i : Nat) :
    (gateExprEnc i Gate.not).reverse = (varEnc (i + 1)).reverse ++ [FormulaSym.notMark] := by
  simp [gateExprEnc, List.reverse_cons]
lemma reverse_gateExprEnc_and (i : Nat) :
    (gateExprEnc i Gate.and).reverse =
      (varEnc i).reverse ++ (varEnc (i + 1)).reverse ++ [FormulaSym.andMark] := by
  simp [gateExprEnc, List.reverse_cons, List.reverse_append, List.append_assoc]
lemma reverse_gateExprEnc_or (i : Nat) :
    (gateExprEnc i Gate.or).reverse =
      (varEnc i).reverse ++ (varEnc (i + 1)).reverse ++ [FormulaSym.orMark] := by
  simp [gateExprEnc, List.reverse_cons, List.reverse_append, List.append_assoc]

-- the stack effect of emitting varEnc k on top of O: the k+1 endMarks (the var
-- mark itself was pushed before the copy phase)
lemma varEnc_rev_cons (k : Nat) (O : List FormulaSym) :
    List.replicate (k + 1) FormulaSym.endMark ++ FormulaSym.varMark :: O = (varEnc k).reverse ++ O := by
  unfold varEnc
  rw [List.reverse_cons, List.reverse_replicate]
  simp [List.append_assoc]

-- one loop step: pop the gate, push the clause header (and/iff/var marks)
lemma loop_step (v : St) (g : Gate) (rest : List Gate) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.loop, v, stkL (g :: rest) c 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveGF, St.mv (some g), stkL rest c 0
          (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep]
-- one loop step on an empty buffer: goto emitTrue
lemma loop_empty (v : St) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.loop, v, stkL [] c 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitTrue, St.done, stkL [] c 0 O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep]

-- the emitDispatch label dispatches on the gate type
lemma emitDispatch_input (gates : List Gate) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.emitDispatch, St.emit Gate.input, stkL gates c 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitInput, St.emit Gate.input, stkL gates c 0 O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, prog]
lemma emitDispatch_const {b : Bool} (gates : List Gate) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.emitDispatch, St.emit (Gate.const b), stkL gates c 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitConst, St.emit (Gate.const b), stkL gates c 0 O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, prog]
lemma emitDispatch_not (gates : List Gate) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.emitDispatch, St.emit Gate.not, stkL gates c 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitNot, St.emit Gate.not, stkL gates c 0 O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, prog]
lemma emitDispatch_and (gates : List Gate) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.emitDispatch, St.emit Gate.and, stkL gates c 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitAnd, St.emit Gate.and, stkL gates c 0 O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, prog]
lemma emitDispatch_or (gates : List Gate) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.emitDispatch, St.emit Gate.or, stkL gates c 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitOr, St.emit Gate.or, stkL gates c 0 O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, prog]

-- the emit labels push the gate-expression symbols
lemma emitInput_step (gates : List Gate) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.emitInput, St.emit Gate.input, stkL gates c 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveInput, St.mv (some Gate.input), stkL gates c 0 (FormulaSym.varMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep]
lemma emitConst_step {b : Bool} (gates : List Gate) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.emitConst, St.emit (Gate.const b), stkL gates c 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.dec, St.emit (Gate.const b), stkL gates c 0 (FormulaSym.lit b :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep]
lemma emitNot_step (gates : List Gate) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.emitNot, St.emit Gate.not, stkL gates c 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveNot, St.mv (some Gate.not),
          stkL gates c 0 (FormulaSym.varMark :: FormulaSym.notMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep]
lemma emitAnd_step (gates : List Gate) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.emitAnd, St.emit Gate.and, stkL gates c 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveAnd1, St.mv (some Gate.and),
          stkL gates c 0 (FormulaSym.varMark :: FormulaSym.andMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep]
lemma emitOr_step (gates : List Gate) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.emitOr, St.emit Gate.or, stkL gates c 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveOr1, St.mv (some Gate.or),
          stkL gates c 0 (FormulaSym.varMark :: FormulaSym.orMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep]

-- the dec label increments the counter and returns to the loop
lemma dec_step (v : St) (gates : List Gate) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.dec, v, stkL gates c 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.loop, v, stkL gates (c + 1) 0 O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]

-- one gate `input` at index `i`: emit its clause (output wire i+2, then the
-- input expression, also wire i+2) and bump the counter
lemma loop_input (v : St) (i : Nat) (rest : List Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[4 * i + 12]
      (some (⟨some Label.loop, v, stkL (Gate.input :: rest) (i + 1) 0 O U⟩ : (mach).Cfg))
    = some (⟨some Label.loop, St.emit Gate.input, stkL rest (i + 2) 0
        (List.reverse (gateFormulaEnc i Gate.input) ++ FormulaSym.andMark :: O) U⟩ : (mach).Cfg) := by
  let c0 : (mach).Cfg := ⟨some Label.loop, v, stkL (Gate.input :: rest) (i + 1) 0 O U⟩
  let c1 : (mach).Cfg := ⟨some Label.moveGF, St.mv (some Gate.input), stkL rest (i + 1) 0
      (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩
  let c2 : (mach).Cfg := ⟨some Label.restoreGF, St.rs (some Gate.input), stkL rest 0 (i + 1)
      (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩
  let c3 : (mach).Cfg := ⟨some Label.emitDispatch, St.emit Gate.input, stkL rest (i + 1) 0
      (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)) U⟩
  let c4 : (mach).Cfg := ⟨some Label.emitInput, St.emit Gate.input, stkL rest (i + 1) 0
      (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)) U⟩
  let c5 : (mach).Cfg := ⟨some Label.moveInput, St.mv (some Gate.input), stkL rest (i + 1) 0
      (FormulaSym.varMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩
  let c6 : (mach).Cfg := ⟨some Label.restoreInput, St.rs (some Gate.input), stkL rest 0 (i + 1)
      (FormulaSym.varMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩
  let c7 : (mach).Cfg := ⟨some Label.dec, St.emit Gate.input, stkL rest (i + 1) 0
      (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark ::
        (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)))) U⟩
  let c8 : (mach).Cfg := ⟨some Label.loop, St.emit Gate.input, stkL rest (i + 2) 0
      (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark ::
        (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)))) U⟩
  have h1 : (flip bind Sstep)^[1] (some c0) = some c1 := by
    exact loop_step v Gate.input rest (i + 1) O U
  have h2 : (flip bind Sstep)^[(i + 1) + 1] (some c1) = some c2 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.moveGF, St.mv (some Gate.input), stkL rest (i + 1) 0 (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreGF, St.rs (some Gate.input), stkL rest 0 (i + 1) (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using moveGF_phase rest (i + 1) 0 Gate.input (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U
  have h3 : (flip bind Sstep)^[(i + 1) + 1] (some c2) = some c3 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.restoreGF, St.rs (some Gate.input), stkL rest 0 (i + 1) (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩ : (mach).Cfg))
        = some (⟨some Label.emitDispatch, St.emit Gate.input, stkL rest (i + 1) 0 (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using restoreGF_phase rest (i + 1) 0 Gate.input (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U
  have h4 : (flip bind Sstep)^[1] (some c3) = some c4 := by
    exact emitDispatch_input rest (i + 1) (c3.stk K.o) U
  have h5 : (flip bind Sstep)^[1] (some c4) = some c5 := by
    exact emitInput_step rest (i + 1) (c4.stk K.o) U
  have h6 : (flip bind Sstep)^[(i + 1) + 1] (some c5) = some c6 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.moveInput, St.mv (some Gate.input), stkL rest (i + 1) 0 (FormulaSym.varMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreInput, St.rs (some Gate.input), stkL rest 0 (i + 1) (FormulaSym.varMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using moveInput_phase rest (i + 1) 0 Gate.input (c5.stk K.o) U
  have h7 : (flip bind Sstep)^[(i + 1) + 1] (some c6) = some c7 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.restoreInput, St.rs (some Gate.input), stkL rest 0 (i + 1) (FormulaSym.varMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩ : (mach).Cfg))
        = some (⟨some Label.dec, St.emit Gate.input, stkL rest (i + 1) 0 (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)))) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using restoreInput_phase rest (i + 1) 0 Gate.input (c6.stk K.o) U
  have h8 : (flip bind Sstep)^[1] (some c7) = some c8 := by
    exact dec_step (v := St.emit Gate.input) rest (i + 1) (c7.stk K.o) U
  have hfinal : c8.stk K.o = List.reverse (gateFormulaEnc i Gate.input) ++ (FormulaSym.andMark :: O) := by
    rw [show c8.stk K.o = List.replicate (i + 3) FormulaSym.endMark ++ FormulaSym.varMark ::
        (List.replicate (i + 3) FormulaSym.endMark ++ FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) by rfl]
    rw [varEnc_rev_cons (i + 2) (List.replicate (i + 3) FormulaSym.endMark ++ FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)]
    rw [varEnc_rev_cons (i + 2) (FormulaSym.iffMark :: FormulaSym.andMark :: O)]
    rw [show (varEnc (i + 2)).reverse ++ ((varEnc (i + 2)).reverse ++ FormulaSym.iffMark :: FormulaSym.andMark :: O)
        = List.reverse (gateFormulaEnc i Gate.input) ++ (FormulaSym.andMark :: O) by
      rw [reverse_gateFormulaEnc i Gate.input]
      rw [reverse_gateExprEnc_input i]
      simp [List.append_assoc, List.cons_append]]
  have htop : c8 = ⟨some Label.loop, St.emit Gate.input, stkL rest (i + 2) 0
      (List.reverse (gateFormulaEnc i Gate.input) ++ FormulaSym.andMark :: O) U⟩ := by
    apply Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext k
      cases k <;> (try rw [hfinal]) <;> simp [c8]
  have htot : (flip bind Sstep)^[1 + (i + 2 + (i + 2 + (1 + (1 + (i + 2 + (i + 2 + 1))))))]
      (some c0) = some c8 :=
    iter_compose 1 (i + 2 + (i + 2 + (1 + (1 + (i + 2 + (i + 2 + 1)))))) h1
      (iter_compose (i + 2) (i + 2 + (1 + (1 + (i + 2 + (i + 2 + 1))))) h2
        (iter_compose (i + 2) (1 + (1 + (i + 2 + (i + 2 + 1)))) h3
          (iter_compose 1 (1 + (i + 2 + (i + 2 + 1))) h4
            (iter_compose 1 (i + 2 + (i + 2 + 1)) h5
              (iter_compose (i + 2) (i + 2 + 1) h6
                (iter_compose (i + 2) 1 h7 h8))))))
  rw [show 4 * i + 12 = 1 + (i + 2 + (i + 2 + (1 + (1 + (i + 2 + (i + 2 + 1)))))) by omega]
  rw [htot]
  rw [htop]
  rfl

-- one gate `const b` at index `i`: emit `lit b` and bump the counter
lemma loop_const {b : Bool} (v : St) (i : Nat) (rest : List Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[2 * i + 8]
      (some (⟨some Label.loop, v, stkL (Gate.const b :: rest) (i + 1) 0 O U⟩ : (mach).Cfg))
    = some (⟨some Label.loop, St.emit (Gate.const b), stkL rest (i + 2) 0
        (List.reverse (gateFormulaEnc i (Gate.const b)) ++ FormulaSym.andMark :: O) U⟩ : (mach).Cfg) := by
  let c0 : (mach).Cfg := ⟨some Label.loop, v, stkL (Gate.const b :: rest) (i + 1) 0 O U⟩
  let c1 : (mach).Cfg := ⟨some Label.moveGF, St.mv (some (Gate.const b)), stkL rest (i + 1) 0
      (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩
  let c2 : (mach).Cfg := ⟨some Label.restoreGF, St.rs (some (Gate.const b)), stkL rest 0 (i + 1)
      (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩
  let c3 : (mach).Cfg := ⟨some Label.emitDispatch, St.emit (Gate.const b), stkL rest (i + 1) 0
      (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)) U⟩
  let c4 : (mach).Cfg := ⟨some Label.emitConst, St.emit (Gate.const b), stkL rest (i + 1) 0
      (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)) U⟩
  let c5 : (mach).Cfg := ⟨some Label.dec, St.emit (Gate.const b), stkL rest (i + 1) 0
      (FormulaSym.lit b :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩
  let c6 : (mach).Cfg := ⟨some Label.loop, St.emit (Gate.const b), stkL rest (i + 2) 0
      (FormulaSym.lit b :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩
  have h1 : (flip bind Sstep)^[1] (some c0) = some c1 := by
    exact loop_step v (Gate.const b) rest (i + 1) O U
  have h2 : (flip bind Sstep)^[(i + 1) + 1] (some c1) = some c2 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.moveGF, St.mv (some (Gate.const b)), stkL rest (i + 1) 0 (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreGF, St.rs (some (Gate.const b)), stkL rest 0 (i + 1) (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using moveGF_phase rest (i + 1) 0 (Gate.const b) (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U
  have h3 : (flip bind Sstep)^[(i + 1) + 1] (some c2) = some c3 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.restoreGF, St.rs (some (Gate.const b)), stkL rest 0 (i + 1) (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩ : (mach).Cfg))
        = some (⟨some Label.emitDispatch, St.emit (Gate.const b), stkL rest (i + 1) 0 (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using restoreGF_phase rest (i + 1) 0 (Gate.const b) (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U
  have h4 : (flip bind Sstep)^[1] (some c3) = some c4 := by
    exact emitDispatch_const rest (i + 1) (c3.stk K.o) U
  have h5 : (flip bind Sstep)^[1] (some c4) = some c5 := by
    exact emitConst_step rest (i + 1) (c4.stk K.o) U
  have h6 : (flip bind Sstep)^[1] (some c5) = some c6 := by
    exact dec_step (v := St.emit (Gate.const b)) rest (i + 1) (c5.stk K.o) U
  have hfinal : c6.stk K.o = List.reverse (gateFormulaEnc i (Gate.const b)) ++ (FormulaSym.andMark :: O) := by
    rw [show c6.stk K.o = FormulaSym.lit b :: (List.replicate (i + 3) FormulaSym.endMark ++ FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) by rfl]
    rw [varEnc_rev_cons (i + 2) (FormulaSym.iffMark :: FormulaSym.andMark :: O)]
    rw [show FormulaSym.lit b :: ((varEnc (i + 2)).reverse ++ FormulaSym.iffMark :: FormulaSym.andMark :: O)
        = List.reverse (gateFormulaEnc i (Gate.const b)) ++ FormulaSym.andMark :: O by
      rw [reverse_gateFormulaEnc i (Gate.const b)]
      rw [reverse_gateExprEnc_const i b]
      simp [List.append_assoc, List.cons_append]]
  have htop : c6 = ⟨some Label.loop, St.emit (Gate.const b), stkL rest (i + 2) 0
      (List.reverse (gateFormulaEnc i (Gate.const b)) ++ FormulaSym.andMark :: O) U⟩ := by
    apply Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext k
      cases k <;> (try rw [hfinal]) <;> simp [c6]
  have htot : (flip bind Sstep)^[1 + (i + 2 + (i + 2 + (1 + (1 + 1))))]
      (some c0) = some c6 :=
    iter_compose 1 (i + 2 + (i + 2 + (1 + (1 + 1)))) h1
      (iter_compose (i + 2) (i + 2 + (1 + (1 + 1))) h2
        (iter_compose (i + 2) (1 + (1 + 1)) h3
          (iter_compose 1 (1 + 1) h4
            (iter_compose 1 1 h5 h6))))
  rw [show 2 * i + 8 = 1 + (i + 2 + (i + 2 + (1 + (1 + 1)))) by omega]
  rw [htot]
  rw [htop]
  rfl

-- one gate `not` at index `i`: emit `not (wire i+1)` and bump the counter
lemma loop_not (v : St) (i : Nat) (rest : List Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[4 * i + 12]
      (some (⟨some Label.loop, v, stkL (Gate.not :: rest) (i + 1) 0 O U⟩ : (mach).Cfg))
    = some (⟨some Label.loop, St.emit Gate.not, stkL rest (i + 2) 0
        (List.reverse (gateFormulaEnc i Gate.not) ++ FormulaSym.andMark :: O) U⟩ : (mach).Cfg) := by
  let c0 : (mach).Cfg := ⟨some Label.loop, v, stkL (Gate.not :: rest) (i + 1) 0 O U⟩
  let c1 : (mach).Cfg := ⟨some Label.moveGF, St.mv (some Gate.not), stkL rest (i + 1) 0
      (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩
  let c2 : (mach).Cfg := ⟨some Label.restoreGF, St.rs (some Gate.not), stkL rest 0 (i + 1)
      (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩
  let c3 : (mach).Cfg := ⟨some Label.emitDispatch, St.emit Gate.not, stkL rest (i + 1) 0
      (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)) U⟩
  let c4 : (mach).Cfg := ⟨some Label.emitNot, St.emit Gate.not, stkL rest (i + 1) 0
      (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)) U⟩
  let c5 : (mach).Cfg := ⟨some Label.moveNot, St.mv (some Gate.not), stkL rest (i + 1) 0
      (FormulaSym.varMark :: FormulaSym.notMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩
  let c6 : (mach).Cfg := ⟨some Label.restoreNot, St.rs (some Gate.not), stkL rest 0 (i + 1)
      (FormulaSym.varMark :: FormulaSym.notMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩
  let c7 : (mach).Cfg := ⟨some Label.dec, St.emit Gate.not, stkL rest (i + 1) 0
      (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.notMark ::
        (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)))) U⟩
  let c8 : (mach).Cfg := ⟨some Label.loop, St.emit Gate.not, stkL rest (i + 2) 0
      (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.notMark ::
        (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)))) U⟩
  have h1 : (flip bind Sstep)^[1] (some c0) = some c1 := by
    exact loop_step v Gate.not rest (i + 1) O U
  have h2 : (flip bind Sstep)^[(i + 1) + 1] (some c1) = some c2 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.moveGF, St.mv (some Gate.not), stkL rest (i + 1) 0 (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreGF, St.rs (some Gate.not), stkL rest 0 (i + 1) (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using moveGF_phase rest (i + 1) 0 Gate.not (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U
  have h3 : (flip bind Sstep)^[(i + 1) + 1] (some c2) = some c3 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.restoreGF, St.rs (some Gate.not), stkL rest 0 (i + 1) (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩ : (mach).Cfg))
        = some (⟨some Label.emitDispatch, St.emit Gate.not, stkL rest (i + 1) 0 (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using restoreGF_phase rest (i + 1) 0 Gate.not (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U
  have h4 : (flip bind Sstep)^[1] (some c3) = some c4 := by
    exact emitDispatch_not rest (i + 1) (c3.stk K.o) U
  have h5 : (flip bind Sstep)^[1] (some c4) = some c5 := by
    exact emitNot_step rest (i + 1) (c4.stk K.o) U
  have h6 : (flip bind Sstep)^[(i + 1) + 1] (some c5) = some c6 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.moveNot, St.mv (some Gate.not), stkL rest (i + 1) 0 (FormulaSym.varMark :: FormulaSym.notMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreNot, St.rs (some Gate.not), stkL rest 0 (i + 1) (FormulaSym.varMark :: FormulaSym.notMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using moveNot_phase rest (i + 1) 0 Gate.not (c5.stk K.o) U
  have h7 : (flip bind Sstep)^[(i + 1) + 1] (some c6) = some c7 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.restoreNot, St.rs (some Gate.not), stkL rest 0 (i + 1) (FormulaSym.varMark :: FormulaSym.notMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩ : (mach).Cfg))
        = some (⟨some Label.dec, St.emit Gate.not, stkL rest (i + 1) 0 (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.notMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)))) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using restoreNot_phase rest (i + 1) 0 Gate.not (c6.stk K.o) U
  have h8 : (flip bind Sstep)^[1] (some c7) = some c8 := by
    exact dec_step (v := St.emit Gate.not) rest (i + 1) (c7.stk K.o) U
  have hfinal : c8.stk K.o = List.reverse (gateFormulaEnc i Gate.not) ++ (FormulaSym.andMark :: O) := by
    rw [show c8.stk K.o = List.replicate (i + 2) FormulaSym.endMark ++ FormulaSym.varMark ::
        (FormulaSym.notMark :: (List.replicate (i + 3) FormulaSym.endMark ++ FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)) by rfl]
    rw [varEnc_rev_cons (i + 1) (FormulaSym.notMark :: (List.replicate (i + 3) FormulaSym.endMark ++ FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))]
    rw [varEnc_rev_cons (i + 2) (FormulaSym.iffMark :: FormulaSym.andMark :: O)]
    rw [show (varEnc (i + 1)).reverse ++ FormulaSym.notMark :: ((varEnc (i + 2)).reverse ++ FormulaSym.iffMark :: FormulaSym.andMark :: O)
        = List.reverse (gateFormulaEnc i Gate.not) ++ FormulaSym.andMark :: O by
      rw [reverse_gateFormulaEnc i Gate.not]
      rw [reverse_gateExprEnc_not i]
      simp [List.append_assoc, List.cons_append]]
  have htop : c8 = ⟨some Label.loop, St.emit Gate.not, stkL rest (i + 2) 0
      (List.reverse (gateFormulaEnc i Gate.not) ++ FormulaSym.andMark :: O) U⟩ := by
    apply Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext k
      cases k <;> (try rw [hfinal]) <;> simp [c8]
  have htot : (flip bind Sstep)^[1 + (i + 2 + (i + 2 + (1 + (1 + (i + 2 + (i + 2 + 1))))))]
      (some c0) = some c8 :=
    iter_compose 1 (i + 2 + (i + 2 + (1 + (1 + (i + 2 + (i + 2 + 1)))))) h1
      (iter_compose (i + 2) (i + 2 + (1 + (1 + (i + 2 + (i + 2 + 1))))) h2
        (iter_compose (i + 2) (1 + (1 + (i + 2 + (i + 2 + 1)))) h3
          (iter_compose 1 (1 + (i + 2 + (i + 2 + 1))) h4
            (iter_compose 1 (i + 2 + (i + 2 + 1)) h5
              (iter_compose (i + 2) (i + 2 + 1) h6
                (iter_compose (i + 2) 1 h7 h8))))))
  rw [show 4 * i + 12 = 1 + (i + 2 + (i + 2 + (1 + (1 + (i + 2 + (i + 2 + 1)))))) by omega]
  rw [htot]
  rw [htop]
  rfl

-- one gate `and` at index `i`: emit `(wire i+1) ∧ (wire i)` and bump the counter
lemma loop_and (v : St) (i : Nat) (rest : List Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[6 * i + 16]
      (some (⟨some Label.loop, v, stkL (Gate.and :: rest) (i + 1) 0 O U⟩ : (mach).Cfg))
    = some (⟨some Label.loop, St.emit Gate.and, stkL rest (i + 2) 0
        (List.reverse (gateFormulaEnc i Gate.and) ++ FormulaSym.andMark :: O) U⟩ : (mach).Cfg) := by
  let c0 : (mach).Cfg := ⟨some Label.loop, v, stkL (Gate.and :: rest) (i + 1) 0 O U⟩
  let c1 : (mach).Cfg := ⟨some Label.moveGF, St.mv (some Gate.and), stkL rest (i + 1) 0
      (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩
  let c2 : (mach).Cfg := ⟨some Label.restoreGF, St.rs (some Gate.and), stkL rest 0 (i + 1)
      (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩
  let c3 : (mach).Cfg := ⟨some Label.emitDispatch, St.emit Gate.and, stkL rest (i + 1) 0
      (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)) U⟩
  let c4 : (mach).Cfg := ⟨some Label.emitAnd, St.emit Gate.and, stkL rest (i + 1) 0
      (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)) U⟩
  let c5 : (mach).Cfg := ⟨some Label.moveAnd1, St.mv (some Gate.and), stkL rest (i + 1) 0
      (FormulaSym.varMark :: FormulaSym.andMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩
  let c6 : (mach).Cfg := ⟨some Label.restoreAnd1, St.rs (some Gate.and), stkL rest 0 (i + 1)
      (FormulaSym.varMark :: FormulaSym.andMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩
  let c7 : (mach).Cfg := ⟨some Label.moveAnd2, St.mv (some Gate.and), stkL rest (i + 1) 0
      (FormulaSym.varMark :: (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.andMark ::
        (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))))) U⟩
  let c8 : (mach).Cfg := ⟨some Label.restoreAnd2, St.rs (some Gate.and), stkL rest 0 (i + 1)
      (FormulaSym.varMark :: (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.andMark ::
        (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))))) U⟩
  let c9 : (mach).Cfg := ⟨some Label.dec, St.emit Gate.and, stkL rest (i + 1) 0
      (List.replicate (i + 1) FormulaSym.endMark ++ (FormulaSym.varMark :: (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.andMark ::
        (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)))))) U⟩
  let c10 : (mach).Cfg := ⟨some Label.loop, St.emit Gate.and, stkL rest (i + 2) 0
      (List.replicate (i + 1) FormulaSym.endMark ++ (FormulaSym.varMark :: (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.andMark ::
        (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)))))) U⟩
  have h1 : (flip bind Sstep)^[1] (some c0) = some c1 := by
    exact loop_step v Gate.and rest (i + 1) O U
  have h2 : (flip bind Sstep)^[(i + 1) + 1] (some c1) = some c2 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.moveGF, St.mv (some Gate.and), stkL rest (i + 1) 0 (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreGF, St.rs (some Gate.and), stkL rest 0 (i + 1) (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using moveGF_phase rest (i + 1) 0 Gate.and (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U
  have h3 : (flip bind Sstep)^[(i + 1) + 1] (some c2) = some c3 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.restoreGF, St.rs (some Gate.and), stkL rest 0 (i + 1) (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩ : (mach).Cfg))
        = some (⟨some Label.emitDispatch, St.emit Gate.and, stkL rest (i + 1) 0 (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using restoreGF_phase rest (i + 1) 0 Gate.and (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U
  have h4 : (flip bind Sstep)^[1] (some c3) = some c4 := by
    exact emitDispatch_and rest (i + 1) (c3.stk K.o) U
  have h5 : (flip bind Sstep)^[1] (some c4) = some c5 := by
    exact emitAnd_step rest (i + 1) (c4.stk K.o) U
  have h6 : (flip bind Sstep)^[(i + 1) + 1] (some c5) = some c6 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.moveAnd1, St.mv (some Gate.and), stkL rest (i + 1) 0 (FormulaSym.varMark :: FormulaSym.andMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreAnd1, St.rs (some Gate.and), stkL rest 0 (i + 1) (FormulaSym.varMark :: FormulaSym.andMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using moveAnd1_phase rest (i + 1) 0 Gate.and (c5.stk K.o) U
  have h7 : (flip bind Sstep)^[(i + 1) + 1] (some c6) = some c7 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.restoreAnd1, St.rs (some Gate.and), stkL rest 0 (i + 1) (FormulaSym.varMark :: FormulaSym.andMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩ : (mach).Cfg))
        = some (⟨some Label.moveAnd2, St.mv (some Gate.and), stkL rest (i + 1) 0 (FormulaSym.varMark :: (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.andMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))))) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using restoreAnd1_phase rest (i + 1) 0 Gate.and (c6.stk K.o) U
  have h8 : (flip bind Sstep)^[(i + 1) + 1] (some c7) = some c8 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.moveAnd2, St.mv (some Gate.and), stkL rest (i + 1) 0 (FormulaSym.varMark :: (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.andMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))))) U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreAnd2, St.rs (some Gate.and), stkL rest 0 (i + 1) (FormulaSym.varMark :: (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.andMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))))) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using moveAnd2_phase rest (i + 1) 0 Gate.and (c7.stk K.o) U
  have h9 : (flip bind Sstep)^[(i + 1) + 1] (some c8) = some c9 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.restoreAnd2, St.rs (some Gate.and), stkL rest 0 (i + 1) (FormulaSym.varMark :: (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.andMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))))) U⟩ : (mach).Cfg))
        = some (⟨some Label.dec, St.emit Gate.and, stkL rest (i + 1) 0 (List.replicate (i + 1) FormulaSym.endMark ++ (FormulaSym.varMark :: (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.andMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)))))) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using restoreAnd2_phase rest (i + 1) 0 Gate.and (c8.stk K.o) U
  have h10 : (flip bind Sstep)^[1] (some c9) = some c10 := by
    exact dec_step (v := St.emit Gate.and) rest (i + 1) (c9.stk K.o) U
  have hfinal : c10.stk K.o = List.reverse (gateFormulaEnc i Gate.and) ++ (FormulaSym.andMark :: O) := by
    rw [show c10.stk K.o = List.replicate (i + 1) FormulaSym.endMark ++ FormulaSym.varMark ::
        (List.replicate (i + 2) FormulaSym.endMark ++ FormulaSym.varMark ::
          (FormulaSym.andMark :: (List.replicate (i + 3) FormulaSym.endMark ++ FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) by rfl]
    rw [varEnc_rev_cons i (List.replicate (i + 2) FormulaSym.endMark ++ FormulaSym.varMark ::
        (FormulaSym.andMark :: (List.replicate (i + 3) FormulaSym.endMark ++ FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)))]
    rw [varEnc_rev_cons (i + 1) (FormulaSym.andMark :: (List.replicate (i + 3) FormulaSym.endMark ++ FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))]
    rw [varEnc_rev_cons (i + 2) (FormulaSym.iffMark :: FormulaSym.andMark :: O)]
    rw [show (varEnc i).reverse ++ ((varEnc (i + 1)).reverse ++ FormulaSym.andMark :: ((varEnc (i + 2)).reverse ++ FormulaSym.iffMark :: FormulaSym.andMark :: O))
        = List.reverse (gateFormulaEnc i Gate.and) ++ (FormulaSym.andMark :: O) by
      rw [reverse_gateFormulaEnc i Gate.and]
      rw [reverse_gateExprEnc_and i]
      simp [List.append_assoc, List.cons_append]]
  have htop : c10 = ⟨some Label.loop, St.emit Gate.and, stkL rest (i + 2) 0
      (List.reverse (gateFormulaEnc i Gate.and) ++ FormulaSym.andMark :: O) U⟩ := by
    apply Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext k
      cases k <;> (try rw [hfinal]) <;> simp [c10]
  have htot : (flip bind Sstep)^[1 + (i + 2 + (i + 2 + (1 + (1 + (i + 2 + (i + 2 + (i + 2 + (i + 2 + 1))))))))]
      (some c0) = some c10 :=
    iter_compose 1 (i + 2 + (i + 2 + (1 + (1 + (i + 2 + (i + 2 + (i + 2 + (i + 2 + 1)))))))) h1
      (iter_compose (i + 2) (i + 2 + (1 + (1 + (i + 2 + (i + 2 + (i + 2 + (i + 2 + 1))))))) h2
        (iter_compose (i + 2) (1 + (1 + (i + 2 + (i + 2 + (i + 2 + (i + 2 + 1)))))) h3
          (iter_compose 1 (1 + (i + 2 + (i + 2 + (i + 2 + (i + 2 + 1))))) h4
            (iter_compose 1 (i + 2 + (i + 2 + (i + 2 + (i + 2 + 1)))) h5
              (iter_compose (i + 2) (i + 2 + (i + 2 + (i + 2 + 1))) h6
                (iter_compose (i + 2) (i + 2 + (i + 2 + 1)) h7
                  (iter_compose (i + 2) (i + 2 + 1) h8
                    (iter_compose (i + 2) 1 h9 h10))))))))
  rw [show 6 * i + 16 = 1 + (i + 2 + (i + 2 + (1 + (1 + (i + 2 + (i + 2 + (i + 2 + (i + 2 + 1)))))))) by omega]
  rw [htot]
  rw [htop]
  rfl

-- one gate `or` at index `i`: emit `(wire i+1) ∨ (wire i)` and bump the counter
lemma loop_or (v : St) (i : Nat) (rest : List Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[6 * i + 16]
      (some (⟨some Label.loop, v, stkL (Gate.or :: rest) (i + 1) 0 O U⟩ : (mach).Cfg))
    = some (⟨some Label.loop, St.emit Gate.or, stkL rest (i + 2) 0
        (List.reverse (gateFormulaEnc i Gate.or) ++ FormulaSym.andMark :: O) U⟩ : (mach).Cfg) := by
  let c0 : (mach).Cfg := ⟨some Label.loop, v, stkL (Gate.or :: rest) (i + 1) 0 O U⟩
  let c1 : (mach).Cfg := ⟨some Label.moveGF, St.mv (some Gate.or), stkL rest (i + 1) 0
      (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩
  let c2 : (mach).Cfg := ⟨some Label.restoreGF, St.rs (some Gate.or), stkL rest 0 (i + 1)
      (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩
  let c3 : (mach).Cfg := ⟨some Label.emitDispatch, St.emit Gate.or, stkL rest (i + 1) 0
      (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)) U⟩
  let c4 : (mach).Cfg := ⟨some Label.emitOr, St.emit Gate.or, stkL rest (i + 1) 0
      (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)) U⟩
  let c5 : (mach).Cfg := ⟨some Label.moveOr1, St.mv (some Gate.or), stkL rest (i + 1) 0
      (FormulaSym.varMark :: FormulaSym.orMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩
  let c6 : (mach).Cfg := ⟨some Label.restoreOr1, St.rs (some Gate.or), stkL rest 0 (i + 1)
      (FormulaSym.varMark :: FormulaSym.orMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩
  let c7 : (mach).Cfg := ⟨some Label.moveOr2, St.mv (some Gate.or), stkL rest (i + 1) 0
      (FormulaSym.varMark :: (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.orMark ::
        (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))))) U⟩
  let c8 : (mach).Cfg := ⟨some Label.restoreOr2, St.rs (some Gate.or), stkL rest 0 (i + 1)
      (FormulaSym.varMark :: (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.orMark ::
        (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))))) U⟩
  let c9 : (mach).Cfg := ⟨some Label.dec, St.emit Gate.or, stkL rest (i + 1) 0
      (List.replicate (i + 1) FormulaSym.endMark ++ (FormulaSym.varMark :: (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.orMark ::
        (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)))))) U⟩
  let c10 : (mach).Cfg := ⟨some Label.loop, St.emit Gate.or, stkL rest (i + 2) 0
      (List.replicate (i + 1) FormulaSym.endMark ++ (FormulaSym.varMark :: (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.orMark ::
        (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)))))) U⟩
  have h1 : (flip bind Sstep)^[1] (some c0) = some c1 := by
    exact loop_step v Gate.or rest (i + 1) O U
  have h2 : (flip bind Sstep)^[(i + 1) + 1] (some c1) = some c2 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.moveGF, St.mv (some Gate.or), stkL rest (i + 1) 0 (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreGF, St.rs (some Gate.or), stkL rest 0 (i + 1) (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using moveGF_phase rest (i + 1) 0 Gate.or (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U
  have h3 : (flip bind Sstep)^[(i + 1) + 1] (some c2) = some c3 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.restoreGF, St.rs (some Gate.or), stkL rest 0 (i + 1) (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U⟩ : (mach).Cfg))
        = some (⟨some Label.emitDispatch, St.emit Gate.or, stkL rest (i + 1) 0 (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using restoreGF_phase rest (i + 1) 0 Gate.or (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O) U
  have h4 : (flip bind Sstep)^[1] (some c3) = some c4 := by
    exact emitDispatch_or rest (i + 1) (c3.stk K.o) U
  have h5 : (flip bind Sstep)^[1] (some c4) = some c5 := by
    exact emitOr_step rest (i + 1) (c4.stk K.o) U
  have h6 : (flip bind Sstep)^[(i + 1) + 1] (some c5) = some c6 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.moveOr1, St.mv (some Gate.or), stkL rest (i + 1) 0 (FormulaSym.varMark :: FormulaSym.orMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreOr1, St.rs (some Gate.or), stkL rest 0 (i + 1) (FormulaSym.varMark :: FormulaSym.orMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using moveOr1_phase rest (i + 1) 0 Gate.or (c5.stk K.o) U
  have h7 : (flip bind Sstep)^[(i + 1) + 1] (some c6) = some c7 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.restoreOr1, St.rs (some Gate.or), stkL rest 0 (i + 1) (FormulaSym.varMark :: FormulaSym.orMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) U⟩ : (mach).Cfg))
        = some (⟨some Label.moveOr2, St.mv (some Gate.or), stkL rest (i + 1) 0 (FormulaSym.varMark :: (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.orMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))))) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using restoreOr1_phase rest (i + 1) 0 Gate.or (c6.stk K.o) U
  have h8 : (flip bind Sstep)^[(i + 1) + 1] (some c7) = some c8 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.moveOr2, St.mv (some Gate.or), stkL rest (i + 1) 0 (FormulaSym.varMark :: (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.orMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))))) U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreOr2, St.rs (some Gate.or), stkL rest 0 (i + 1) (FormulaSym.varMark :: (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.orMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))))) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using moveOr2_phase rest (i + 1) 0 Gate.or (c7.stk K.o) U
  have h9 : (flip bind Sstep)^[(i + 1) + 1] (some c8) = some c9 := by
    change (flip bind Sstep)^[(i + 1) + 1]
        (some (⟨some Label.restoreOr2, St.rs (some Gate.or), stkL rest 0 (i + 1) (FormulaSym.varMark :: (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.orMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))))) U⟩ : (mach).Cfg))
        = some (⟨some Label.dec, St.emit Gate.or, stkL rest (i + 1) 0 (List.replicate (i + 1) FormulaSym.endMark ++ (FormulaSym.varMark :: (List.replicate (i + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.orMark :: (List.replicate (i + 3) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)))))) U⟩ : (mach).Cfg)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using restoreOr2_phase rest (i + 1) 0 Gate.or (c8.stk K.o) U
  have h10 : (flip bind Sstep)^[1] (some c9) = some c10 := by
    exact dec_step (v := St.emit Gate.or) rest (i + 1) (c9.stk K.o) U
  have hfinal : c10.stk K.o = List.reverse (gateFormulaEnc i Gate.or) ++ (FormulaSym.andMark :: O) := by
    rw [show c10.stk K.o = List.replicate (i + 1) FormulaSym.endMark ++ FormulaSym.varMark ::
        (List.replicate (i + 2) FormulaSym.endMark ++ FormulaSym.varMark ::
          (FormulaSym.orMark :: (List.replicate (i + 3) FormulaSym.endMark ++ FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))) by rfl]
    rw [varEnc_rev_cons i (List.replicate (i + 2) FormulaSym.endMark ++ FormulaSym.varMark ::
        (FormulaSym.orMark :: (List.replicate (i + 3) FormulaSym.endMark ++ FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O)))]
    rw [varEnc_rev_cons (i + 1) (FormulaSym.orMark :: (List.replicate (i + 3) FormulaSym.endMark ++ FormulaSym.varMark :: FormulaSym.iffMark :: FormulaSym.andMark :: O))]
    rw [varEnc_rev_cons (i + 2) (FormulaSym.iffMark :: FormulaSym.andMark :: O)]
    rw [show (varEnc i).reverse ++ ((varEnc (i + 1)).reverse ++ FormulaSym.orMark :: ((varEnc (i + 2)).reverse ++ FormulaSym.iffMark :: FormulaSym.andMark :: O))
        = List.reverse (gateFormulaEnc i Gate.or) ++ (FormulaSym.andMark :: O) by
      rw [reverse_gateFormulaEnc i Gate.or]
      rw [reverse_gateExprEnc_or i]
      simp [List.append_assoc, List.cons_append]]
  have htop : c10 = ⟨some Label.loop, St.emit Gate.or, stkL rest (i + 2) 0
      (List.reverse (gateFormulaEnc i Gate.or) ++ FormulaSym.andMark :: O) U⟩ := by
    apply Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext k
      cases k <;> (try rw [hfinal]) <;> simp [c10]
  have htot : (flip bind Sstep)^[1 + (i + 2 + (i + 2 + (1 + (1 + (i + 2 + (i + 2 + (i + 2 + (i + 2 + 1))))))))]
      (some c0) = some c10 :=
    iter_compose 1 (i + 2 + (i + 2 + (1 + (1 + (i + 2 + (i + 2 + (i + 2 + (i + 2 + 1)))))))) h1
      (iter_compose (i + 2) (i + 2 + (1 + (1 + (i + 2 + (i + 2 + (i + 2 + (i + 2 + 1))))))) h2
        (iter_compose (i + 2) (1 + (1 + (i + 2 + (i + 2 + (i + 2 + (i + 2 + 1)))))) h3
          (iter_compose 1 (1 + (i + 2 + (i + 2 + (i + 2 + (i + 2 + 1))))) h4
            (iter_compose 1 (i + 2 + (i + 2 + (i + 2 + (i + 2 + 1)))) h5
              (iter_compose (i + 2) (i + 2 + (i + 2 + (i + 2 + 1))) h6
                (iter_compose (i + 2) (i + 2 + (i + 2 + 1)) h7
                  (iter_compose (i + 2) (i + 2 + 1) h8
                    (iter_compose (i + 2) 1 h9 h10))))))))
  rw [show 6 * i + 16 = 1 + (i + 2 + (i + 2 + (1 + (1 + (i + 2 + (i + 2 + (i + 2 + (i + 2 + 1)))))))) by omega]
  rw [htot]
  rw [htop]
  rfl

-- the reversed gate-formula list for a cons splits into the suffix and this gate
lemma reverse_gateFormulasList (i : Nat) (g : Gate) (rest : List Gate) :
    List.reverse (gateFormulasList i (g :: rest)) =
      List.reverse (gateFormulasList (i + 1) rest) ++ List.reverse (gateFormulaEnc i g) ++ [FormulaSym.andMark] := by
  simp [gateFormulasList, List.reverse_cons, List.reverse_append, List.append_assoc]

-- the loop phase: emit every gate's clause, then stop (empty buffer → emitTrue)
lemma loop_phase_aux (v : St) (i : Nat) (gates : List Gate) (O U : List FormulaSym) :
    (flip bind Sstep)^[loopSteps i gates]
      (some (⟨some Label.loop, v, stkL gates (i + 1) 0 O U⟩ : (mach).Cfg))
    = some (⟨some Label.emitTrue, St.done, stkL [] (i + gates.length + 1) 0
        (List.reverse (gateFormulasList i gates) ++ O) U⟩ : (mach).Cfg) := by
  induction gates generalizing i O v with
  | nil =>
      have h : Sstep (⟨some Label.loop, v, stkL [] (i + 1) 0 O U⟩ : (mach).Cfg)
          = some (⟨some Label.emitTrue, St.done, stkL [] (i + 1) 0 O U⟩ : (mach).Cfg) := by
        simpa using loop_empty v (i + 1) O U
      simpa [loopSteps, gateFormulasList, flip] using h
  | cons g rest ih =>
      have hg : (flip bind Sstep)^[gateSteps i g]
          (some (⟨some Label.loop, v, stkL (g :: rest) (i + 1) 0 O U⟩ : (mach).Cfg))
          = some (⟨some Label.loop, St.emit g, stkL rest (i + 2) 0
              (List.reverse (gateFormulaEnc i g) ++ FormulaSym.andMark :: O) U⟩ : (mach).Cfg) := by
        cases g with
        | input => simpa [gateSteps] using loop_input v i rest O U
        | const b => simpa [gateSteps] using loop_const v i rest O U
        | not => simpa [gateSteps] using loop_not v i rest O U
        | and => simpa [gateSteps] using loop_and v i rest O U
        | or => simpa [gateSteps] using loop_or v i rest O U
      have hih' : (flip bind Sstep)^[loopSteps (i + 1) rest]
          (some (⟨some Label.loop, St.emit g, stkL rest (i + 2) 0
              (List.reverse (gateFormulaEnc i g) ++ FormulaSym.andMark :: O) U⟩ : (mach).Cfg))
          = some (⟨some Label.emitTrue, St.done, stkL [] ((i + 1) + rest.length + 1) 0
              (List.reverse (gateFormulasList (i + 1) rest) ++ (List.reverse (gateFormulaEnc i g) ++ FormulaSym.andMark :: O)) U⟩ : (mach).Cfg) := by
        change (flip bind Sstep)^[loopSteps (i + 1) rest]
            (some (⟨some Label.loop, St.emit g, stkL rest (i + 2) 0
                (List.reverse (gateFormulaEnc i g) ++ FormulaSym.andMark :: O) U⟩ : (mach).Cfg))
            = some (⟨some Label.emitTrue, St.done, stkL [] ((i + 1) + rest.length + 1) 0
                (List.reverse (gateFormulasList (i + 1) rest) ++ (List.reverse (gateFormulaEnc i g) ++ FormulaSym.andMark :: O)) U⟩ : (mach).Cfg)
        exact ih (v := St.emit g) (i := i + 1) (O := List.reverse (gateFormulaEnc i g) ++ FormulaSym.andMark :: O)
      rw [loopSteps]
      rw [show gateSteps i g + loopSteps (i + 1) rest = loopSteps (i + 1) rest + gateSteps i g by omega]
      rw [Function.iterate_add_apply]
      rw [hg]
      change (flip bind Sstep)^[loopSteps (i + 1) rest]
          (some (⟨some Label.loop, St.emit g, stkL rest (i + 2) 0
              (List.reverse (gateFormulaEnc i g) ++ FormulaSym.andMark :: O) U⟩ : (mach).Cfg))
          = some (⟨some Label.emitTrue, St.done, stkL [] (i + (g :: rest).length + 1) 0
              (List.reverse (gateFormulasList i (g :: rest)) ++ O) U⟩ : (mach).Cfg)
      rw [hih']
      simp [reverse_gateFormulasList, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.append_assoc]

-- ============================================================
-- Gate loop: finish (emitTrue clears the counter, copyOut to out)
-- ============================================================

-- emitTrue: pop one counter unit
lemma emitTrue_step (v : St) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.emitTrue, v, stkL [] (c + 1) 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitTrue, St.mv none, stkL [] c 0 O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
-- emitTrue: counter empty → push the trailing `lit true`, goto copyOut
lemma emitTrue_done (v : St) (O U : List FormulaSym) :
    Sstep (⟨some Label.emitTrue, v, stkL [] 0 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.copyOut, St.done, stkL [] 0 0 (FormulaSym.lit true :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep]
-- emitTrue phase: clear the counter, then push `lit true`
lemma emitTrue_phase (v : St) (c : Nat) (O U : List FormulaSym) :
    (flip bind Sstep)^[c + 1]
      (some (⟨some Label.emitTrue, v, stkL [] c 0 O U⟩ : (mach).Cfg))
    = some (⟨some Label.copyOut, St.done, stkL [] 0 0 (FormulaSym.lit true :: O) U⟩ : (mach).Cfg) := by
  induction c generalizing v O U with
  | zero =>
      have h := emitTrue_done v O U
      change (flip bind Sstep) (some (⟨some Label.emitTrue, v, stkL [] 0 0 O U⟩ : (mach).Cfg))
        = some (⟨some Label.copyOut, St.done, stkL [] 0 0 (FormulaSym.lit true :: O) U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ c ih =>
      have h := emitTrue_step v c O U
      rw [show Nat.succ c + 1 = c + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[c + 1]
          (Sstep (⟨some Label.emitTrue, v, stkL [] (c + 1) 0 O U⟩ : (mach).Cfg))
        = some (⟨some Label.copyOut, St.done, stkL [] 0 0 (FormulaSym.lit true :: O) U⟩ : (mach).Cfg)
      rw [h]
      exact ih (St.mv none) O U

-- copyOut: pop one symbol from o onto out
lemma copyOut_step (v : St) (s : FormulaSym) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.copyOut, v, stkL [] c 0 (s :: O) U⟩ : (mach).Cfg)
      = some (⟨some Label.copyOut, St.sym s, stkL [] c 0 O (s :: U)⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep]
-- copyOut: o empty → done, resetting the state to init
lemma copyOut_done (v : St) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.copyOut, v, stkL [] c 0 [] U⟩ : (mach).Cfg)
      = some (⟨some Label.done, St.init, stkL [] c 0 [] U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep]
-- copyOut phase: transfer o to out (reversing), then goto done
lemma copyOut_phase (v : St) (c : Nat) (O U : List FormulaSym) :
    (flip bind Sstep)^[O.length + 1]
      (some (⟨some Label.copyOut, v, stkL [] c 0 O U⟩ : (mach).Cfg))
    = some (⟨some Label.done, St.init, stkL [] c 0 [] (O.reverse ++ U)⟩ : (mach).Cfg) := by
  induction O generalizing v U with
  | nil =>
      have h := copyOut_done v c [] U
      change (flip bind Sstep) (some (⟨some Label.copyOut, v, stkL [] c 0 [] U⟩ : (mach).Cfg))
        = some (⟨some Label.done, St.init, stkL [] c 0 [] U⟩ : (mach).Cfg)
      simpa [flip] using h
  | cons s rest ih =>
      have h := copyOut_step v s c rest U
      rw [show (s :: rest).length + 1 = (rest.length + 1) + 1 by simp [List.length_cons]]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[rest.length + 1]
          (Sstep (⟨some Label.copyOut, v, stkL [] c 0 (s :: rest) U⟩ : (mach).Cfg))
        = some (⟨some Label.done, St.init, stkL [] c 0 [] ((s :: rest).reverse ++ U)⟩ : (mach).Cfg)
      rw [h]
      have hih := ih (St.sym s) (s :: U)
      calc
        (flip bind Sstep)^[rest.length + 1]
            (some (⟨some Label.copyOut, St.sym s, stkL [] c 0 rest (s :: U)⟩ : (mach).Cfg))
          = some (⟨some Label.done, St.init, stkL [] c 0 [] (rest.reverse ++ (s :: U))⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.done, St.init, stkL [] c 0 [] ((s :: rest).reverse ++ U)⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkL, List.reverse_cons, List.append_assoc]

-- the done label halts, leaving the state at init
lemma done_step (S : ∀ k : K, List (Γk k)) :
    Sstep (⟨some Label.done, St.init, S⟩ : (mach).Cfg)
      = some (⟨none, St.init, S⟩ : (mach).Cfg) := by
  simp [Sstep, prog]

-- ============================================================
-- Time analysis
-- ============================================================

-- each gate takes at most 6·i + 16 steps at index i
lemma gateSteps_le (i : Nat) (g : Gate) : gateSteps i g ≤ 6 * i + 16 := by
  cases g <;> simp [gateSteps] <;> omega

-- the whole loop phase takes at most |gates|·(6·(i+|gates|)+16) + 1 steps
lemma loopSteps_le (i : Nat) (gates : List Gate) :
    loopSteps i gates ≤ gates.length * (6 * (i + gates.length) + 16) + 1 := by
  induction gates generalizing i with
  | nil => simp [loopSteps]
  | cons g rest ih =>
      have hg : gateSteps i g ≤ 6 * (i + (g :: rest).length) + 16 := by
        cases g <;> simp [gateSteps, List.length_cons] <;> omega
      have hih : loopSteps (i + 1) rest ≤ rest.length * (6 * ((i + 1) + rest.length) + 16) + 1 :=
        ih (i + 1)
      rw [loopSteps]
      simp [List.length_cons] at hg ⊢
      nlinarith [hg, hih]

-- the length of the emitted gate formulas is quadratic in the number of gates
lemma gateFormulasList_length_le (i : Nat) (gates : List Gate) :
    (gateFormulasList i gates).length ≤ (3 * i + 3 * gates.length + 9) * gates.length := by
  induction gates generalizing i with
  | nil => simp [gateFormulasList]
  | cons g rest ih =>
      have hg : (gateExprEnc i g).length ≤ 2 * i + 6 := by
        cases g <;> simp [gateExprEnc, varEnc, List.length_append] <;> omega
      have hterm : (gateFormulaEnc i g).length + 1 ≤ 3 * i + 12 := by
        have ht : (FormulaSym.andMark :: gateFormulaEnc i g).length ≤ 3 * i + 12 := by
          simp [gateFormulaEnc, varEnc, List.length_append]
          nlinarith [hg]
        simpa [List.length_cons] using ht
      have hih := ih (i + 1)
      rw [gateFormulasList]
      simp [List.length_append]
      nlinarith [hterm, hih]

-- specialising to the start index 0
lemma gateFormulasList_0_length_le (gates : List Gate) :
    (gateFormulasList 0 gates).length ≤ 3 * gates.length * gates.length + 9 * gates.length := by
  have h := gateFormulasList_length_le 0 gates
  nlinarith

-- the polynomial time bound of the reduction machine
noncomputable def csTime : Polynomial ℕ := 9 * Polynomial.X ^ 2 + 32 * Polynomial.X + 16

-- the machine's input/output alphabets
def csInputAlphabet : (mach).Γ (mach).k₀ ≃ Gate := Equiv.refl _
def csOutputAlphabet : (mach).Γ (mach).k₁ ≃ FormulaSym := Equiv.refl _

-- ============================================================
-- Header phase on the full stack (buf holds the gates)
-- ============================================================

-- header: push the top-level andMark and the output wire's varMark
lemma header_step (gates : List Gate) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.header, St.done, stkL gates c 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveHeader, St.mv none, stkL gates c 0
          (FormulaSym.varMark :: FormulaSym.andMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep]

-- moveHeader: counter → scratch, with the gate buffer untouched
lemma moveHeaderH_step (gates : List Gate) (cnt Tmp : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.moveHeader, St.mv none, stkL gates (cnt + 1) Tmp O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveHeader, St.mv none, stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
lemma moveHeaderH_done (gates : List Gate) (Tmp : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.moveHeader, St.mv none, stkL gates 0 Tmp O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreHeader, St.rs none, stkL gates 0 Tmp O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog]
lemma moveHeaderH_phase (gates : List Gate) (cnt Tmp : Nat) (O U : List FormulaSym) :
    (flip bind Sstep)^[cnt + 1]
      (some (⟨some Label.moveHeader, St.mv none, stkL gates cnt Tmp O U⟩ : (mach).Cfg))
    = some (⟨some Label.restoreHeader, St.rs none, stkL gates 0 (Tmp + cnt) O U⟩ : (mach).Cfg) := by
  induction cnt generalizing Tmp O U with
  | zero =>
      have h := moveHeaderH_done gates Tmp O U
      change (flip bind Sstep) (some (⟨some Label.moveHeader, St.mv none, stkL gates 0 Tmp O U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreHeader, St.rs none, stkL gates 0 (Tmp + 0) O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ cnt ih =>
      have hone := moveHeaderH_step gates cnt Tmp O U
      rw [show Nat.succ cnt + 1 = cnt + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[cnt + 1]
          (Sstep (⟨some Label.moveHeader, St.mv none, stkL gates (cnt + 1) Tmp O U⟩ : (mach).Cfg))
        = some (⟨some Label.restoreHeader, St.rs none, stkL gates 0 (Tmp + (cnt + 1)) O U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (Tmp + 1) O U
      calc
        (flip bind Sstep)^[cnt + 1]
            (some (⟨some Label.moveHeader, St.mv none, stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg))
          = some (⟨some Label.restoreHeader, St.rs none, stkL gates 0 ((Tmp + 1) + cnt) O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.restoreHeader, St.rs none, stkL gates 0 (Tmp + (cnt + 1)) O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkL, Nat.add_comm, Nat.add_assoc] <;> try omega

-- restoreHeader: scratch → endMarks on o and units on cnt (2 extra endMarks)
lemma restoreHeaderH_step (gates : List Gate) (cnt Tmp : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.restoreHeader, St.rs none, stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreHeader, St.rs none, stkL gates (cnt + 1) Tmp (FormulaSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
lemma restoreHeaderH_done (gates : List Gate) (cnt : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.restoreHeader, St.rs none, stkL gates cnt 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.reset, St.mv none, stkL gates cnt 0
          (FormulaSym.endMark :: FormulaSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog]
lemma restoreHeaderH_phase (gates : List Gate) (Tmp cnt : Nat) (O U : List FormulaSym) :
    (flip bind Sstep)^[Tmp + 1]
      (some (⟨some Label.restoreHeader, St.rs none, stkL gates cnt Tmp O U⟩ : (mach).Cfg))
    = some (⟨some Label.reset, St.mv none, stkL gates (cnt + Tmp) 0
        (List.replicate (Tmp + 2) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg) := by
  induction Tmp generalizing cnt O U with
  | zero =>
      have h := restoreHeaderH_done gates cnt O U
      change (flip bind Sstep) (some (⟨some Label.restoreHeader, St.rs none, stkL gates cnt 0 O U⟩ : (mach).Cfg))
        = some (⟨some Label.reset, St.mv none, stkL gates (cnt + 0) 0
            (List.replicate (0 + 2) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ Tmp ih =>
      have hone := restoreHeaderH_step gates cnt Tmp O U
      rw [show Nat.succ Tmp + 1 = Tmp + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[Tmp + 1]
          (Sstep (⟨some Label.restoreHeader, St.rs none, stkL gates cnt (Tmp + 1) O U⟩ : (mach).Cfg))
        = some (⟨some Label.reset, St.mv none, stkL gates (cnt + (Tmp + 1)) 0
            (List.replicate ((Tmp + 1) + 2) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (cnt + 1) (FormulaSym.endMark :: O) U
      calc
        (flip bind Sstep)^[Tmp + 1]
            (some (⟨some Label.restoreHeader, St.rs none, stkL gates (cnt + 1) Tmp (FormulaSym.endMark :: O) U⟩ : (mach).Cfg))
          = some (⟨some Label.reset, St.mv none, stkL gates ((cnt + 1) + Tmp) 0
              (List.replicate (Tmp + 2) FormulaSym.endMark ++ (FormulaSym.endMark :: O)) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.reset, St.mv none, stkL gates (cnt + (Tmp + 1)) 0
            (List.replicate ((Tmp + 1) + 2) FormulaSym.endMark ++ O) U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stkL, replicate_cons_append, List.append_assoc] <;> try omega

-- reset: clear the counter, push a single unit for the first loop gate
lemma resetH_step (gates : List Gate) (c : Nat) (O U : List FormulaSym) :
    Sstep (⟨some Label.reset, St.mv none, stkL gates (c + 1) 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.reset, St.mv none, stkL gates c 0 O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]
lemma resetH_done (gates : List Gate) (O U : List FormulaSym) :
    Sstep (⟨some Label.reset, St.mv none, stkL gates 0 0 O U⟩ : (mach).Cfg)
      = some (⟨some Label.loop, St.done, stkL gates 1 0 O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stkL, Function.update, prog, List.replicate_succ]
lemma resetH_phase (gates : List Gate) (c : Nat) (O U : List FormulaSym) :
    (flip bind Sstep)^[c + 1]
      (some (⟨some Label.reset, St.mv none, stkL gates c 0 O U⟩ : (mach).Cfg))
    = some (⟨some Label.loop, St.done, stkL gates 1 0 O U⟩ : (mach).Cfg) := by
  induction c generalizing O U with
  | zero =>
      have h := resetH_done gates O U
      change (flip bind Sstep) (some (⟨some Label.reset, St.mv none, stkL gates 0 0 O U⟩ : (mach).Cfg))
        = some (⟨some Label.loop, St.done, stkL gates 1 0 O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ c ih =>
      have h := resetH_step gates c O U
      rw [show Nat.succ c + 1 = c + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[c + 1]
          (Sstep (⟨some Label.reset, St.mv none, stkL gates (c + 1) 0 O U⟩ : (mach).Cfg))
        = some (⟨some Label.loop, St.done, stkL gates 1 0 O U⟩ : (mach).Cfg)
      rw [h]
      exact ih O U

-- the reversed output stack equals the target formula list
lemma copyOut_reverse (gates : List Gate) :
    (FormulaSym.lit true :: (List.reverse (gateFormulasList 0 gates) ++
        List.replicate (gates.length + 2) FormulaSym.endMark ++
        FormulaSym.varMark :: FormulaSym.andMark :: [])).reverse
      = circuitToFormulaList gates := by
  simp [circuitToFormulaList, varEnc, List.reverse_cons, List.reverse_append,
    List.reverse_replicate, List.append_assoc]

-- the reduction machine computes `circuitToFormulaList` in polynomial time
noncomputable def csOutputsFun (gates : List Gate) :
    TM2OutputsInTime mach gates (some (circuitToFormulaList gates)) (csTime.eval gates.length) := by
  let n := gates.length
  let initC : (mach).Cfg := ⟨some Label.count, St.init, stk gates [] 0 [] [] []⟩
  let C1 : (mach).Cfg := ⟨some Label.reorder, St.done, stk [] gates.reverse n [] [] []⟩
  let C2 : (mach).Cfg := ⟨some Label.header, St.done, stkL gates n 0 [] []⟩
  let C3 : (mach).Cfg := ⟨some Label.moveHeader, St.mv none, stkL gates n 0
      (FormulaSym.varMark :: FormulaSym.andMark :: []) []⟩
  let C4 : (mach).Cfg := ⟨some Label.restoreHeader, St.rs none, stkL gates 0 n
      (FormulaSym.varMark :: FormulaSym.andMark :: []) []⟩
  let C5 : (mach).Cfg := ⟨some Label.reset, St.mv none, stkL gates n 0
      (List.replicate (n + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.andMark :: [])) []⟩
  let C6 : (mach).Cfg := ⟨some Label.loop, St.done, stkL gates 1 0
      (List.replicate (n + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.andMark :: [])) []⟩
  let C7 : (mach).Cfg := ⟨some Label.emitTrue, St.done, stkL [] (n + 1) 0
      (List.reverse (gateFormulasList 0 gates) ++ (List.replicate (n + 2) FormulaSym.endMark ++
        (FormulaSym.varMark :: FormulaSym.andMark :: []))) []⟩
  let C8 : (mach).Cfg := ⟨some Label.copyOut, St.done, stkL [] 0 0
      (FormulaSym.lit true :: (List.reverse (gateFormulasList 0 gates) ++
        (List.replicate (n + 2) FormulaSym.endMark ++
          (FormulaSym.varMark :: FormulaSym.andMark :: [])))) []⟩
  let C9 : (mach).Cfg := ⟨some Label.done, St.init, stkL [] 0 0 [] ((C8.stk K.o).reverse ++ [])⟩
  let C10 : (mach).Cfg := ⟨none, St.init, stkL [] 0 0 [] ((C8.stk K.o).reverse ++ [])⟩
  have hcount : EvalsToInTime Sstep initC (some C1) (n + 1) := by
    refine ⟨⟨n + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[n + 1] (some initC) = some C1
    change (flip bind Sstep)^[n + 1]
        (some (⟨some Label.count, St.init, stk gates [] 0 [] [] []⟩ : (mach).Cfg))
        = some (⟨some Label.reorder, St.done, stk [] gates.reverse n [] [] []⟩ : (mach).Cfg)
    rw [count_phase_aux St.init gates [] 0 [] [] []]
    simpa [n, List.append_nil, Nat.zero_add]
  have hreorder : EvalsToInTime Sstep C1 (some C2) (n + 1) := by
    refine ⟨⟨n + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[n + 1] (some C1) = some C2
    change (flip bind Sstep)^[n + 1]
        (some (⟨some Label.reorder, St.done, stkR gates.reverse [] n [] []⟩ : (mach).Cfg))
        = some (⟨some Label.header, St.done, stkL gates n 0 [] []⟩ : (mach).Cfg)
    rw [show n + 1 = gates.reverse.length + 1 by simp [n, List.length_reverse]]
    rw [reorder_phase_aux St.done gates.reverse [] n [] []]
    apply congrArg some
    apply Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext k
      cases k <;> simp [stkR, stkL, List.reverse_reverse, List.append_nil, Nat.zero_add]
  have hheader : EvalsToInTime Sstep C2 (some C3) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change (flip bind Sstep) (some C2) = some C3
    exact header_step gates n [] []
  have hmoveHeader : EvalsToInTime Sstep C3 (some C4) (n + 1) := by
    refine ⟨⟨n + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[n + 1] (some C3) = some C4
    change (flip bind Sstep)^[n + 1]
        (some (⟨some Label.moveHeader, St.mv none, stkL gates n 0 (FormulaSym.varMark :: FormulaSym.andMark :: []) []⟩ : (mach).Cfg))
        = some (⟨some Label.restoreHeader, St.rs none, stkL gates 0 n (FormulaSym.varMark :: FormulaSym.andMark :: []) []⟩ : (mach).Cfg)
    rw [moveHeaderH_phase gates n 0 (FormulaSym.varMark :: FormulaSym.andMark :: []) []]
    try simp [n, Nat.zero_add]
  have hrestoreHeader : EvalsToInTime Sstep C4 (some C5) (n + 1) := by
    refine ⟨⟨n + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[n + 1] (some C4) = some C5
    change (flip bind Sstep)^[n + 1]
        (some (⟨some Label.restoreHeader, St.rs none, stkL gates 0 n (FormulaSym.varMark :: FormulaSym.andMark :: []) []⟩ : (mach).Cfg))
        = some (⟨some Label.reset, St.mv none, stkL gates n 0
            (List.replicate (n + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.andMark :: [])) []⟩ : (mach).Cfg)
    rw [restoreHeaderH_phase gates n 0 (FormulaSym.varMark :: FormulaSym.andMark :: []) []]
    try simp [n, Nat.zero_add]
  have hreset : EvalsToInTime Sstep C5 (some C6) (n + 1) := by
    refine ⟨⟨n + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[n + 1] (some C5) = some C6
    change (flip bind Sstep)^[n + 1]
        (some (⟨some Label.reset, St.mv none, stkL gates n 0
            (List.replicate (n + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.andMark :: [])) []⟩ : (mach).Cfg))
        = some (⟨some Label.loop, St.done, stkL gates 1 0
            (List.replicate (n + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.andMark :: [])) []⟩ : (mach).Cfg)
    rw [resetH_phase gates n
      (List.replicate (n + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.andMark :: [])) []]
    try simp [n]
  have hloop : EvalsToInTime Sstep C6 (some C7) (loopSteps 0 gates) := by
    refine ⟨⟨loopSteps 0 gates, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[loopSteps 0 gates] (some C6) = some C7
    change (flip bind Sstep)^[loopSteps 0 gates]
        (some (⟨some Label.loop, St.done, stkL gates 1 0
            (List.replicate (n + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.andMark :: [])) []⟩ : (mach).Cfg))
        = some (⟨some Label.emitTrue, St.done, stkL [] (n + 1) 0
            (List.reverse (gateFormulasList 0 gates) ++ (List.replicate (n + 2) FormulaSym.endMark ++
              (FormulaSym.varMark :: FormulaSym.andMark :: []))) []⟩ : (mach).Cfg)
    rw [loop_phase_aux St.done 0 gates
      (List.replicate (n + 2) FormulaSym.endMark ++ (FormulaSym.varMark :: FormulaSym.andMark :: [])) []]
    try simp [n, Nat.add_assoc]
  have hemTrue : EvalsToInTime Sstep C7 (some C8) (n + 2) := by
    refine ⟨⟨n + 2, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[n + 2] (some C7) = some C8
    change (flip bind Sstep)^[n + 2]
        (some (⟨some Label.emitTrue, St.done, stkL [] (n + 1) 0
            (List.reverse (gateFormulasList 0 gates) ++ (List.replicate (n + 2) FormulaSym.endMark ++
              (FormulaSym.varMark :: FormulaSym.andMark :: []))) []⟩ : (mach).Cfg))
        = some (⟨some Label.copyOut, St.done, stkL [] 0 0
            (FormulaSym.lit true :: (List.reverse (gateFormulasList 0 gates) ++
              (List.replicate (n + 2) FormulaSym.endMark ++
                (FormulaSym.varMark :: FormulaSym.andMark :: [])))) []⟩ : (mach).Cfg)
    rw [emitTrue_phase St.done (n + 1)
      (List.reverse (gateFormulasList 0 gates) ++ (List.replicate (n + 2) FormulaSym.endMark ++
        (FormulaSym.varMark :: FormulaSym.andMark :: []))) []]
    try simp [n]
  have hcopyOut : EvalsToInTime Sstep C8 (some C9) ((C8.stk K.o).length + 1) := by
    refine ⟨⟨(C8.stk K.o).length + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[(C8.stk K.o).length + 1] (some C8) = some C9
    change (flip bind Sstep)^[(C8.stk K.o).length + 1]
        (some (⟨some Label.copyOut, St.done, stkL [] 0 0 (C8.stk K.o) []⟩ : (mach).Cfg))
        = some (⟨some Label.done, St.init, stkL [] 0 0 [] ((C8.stk K.o).reverse ++ [])⟩ : (mach).Cfg)
    rw [copyOut_phase St.done 0 (C8.stk K.o) []]
    try simp [List.append_nil]
  have hdone : EvalsToInTime Sstep C9 (some C10) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change (flip bind Sstep) (some C9) = some C10
    exact done_step (C9.stk)
  have h12 : EvalsToInTime Sstep initC (some C2) ((n + 1) + (n + 1)) :=
    EvalsToInTime.trans Sstep (n + 1) (n + 1) initC C1 (some C2) hcount hreorder
  have h123 : EvalsToInTime Sstep initC (some C3) (1 + ((n + 1) + (n + 1))) :=
    EvalsToInTime.trans Sstep ((n + 1) + (n + 1)) 1 initC C2 (some C3) h12 hheader
  have h1234 : EvalsToInTime Sstep initC (some C4) ((n + 1) + (1 + ((n + 1) + (n + 1)))) :=
    EvalsToInTime.trans Sstep (1 + ((n + 1) + (n + 1))) (n + 1) initC C3 (some C4) h123 hmoveHeader
  have h12345 : EvalsToInTime Sstep initC (some C5) ((n + 1) + ((n + 1) + (1 + ((n + 1) + (n + 1))))) :=
    EvalsToInTime.trans Sstep ((n + 1) + (1 + ((n + 1) + (n + 1)))) (n + 1) initC C4 (some C5) h1234 hrestoreHeader
  have h123456 : EvalsToInTime Sstep initC (some C6) ((n + 1) + ((n + 1) + ((n + 1) + (1 + ((n + 1) + (n + 1)))))) :=
    EvalsToInTime.trans Sstep ((n + 1) + ((n + 1) + (1 + ((n + 1) + (n + 1))))) (n + 1) initC C5 (some C6) h12345 hreset
  have h1234567 : EvalsToInTime Sstep initC (some C7) (loopSteps 0 gates + ((n + 1) + ((n + 1) + ((n + 1) + (1 + ((n + 1) + (n + 1))))))) :=
    EvalsToInTime.trans Sstep ((n + 1) + ((n + 1) + ((n + 1) + (1 + ((n + 1) + (n + 1)))))) (loopSteps 0 gates) initC C6 (some C7) h123456 hloop
  have h12345678 : EvalsToInTime Sstep initC (some C8) ((n + 2) + (loopSteps 0 gates + ((n + 1) + ((n + 1) + ((n + 1) + (1 + ((n + 1) + (n + 1)))))))) :=
    EvalsToInTime.trans Sstep (loopSteps 0 gates + ((n + 1) + ((n + 1) + ((n + 1) + (1 + ((n + 1) + (n + 1))))))) (n + 2) initC C7 (some C8) h1234567 hemTrue
  have h123456789 : EvalsToInTime Sstep initC (some C9) ((C8.stk K.o).length + 1 + ((n + 2) + (loopSteps 0 gates + ((n + 1) + ((n + 1) + ((n + 1) + (1 + ((n + 1) + (n + 1))))))))) :=
    EvalsToInTime.trans Sstep ((n + 2) + (loopSteps 0 gates + ((n + 1) + ((n + 1) + ((n + 1) + (1 + ((n + 1) + (n + 1)))))))) ((C8.stk K.o).length + 1) initC C8 (some C9) h12345678 hcopyOut
  have h12345678910 : EvalsToInTime Sstep initC (some C10) (1 + ((C8.stk K.o).length + 1 + ((n + 2) + (loopSteps 0 gates + ((n + 1) + ((n + 1) + ((n + 1) + (1 + ((n + 1) + (n + 1)))))))))) :=
    EvalsToInTime.trans Sstep ((C8.stk K.o).length + 1 + ((n + 2) + (loopSteps 0 gates + ((n + 1) + ((n + 1) + ((n + 1) + (1 + ((n + 1) + (n + 1))))))))) 1 initC C9 (some C10) h123456789 hdone
  have hout : (C8.stk K.o).reverse = circuitToFormulaList gates := by
    have horev : (C8.stk K.o).reverse =
        (FormulaSym.lit true :: (List.reverse (gateFormulasList 0 gates) ++
          List.replicate (n + 2) FormulaSym.endMark ++
          FormulaSym.varMark :: FormulaSym.andMark :: [])).reverse := by
      simp [C8, List.append_assoc]
    rw [horev]
    simpa [n] using copyOut_reverse gates
  have hfinalCfg : C10 = haltList mach (circuitToFormulaList gates) := by
    apply Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext k
      cases k <;> simp [C10, haltList, hout]
  have hinit : initList mach gates = initC := by
    apply Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext k
      cases k <;> simp [initC, initList, stk]
  have hloop_le : loopSteps 0 gates ≤ 6 * n * n + 16 * n + 1 := by
    have h := loopSteps_le 0 gates
    nlinarith [h]
  have hoLen : (C8.stk K.o).length ≤ 3 * n * n + 10 * n + 5 := by
    have hlen : (C8.stk K.o).length = (gateFormulasList 0 gates).length + n + 5 := by
      simp [C8, List.length_append, List.length_cons, List.length_replicate]
      omega
    have hgf := gateFormulasList_0_length_le gates
    rw [hlen]
    nlinarith [hgf]
  have hct : csTime.eval n = 9 * n * n + 32 * n + 16 := by
    simp [csTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_natCast]
    ring
  have htotal_le : 1 + ((C8.stk K.o).length + 1 + ((n + 2) + (loopSteps 0 gates + ((n + 1) + ((n + 1) + ((n + 1) + (1 + ((n + 1) + (n + 1))))))))) ≤ csTime.eval n := by
    rw [hct]
    nlinarith [hloop_le, hoLen]
  have hfull : EvalsToInTime Sstep initC (some (haltList mach (circuitToFormulaList gates)))
      (1 + ((C8.stk K.o).length + 1 + ((n + 2) + (loopSteps 0 gates + ((n + 1) + ((n + 1) + ((n + 1) + (1 + ((n + 1) + (n + 1)))))))))) := by
    simpa [hfinalCfg] using h12345678910
  change EvalsToInTime Sstep (initList mach gates) (some (haltList mach (circuitToFormulaList gates)))
      (csTime.eval gates.length)
  rw [hinit]
  exact ⟨hfull.toEvalsTo, le_trans hfull.steps_le_m htotal_le⟩

/-- The reduction machine computes `circuitToFormulaList` in polynomial time. -/
noncomputable def csComputableInPolyTime :
    TM2ComputableInPolyTime (id : List Gate → List Gate) (id : List FormulaSym → List FormulaSym)
      circuitToFormulaList where
  tm := mach
  inputAlphabet := csInputAlphabet
  outputAlphabet := csOutputAlphabet
  time := csTime
  outputsFun := fun gates => by
    simpa [csInputAlphabet, csOutputAlphabet] using csOutputsFun gates

end TM2CS

end Turing

namespace CLRS

namespace Chapter34

/--
**Theorem (CIRCUIT-SAT poly-reduces to SAT, CLRS Lemma 34.6).**  A circuit is
satisfiable iff the formula produced by `circuitToFormulaList` is satisfiable.
-/
theorem circuitSAT_reducible_to_SAT : PolyTimeReducible CIRCUIT_SAT SAT := by
  refine ⟨circuitToFormulaList, ?comp, ?iff⟩
  · exact ⟨Turing.TM2CS.csComputableInPolyTime⟩
  · intro gates
    rw [circuitToFormulaList_eq_enc]
    constructor
    · intro hc
      have hsat := (circuitSatisfiable_iff_satisfiable_circuitToFormula gates).1 hc
      exact ⟨circuitToFormula gates, rfl, hsat⟩
    · intro hs
      rcases hs with ⟨f, hf, hsat⟩
      have hsat' : Formula.Satisfiable (circuitToFormula gates) := by
        have hf_eq : f = circuitToFormula gates := by
          rw [← decode_enc f, ← decode_enc (circuitToFormula gates), hf]
        rwa [← hf_eq]
      exact (circuitSatisfiable_iff_satisfiable_circuitToFormula gates).2 hsat'

end Chapter34

end CLRS
