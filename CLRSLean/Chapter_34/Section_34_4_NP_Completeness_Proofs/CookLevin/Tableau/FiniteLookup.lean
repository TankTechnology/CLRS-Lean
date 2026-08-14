import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau

/-!
# CLRS Section 34.4 - Finite one-hot lookup circuits

This module compiles static functions between finite one-hot families.  Static
preimages determine the circuit shape: single-source maps disjoin each fiber,
pair maps first materialize every pair conjunction and then disjoin its image
fiber, and predicates disjoin only their true preimage.

Main results:

- Definition {lit}`oneHotMap`: finite one-hot maps with exact cost {lit}`n + m`.
- Definition {lit}`oneHotPairMap`: finite pair maps with exact cost
  {lit}`2 * n * p + m`.
- Definition {lit}`oneHotPredicate`: finite predicates with exact true-fiber
  cost and the uniform bound {lit}`n + 1`.

Current gaps:

- None for these finite lookup primitives.  Downstream {lit}`StatementCircuits`
  and {lit}`TransitionCircuits` supply recursive statement compilation and the
  local step check.  Non-aliasing row allocation and verified whole-tableau
  assembly remain milestone 8F.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

open scoped BigOperators

/-! ## Static finite fibers -/

/-- Source coordinates mapped to one fixed target coordinate. -/
def oneHotPreimage {n m : Nat} (f : Fin n → Fin m) (target : Fin m) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => f i = target

/-- Source wires belonging to one fixed target fiber, in canonical finite-set
order. -/
private def oneHotPreimageWires {n m : Nat}
    (source : Fin n → CircuitBuilder.Wire)
    (f : Fin n → Fin m) (target : Fin m) : List CircuitBuilder.Wire :=
  (oneHotPreimage f target).toList.map source

@[simp] private theorem oneHotPreimageWires_length {n m : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m)
    (target : Fin m) :
    (oneHotPreimageWires source f target).length =
      (oneHotPreimage f target).card := by
  simp [oneHotPreimageWires]

private theorem oneHotPreimageWires_valid {n m : Nat}
    {base : CircuitBuilder} (source : Fin n → CircuitBuilder.Wire)
    (f : Fin n → Fin m) (target : Fin m)
    (hsource : ∀ i, base.WireValid (source i)) :
    ∀ wire ∈ oneHotPreimageWires source f target, base.WireValid wire := by
  intro wire hwire
  simp only [oneHotPreimageWires, Finset.mem_toList, List.mem_map] at hwire
  rcases hwire with ⟨i, _, rfl⟩
  exact hsource i

private theorem sum_oneHotPreimage_card {n m : Nat} (f : Fin n → Fin m) :
    (∑ target : Fin m, (oneHotPreimage f target).card) = n := by
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset (Fin m))) (f := f)
    (fun i _ => Finset.mem_univ (f i))
  simpa [oneHotPreimage] using hpartition.symm

private theorem oneHotPreimage_any_encodeOneHot {n m : Nat}
    (f : Fin n → Fin m) (chosen : Fin n) (target : Fin m) :
    (oneHotPreimage f target).toList.any (encodeOneHot chosen) =
      encodeOneHot (f chosen) target := by
  by_cases h : f chosen = target
  · simp [oneHotPreimage, encodeOneHot, h]
  · have h' : target ≠ f chosen := Ne.symm h
    simp [oneHotPreimage, encodeOneHot, h']
    intro x hx hxchosen
    subst x
    exact h hx

/-! ## Single-source one-hot maps -/

/-- Proof-carrying result of mapping one finite one-hot wire family. -/
structure OneHotMapResult (base : CircuitBuilder) {n m : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m) where
  /-- Builder after all target-fiber disjunctions. -/
  builder : CircuitBuilder
  /-- One output wire for every target coordinate. -/
  wires : Fin m → CircuitBuilder.Wire
  /-- The lookup preserves the complete input builder prefix. -/
  extension : base.Extends builder
  /-- Every target-coordinate output belongs to the result builder. -/
  valid : ∀ j, builder.WireValid (wires j)
  /-- Every source is used once and every target fiber has one false seed. -/
  gate_delta : builder.gates.length = base.gates.length + (n + m)
  /-- Each output is the disjunction of its static source preimage. -/
  eval : ∀ inputs j, builder.evalWire inputs (wires j) =
    (oneHotPreimage f j).toList.any
      (fun i => base.evalWire inputs (source i))

private structure OneHotMapBodyResult (base : CircuitBuilder) {n m : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m)
    (k : Nat) (hk : k ≤ m) where
  builder : CircuitBuilder
  wires : Fin k → CircuitBuilder.Wire
  extension : base.Extends builder
  valid : ∀ j, builder.WireValid (wires j)
  gate_delta : builder.gates.length = base.gates.length +
    ∑ j : Fin k, ((oneHotPreimage f (Fin.castLE hk j)).card + 1)
  eval : ∀ inputs j, builder.evalWire inputs (wires j) =
    (oneHotPreimage f (Fin.castLE hk j)).toList.any
      (fun i => base.evalWire inputs (source i))

private def oneHotMapBody (base : CircuitBuilder) {n m : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m)
    (hsource : ∀ i, base.WireValid (source i)) :
    (k : Nat) → (hk : k ≤ m) → OneHotMapBodyResult base source f k hk
  | 0, hk =>
      { builder := base
        wires := fun j => Fin.elim0 j
        extension := .refl base
        valid := fun j => Fin.elim0 j
        gate_delta := by simp
        eval := fun _ j => Fin.elim0 j }
  | k + 1, hk => by
      let hkPrevious : k ≤ m := by omega
      let previous := oneHotMapBody base source f hsource k hkPrevious
      let target : Fin m := Fin.castLE hk (Fin.last k)
      let fiber := oneHotPreimageWires source f target
      have hfiber : ∀ wire ∈ fiber, previous.builder.WireValid wire := by
        intro wire hwire
        exact previous.extension.wireValid
          (oneHotPreimageWires_valid source f target hsource wire hwire)
      let output := previous.builder.disjunction fiber hfiber
      let hext := CircuitBuilder.disjunction_extends previous.builder fiber hfiber
      let wires : Fin (k + 1) → CircuitBuilder.Wire := fun j =>
        if hj : j.val < k then previous.wires ⟨j.val, hj⟩ else output.2
      refine
        { builder := output.1
          wires := wires
          extension := previous.extension.trans hext
          valid := ?_
          gate_delta := ?_
          eval := ?_ }
      · intro j
        simp only [wires]
        split
        next hj => exact hext.wireValid (previous.valid ⟨j.val, hj⟩)
        next => exact CircuitBuilder.disjunction_wireValid previous.builder fiber hfiber
      · rw [CircuitBuilder.disjunction_gate_delta, previous.gate_delta]
        rw [Fin.sum_univ_castSucc]
        have hcast : ∀ j : Fin k,
            Fin.castLE hkPrevious j = Fin.castLE hk j.castSucc := by
          intro j
          exact Fin.ext rfl
        simp_rw [hcast]
        simp only [fiber, target, oneHotPreimageWires_length]
        omega
      · intro inputs j
        simp only [wires]
        split
        next hj =>
          rw [hext.evalWire_eq inputs (previous.valid ⟨j.val, hj⟩)]
          rw [previous.eval]
          have hindex : Fin.castLE hkPrevious ⟨j.val, hj⟩ =
              Fin.castLE hk j := Fin.ext rfl
          rw [hindex]
        next hj =>
          have hjlast : j = Fin.last k := by
            apply Fin.ext
            simp
            omega
          subst j
          rw [CircuitBuilder.disjunction_eval]
          simp only [fiber, target, oneHotPreimageWires, List.any_map]
          apply List.any_congr rfl
          intro i
          change previous.builder.evalWire inputs (source i) =
            base.evalWire inputs (source i)
          rw [previous.extension.evalWire_eq inputs (hsource i)]

/-- Map a finite one-hot family through a static function. -/
def oneHotMap (base : CircuitBuilder) {n m : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m)
    (hsource : ∀ i, base.WireValid (source i)) :
    OneHotMapResult base source f := by
  let body := oneHotMapBody base source f hsource m (Nat.le_refl m)
  refine
    { builder := body.builder
      wires := body.wires
      extension := body.extension
      valid := body.valid
      gate_delta := ?_
      eval := ?_ }
  · rw [body.gate_delta]
    simp only [Fin.castLE_refl]
    rw [Finset.sum_add_distrib, sum_oneHotPreimage_card]
    simp
  · intro inputs j
    simpa using body.eval inputs j

/-- A finite one-hot map preserves the complete input prefix. -/
theorem oneHotMap_extends (base : CircuitBuilder) {n m : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m)
    (hsource : ∀ i, base.WireValid (source i)) :
    base.Extends (oneHotMap base source f hsource).builder :=
  (oneHotMap base source f hsource).extension

/-- Every finite one-hot map output belongs to its result builder. -/
theorem oneHotMap_wireValid (base : CircuitBuilder) {n m : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m)
    (hsource : ∀ i, base.WireValid (source i)) (j : Fin m) :
    (oneHotMap base source f hsource).builder.WireValid
      ((oneHotMap base source f hsource).wires j) :=
  (oneHotMap base source f hsource).valid j

/-- A finite one-hot map emits exactly {lit}`n + m` gates. -/
theorem oneHotMap_gate_delta (base : CircuitBuilder) {n m : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m)
    (hsource : ∀ i, base.WireValid (source i)) :
    (oneHotMap base source f hsource).builder.gates.length =
      base.gates.length + (n + m) :=
  (oneHotMap base source f hsource).gate_delta

/-- Each finite one-hot map coordinate evaluates to its static fiber OR. -/
theorem oneHotMap_eval (base : CircuitBuilder) {n m : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m)
    (hsource : ∀ i, base.WireValid (source i)) (inputs : Nat → Bool)
    (j : Fin m) :
    (oneHotMap base source f hsource).builder.evalWire inputs
        ((oneHotMap base source f hsource).wires j) =
      (oneHotPreimage f j).toList.any
        (fun i => base.evalWire inputs (source i)) :=
  (oneHotMap base source f hsource).eval inputs j

/-- One-hot map construction is independent of source-validity proofs. -/
theorem oneHotMap_proof_irrel (base : CircuitBuilder) {n m : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m)
    (hsource₁ hsource₂ : ∀ i, base.WireValid (source i)) :
    oneHotMap base source f hsource₁ = oneHotMap base source f hsource₂ := by
  rfl

/-- Mapping an exact canonical source code produces the canonical image code. -/
theorem oneHotMap_eval_encodeOneHot (base : CircuitBuilder) {n m : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m)
    (hsource : ∀ i, base.WireValid (source i)) (inputs : Nat → Bool)
    (chosen : Fin n)
    (hencoded : (fun i => base.evalWire inputs (source i)) =
      encodeOneHot chosen) :
    (fun j => (oneHotMap base source f hsource).builder.evalWire inputs
      ((oneHotMap base source f hsource).wires j)) =
        encodeOneHot (f chosen) := by
  funext j
  rw [oneHotMap_eval, hencoded]
  exact oneHotPreimage_any_encodeOneHot f chosen j

/-- A finite one-hot map preserves the generic one-hot invariant. -/
theorem oneHotMap_oneHot (base : CircuitBuilder) {n m : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m)
    (hsource : ∀ i, base.WireValid (source i)) (inputs : Nat → Bool)
    (hone : OneHot fun i => base.evalWire inputs (source i)) :
    OneHot fun j => (oneHotMap base source f hsource).builder.evalWire inputs
      ((oneHotMap base source f hsource).wires j) := by
  rcases hone with ⟨chosen, hchosen, hunique⟩
  have hencoded : (fun i => base.evalWire inputs (source i)) =
      encodeOneHot chosen := by
    funext i
    by_cases hi : i = chosen
    · subst i
      simp [encodeOneHot, hchosen]
    · have hfalse : base.evalWire inputs (source i) = false :=
        Bool.eq_false_of_not_eq_true (fun htrue => hi (hunique i htrue))
      simp [encodeOneHot, hi, hfalse]
  rw [oneHotMap_eval_encodeOneHot base source f hsource inputs chosen hencoded]
  exact oneHot_encodeOneHot (f chosen)

/-! ## Pair-source one-hot maps -/

/-- Decode one flattened pair coordinate and apply a static binary function. -/
def oneHotPairFunction {n p m : Nat} (f : Fin n → Fin p → Fin m) :
    Fin (n * p) → Fin m :=
  fun q =>
    let pair := finProdFinEquiv.symm q
    f pair.1 pair.2

/-- Flattened pair coordinates mapped to one fixed target coordinate. -/
def oneHotPairPreimage {n p m : Nat} (f : Fin n → Fin p → Fin m)
    (target : Fin m) : Finset (Fin (n * p)) :=
  oneHotPreimage (oneHotPairFunction f) target

private structure OneHotPairAndBodyResult (base : CircuitBuilder) {n p : Nat}
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire) (k : Nat) (hk : k ≤ n * p) where
  builder : CircuitBuilder
  wires : Fin k → CircuitBuilder.Wire
  extension : base.Extends builder
  valid : ∀ q, builder.WireValid (wires q)
  gate_delta : builder.gates.length = base.gates.length + k
  eval : ∀ inputs q,
    builder.evalWire inputs (wires q) =
      let pair := finProdFinEquiv.symm (Fin.castLE hk q)
      base.evalWire inputs (left pair.1) &&
        base.evalWire inputs (right pair.2)

private def oneHotPairAndBody (base : CircuitBuilder) {n p : Nat}
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire)
    (hleft : ∀ i, base.WireValid (left i))
    (hright : ∀ j, base.WireValid (right j)) :
    (k : Nat) → (hk : k ≤ n * p) →
      OneHotPairAndBodyResult base left right k hk
  | 0, hk =>
      { builder := base
        wires := fun q => Fin.elim0 q
        extension := .refl base
        valid := fun q => Fin.elim0 q
        gate_delta := by simp
        eval := fun _ q => Fin.elim0 q }
  | k + 1, hk => by
      let hkPrevious : k ≤ n * p := by omega
      let previous := oneHotPairAndBody base left right hleft hright k hkPrevious
      let q : Fin (n * p) := Fin.castLE hk (Fin.last k)
      let pair := finProdFinEquiv.symm q
      have hleftPrevious : previous.builder.WireValid (left pair.1) :=
        previous.extension.wireValid (hleft pair.1)
      have hrightPrevious : previous.builder.WireValid (right pair.2) :=
        previous.extension.wireValid (hright pair.2)
      let output := previous.builder.and (left pair.1) (right pair.2)
        hleftPrevious hrightPrevious
      let hext := CircuitBuilder.and_extends previous.builder
        (left pair.1) (right pair.2) hleftPrevious hrightPrevious
      let wires : Fin (k + 1) → CircuitBuilder.Wire := fun index =>
        if hindex : index.val < k then
          previous.wires ⟨index.val, hindex⟩
        else output.2
      refine
        { builder := output.1
          wires := wires
          extension := previous.extension.trans hext
          valid := ?_
          gate_delta := ?_
          eval := ?_ }
      · intro index
        simp only [wires]
        split
        next hindex => exact hext.wireValid (previous.valid ⟨index.val, hindex⟩)
        next =>
          simpa only [output] using
            (CircuitBuilder.and_wireValid previous.builder
              (left pair.1) (right pair.2) hleftPrevious hrightPrevious)
      · dsimp only [output]
        rw [CircuitBuilder.and_gate_delta, previous.gate_delta]
        omega
      · intro inputs index
        simp only [wires]
        split
        next hindex =>
          rw [hext.evalWire_eq inputs (previous.valid ⟨index.val, hindex⟩)]
          rw [previous.eval]
          have hcast : Fin.castLE hkPrevious ⟨index.val, hindex⟩ =
              Fin.castLE hk index := Fin.ext rfl
          rw [hcast]
        next hindex =>
          have hlast : index = Fin.last k := by
            apply Fin.ext
            simp
            omega
          subst index
          dsimp only [output]
          rw [CircuitBuilder.and_eval]
          have hleftEval := previous.extension.evalWire_eq inputs (hleft pair.1)
          have hrightEval := previous.extension.evalWire_eq inputs (hright pair.2)
          simp only [q, pair] at hleftEval hrightEval ⊢
          rw [hleftEval, hrightEval]

private structure OneHotPairAndResult (base : CircuitBuilder) {n p : Nat}
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire) where
  builder : CircuitBuilder
  wires : Fin (n * p) → CircuitBuilder.Wire
  extension : base.Extends builder
  valid : ∀ q, builder.WireValid (wires q)
  gate_delta : builder.gates.length = base.gates.length + n * p
  eval : ∀ inputs q,
    builder.evalWire inputs (wires q) =
      let pair := finProdFinEquiv.symm q
      base.evalWire inputs (left pair.1) &&
        base.evalWire inputs (right pair.2)

private def oneHotPairAnd (base : CircuitBuilder) {n p : Nat}
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire)
    (hleft : ∀ i, base.WireValid (left i))
    (hright : ∀ j, base.WireValid (right j)) :
    OneHotPairAndResult base left right := by
  let body := oneHotPairAndBody base left right hleft hright (n * p)
    (Nat.le_refl (n * p))
  exact
    { builder := body.builder
      wires := body.wires
      extension := body.extension
      valid := body.valid
      gate_delta := body.gate_delta
      eval := by intro inputs q; simpa using body.eval inputs q }

/-- Proof-carrying result of mapping two one-hot families through a static
binary function. -/
structure OneHotPairMapResult (base : CircuitBuilder) {n p m : Nat}
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire)
    (f : Fin n → Fin p → Fin m) where
  /-- Builder after pair conjunctions and target-fiber disjunctions. -/
  builder : CircuitBuilder
  /-- One output wire for every target coordinate. -/
  wires : Fin m → CircuitBuilder.Wire
  /-- The pair lookup preserves the complete input builder prefix. -/
  extension : base.Extends builder
  /-- Every pair-lookup output belongs to the result builder. -/
  valid : ∀ j, builder.WireValid (wires j)
  /-- Serial pair materialization followed by fiber ORs has exact cost. -/
  gate_delta : builder.gates.length = base.gates.length + (2 * n * p + m)
  /-- Each output is the OR of the conjunctions in its static pair fiber. -/
  eval : ∀ inputs j, builder.evalWire inputs (wires j) =
    (oneHotPairPreimage f j).toList.any fun q =>
      let pair := finProdFinEquiv.symm q
      base.evalWire inputs (left pair.1) &&
        base.evalWire inputs (right pair.2)

/-- Map two finite one-hot families through a static binary function. -/
def oneHotPairMap (base : CircuitBuilder) {n p m : Nat}
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire)
    (f : Fin n → Fin p → Fin m)
    (hleft : ∀ i, base.WireValid (left i))
    (hright : ∀ j, base.WireValid (right j)) :
    OneHotPairMapResult base left right f := by
  let pairs := oneHotPairAnd base left right hleft hright
  let mapped := oneHotMap pairs.builder pairs.wires (oneHotPairFunction f)
    pairs.valid
  refine
    { builder := mapped.builder
      wires := mapped.wires
      extension := pairs.extension.trans mapped.extension
      valid := mapped.valid
      gate_delta := ?_
      eval := ?_ }
  · rw [mapped.gate_delta, pairs.gate_delta]
    ring
  · intro inputs j
    rw [mapped.eval]
    simp only [oneHotPairPreimage]
    apply List.any_congr rfl
    intro q
    exact pairs.eval inputs q

/-- A finite pair lookup preserves the complete input prefix. -/
theorem oneHotPairMap_extends (base : CircuitBuilder) {n p m : Nat}
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire)
    (f : Fin n → Fin p → Fin m)
    (hleft : ∀ i, base.WireValid (left i))
    (hright : ∀ j, base.WireValid (right j)) :
    base.Extends (oneHotPairMap base left right f hleft hright).builder :=
  (oneHotPairMap base left right f hleft hright).extension

/-- Every finite pair-lookup output belongs to its result builder. -/
theorem oneHotPairMap_wireValid (base : CircuitBuilder) {n p m : Nat}
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire)
    (f : Fin n → Fin p → Fin m)
    (hleft : ∀ i, base.WireValid (left i))
    (hright : ∀ j, base.WireValid (right j)) (target : Fin m) :
    (oneHotPairMap base left right f hleft hright).builder.WireValid
      ((oneHotPairMap base left right f hleft hright).wires target) :=
  (oneHotPairMap base left right f hleft hright).valid target

/-- A finite pair lookup emits exactly {lit}`2 * n * p + m` gates. -/
theorem oneHotPairMap_gate_delta (base : CircuitBuilder) {n p m : Nat}
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire)
    (f : Fin n → Fin p → Fin m)
    (hleft : ∀ i, base.WireValid (left i))
    (hright : ∀ j, base.WireValid (right j)) :
    (oneHotPairMap base left right f hleft hright).builder.gates.length =
      base.gates.length + (2 * n * p + m) :=
  (oneHotPairMap base left right f hleft hright).gate_delta

/-- Each finite pair-lookup coordinate evaluates to its static pair-fiber OR. -/
theorem oneHotPairMap_eval (base : CircuitBuilder) {n p m : Nat}
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire)
    (f : Fin n → Fin p → Fin m)
    (hleft : ∀ i, base.WireValid (left i))
    (hright : ∀ j, base.WireValid (right j)) (inputs : Nat → Bool)
    (target : Fin m) :
    (oneHotPairMap base left right f hleft hright).builder.evalWire inputs
        ((oneHotPairMap base left right f hleft hright).wires target) =
      (oneHotPairPreimage f target).toList.any fun q =>
        let pair := finProdFinEquiv.symm q
        base.evalWire inputs (left pair.1) &&
          base.evalWire inputs (right pair.2) :=
  (oneHotPairMap base left right f hleft hright).eval inputs target

/-- Pair lookup construction is independent of wire-validity proofs. -/
theorem oneHotPairMap_proof_irrel (base : CircuitBuilder) {n p m : Nat}
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire)
    (f : Fin n → Fin p → Fin m)
    (hleft₁ hleft₂ : ∀ i, base.WireValid (left i))
    (hright₁ hright₂ : ∀ j, base.WireValid (right j)) :
    oneHotPairMap base left right f hleft₁ hright₁ =
      oneHotPairMap base left right f hleft₂ hright₂ := by
  rfl

/-- Canonical source codes produce the canonical binary-function image code. -/
theorem oneHotPairMap_eval_encodeOneHot (base : CircuitBuilder) {n p m : Nat}
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire)
    (f : Fin n → Fin p → Fin m)
    (hleft : ∀ i, base.WireValid (left i))
    (hright : ∀ j, base.WireValid (right j)) (inputs : Nat → Bool)
    (chosenLeft : Fin n) (chosenRight : Fin p)
    (hleftEncoded : (fun i => base.evalWire inputs (left i)) =
      encodeOneHot chosenLeft)
    (hrightEncoded : (fun j => base.evalWire inputs (right j)) =
      encodeOneHot chosenRight) :
    (fun target =>
      (oneHotPairMap base left right f hleft hright).builder.evalWire inputs
        ((oneHotPairMap base left right f hleft hright).wires target)) =
      encodeOneHot (f chosenLeft chosenRight) := by
  let chosenPair : Fin (n * p) := finProdFinEquiv (chosenLeft, chosenRight)
  have hpairs : (fun q =>
      let pair := finProdFinEquiv.symm q
      base.evalWire inputs (left pair.1) &&
        base.evalWire inputs (right pair.2)) = encodeOneHot chosenPair := by
    funext q
    have hleftValue := congrFun hleftEncoded (finProdFinEquiv.symm q).1
    have hrightValue := congrFun hrightEncoded (finProdFinEquiv.symm q).2
    dsimp only
    rw [hleftValue, hrightValue]
    simp only [encodeOneHot, chosenPair]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.and_eq_true]
    constructor
    · rintro ⟨hfst, hsnd⟩
      have hp : finProdFinEquiv.symm q = (chosenLeft, chosenRight) := by
        apply Prod.ext
        · exact hfst
        · exact hsnd
      apply finProdFinEquiv.symm.injective
      simpa using hp
    · intro hq
      subst q
      simp
  funext target
  rw [oneHotPairMap_eval, hpairs]
  simpa [oneHotPairPreimage, oneHotPairFunction, chosenPair] using
    (oneHotPreimage_any_encodeOneHot (oneHotPairFunction f) chosenPair target)

/-! ## Boolean predicates over one-hot families -/

/-- Source coordinates on which a static Boolean predicate is true. -/
def oneHotTruePreimage {n : Nat} (f : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => f i = true

/-- Source wires selected by the true preimage of a Boolean predicate. -/
private def oneHotTruePreimageWires {n : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool) :
    List CircuitBuilder.Wire :=
  (oneHotTruePreimage f).toList.map source

@[simp] private theorem oneHotTruePreimageWires_length {n : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool) :
    (oneHotTruePreimageWires source f).length = (oneHotTruePreimage f).card := by
  simp [oneHotTruePreimageWires]

private theorem oneHotTruePreimageWires_valid {n : Nat}
    {base : CircuitBuilder} (source : Fin n → CircuitBuilder.Wire)
    (f : Fin n → Bool) (hsource : ∀ i, base.WireValid (source i)) :
    ∀ wire ∈ oneHotTruePreimageWires source f, base.WireValid wire := by
  intro wire hwire
  simp only [oneHotTruePreimageWires, Finset.mem_toList, List.mem_map] at hwire
  rcases hwire with ⟨i, _, rfl⟩
  exact hsource i

/-- Proof-carrying result of querying a static predicate on one-hot wires. -/
structure OneHotPredicateResult (base : CircuitBuilder) {n : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool) where
  /-- Builder after the true-fiber disjunction. -/
  builder : CircuitBuilder
  /-- Wire indicating that the selected coordinate satisfies the predicate. -/
  wire : CircuitBuilder.Wire
  /-- The predicate query preserves the complete input builder prefix. -/
  extension : base.Extends builder
  /-- The predicate output belongs to the result builder. -/
  valid : builder.WireValid wire
  /-- The exact cost is one false seed plus the true-fiber cardinality. -/
  gate_delta : builder.gates.length = base.gates.length +
    ((oneHotTruePreimage f).card + 1)
  /-- The exact cost is uniformly bounded by {lit}`n + 1`. -/
  gate_bound : builder.gates.length ≤ base.gates.length + (n + 1)
  /-- The output is the disjunction over the static true preimage. -/
  eval : ∀ inputs, builder.evalWire inputs wire =
    (oneHotTruePreimage f).toList.any fun i =>
      base.evalWire inputs (source i)

/-- Query a static Boolean predicate on one finite one-hot family. -/
def oneHotPredicate (base : CircuitBuilder) {n : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool)
    (hsource : ∀ i, base.WireValid (source i)) :
    OneHotPredicateResult base source f := by
  let wires := oneHotTruePreimageWires source f
  have hwires := oneHotTruePreimageWires_valid source f hsource
  let output := base.disjunction wires hwires
  refine
    { builder := output.1
      wire := output.2
      extension := CircuitBuilder.disjunction_extends base wires hwires
      valid := CircuitBuilder.disjunction_wireValid base wires hwires
      gate_delta := ?_
      gate_bound := ?_
      eval := ?_ }
  · rw [CircuitBuilder.disjunction_gate_delta]
    simp only [wires, oneHotTruePreimageWires_length]
    omega
  · rw [CircuitBuilder.disjunction_gate_delta]
    simp only [wires, oneHotTruePreimageWires_length]
    have hcard : (oneHotTruePreimage f).card ≤ n := by
      simpa using (oneHotTruePreimage f).card_le_univ
    omega
  · intro inputs
    rw [CircuitBuilder.disjunction_eval]
    simp only [wires, oneHotTruePreimageWires, List.any_map]
    rfl

/-- A one-hot predicate query preserves the complete input prefix. -/
theorem oneHotPredicate_extends (base : CircuitBuilder) {n : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool)
    (hsource : ∀ i, base.WireValid (source i)) :
    base.Extends (oneHotPredicate base source f hsource).builder :=
  (oneHotPredicate base source f hsource).extension

/-- The one-hot predicate output belongs to its result builder. -/
theorem oneHotPredicate_wireValid (base : CircuitBuilder) {n : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool)
    (hsource : ∀ i, base.WireValid (source i)) :
    (oneHotPredicate base source f hsource).builder.WireValid
      (oneHotPredicate base source f hsource).wire :=
  (oneHotPredicate base source f hsource).valid

/-- A predicate query emits exactly its true-fiber cardinality plus one gate. -/
theorem oneHotPredicate_gate_delta (base : CircuitBuilder) {n : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool)
    (hsource : ∀ i, base.WireValid (source i)) :
    (oneHotPredicate base source f hsource).builder.gates.length =
      base.gates.length + ((oneHotTruePreimage f).card + 1) :=
  (oneHotPredicate base source f hsource).gate_delta

/-- A predicate query emits at most {lit}`n + 1` gates. -/
theorem oneHotPredicate_gate_bound (base : CircuitBuilder) {n : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool)
    (hsource : ∀ i, base.WireValid (source i)) :
    (oneHotPredicate base source f hsource).builder.gates.length ≤
      base.gates.length + (n + 1) :=
  (oneHotPredicate base source f hsource).gate_bound

/-- A one-hot predicate query evaluates to its static true-fiber OR. -/
theorem oneHotPredicate_eval (base : CircuitBuilder) {n : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool)
    (hsource : ∀ i, base.WireValid (source i)) (inputs : Nat → Bool) :
    (oneHotPredicate base source f hsource).builder.evalWire inputs
        (oneHotPredicate base source f hsource).wire =
      (oneHotTruePreimage f).toList.any fun i =>
        base.evalWire inputs (source i) :=
  (oneHotPredicate base source f hsource).eval inputs

/-- Predicate-query construction is independent of wire-validity proofs. -/
theorem oneHotPredicate_proof_irrel (base : CircuitBuilder) {n : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool)
    (hsource₁ hsource₂ : ∀ i, base.WireValid (source i)) :
    oneHotPredicate base source f hsource₁ =
      oneHotPredicate base source f hsource₂ := by
  rfl

/-- A canonical source code makes a static predicate return its chosen value. -/
theorem oneHotPredicate_eval_encodeOneHot (base : CircuitBuilder) {n : Nat}
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool)
    (hsource : ∀ i, base.WireValid (source i)) (inputs : Nat → Bool)
    (chosen : Fin n)
    (hencoded : (fun i => base.evalWire inputs (source i)) =
      encodeOneHot chosen) :
    (oneHotPredicate base source f hsource).builder.evalWire inputs
      (oneHotPredicate base source f hsource).wire = f chosen := by
  rw [oneHotPredicate_eval, hencoded]
  by_cases h : f chosen = true
  · simp [oneHotTruePreimage, encodeOneHot, h]
  · have hfalse : f chosen = false := Bool.eq_false_of_not_eq_true h
    simp [oneHotTruePreimage, encodeOneHot, hfalse]
    intro x hx hxchosen
    subst x
    exact h hx

end

end CLRS.Chapter34.Turing.CookLevin
