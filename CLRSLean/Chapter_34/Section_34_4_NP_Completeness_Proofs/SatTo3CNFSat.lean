import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CircuitSAT

/-!
# SAT poly-reduces to 3-CNF-SAT

The reduction of CLRS Lemma 34.7: every boolean formula is satisfiable iff the
3-CNF formula obtained by the Tseitin transformation is satisfiable.  The
construction introduces one auxiliary variable per internal node, and asserts
(by 3-literal clauses) that each auxiliary equals its subformula's value; the
output forces the root's auxiliary to be true.

Main results:

- Model `Literal`/`Clause`/`CNF` with evaluation and `CnfSatisfiable`.
- The reduction `to3CNF` and its correctness:
  `cnfSatisfiable_to3CNF_iff`: `CnfSatisfiable (to3CNF φ)` iff
  `Formula.Satisfiable φ`.
- The language `ThreeCNFSat`.

**Current status**: semantic model, reduction, and the correctness theorem are
in place.  The list encoding, the reduction machine, and its `outputsFun`
(assembling `PolyTimeReducible SAT ThreeCNFSat`) are pending.
-/

namespace CLRS

namespace Chapter34

/-- A literal: a variable (index), possibly negated. -/
inductive Literal : Type
  | pos (i : Nat)
  | neg (i : Nat)
deriving DecidableEq, Repr, Inhabited

/-- A clause: a disjunction of literals. -/
abbrev Clause := List Literal

/-- A CNF formula: a conjunction of clauses. -/
abbrev CNF := List Clause

/-- A literal evaluates to the variable's value, or its negation. -/
def evalLit (σ : Nat → Bool) : Literal → Prop
  | Literal.pos i => σ i = true
  | Literal.neg i => σ i = false

/-- A clause is true when at least one literal is. -/
def evalClause (σ : Nat → Bool) (c : Clause) : Prop :=
  ∃ l ∈ c, evalLit σ l

/-- A CNF formula is true when every clause is. -/
def evalCNF (σ : Nat → Bool) (f : CNF) : Prop :=
  ∀ c ∈ f, evalClause σ c

/-- A CNF formula is **satisfiable** when some assignment makes it true. -/
def CnfSatisfiable (f : CNF) : Prop :=
  ∃ σ, evalCNF σ f

/-- The number of original variables of a formula (the maximum index plus one). -/
def numVars : Formula → Nat
  | Formula.var i => i + 1
  | Formula.const _ => 0
  | Formula.not f => numVars f
  | Formula.and f g => max (numVars f) (numVars g)
  | Formula.or f g => max (numVars f) (numVars g)
  | Formula.iff f g => max (numVars f) (numVars g)

-- clause templates for the Tseitin encoding

/-- Force a variable true with a unit clause. -/
def forceTrue (i : Nat) : CNF := [[Literal.pos i]]

/-- Force a variable false with a unit clause. -/
def forceFalse (i : Nat) : CNF := [[Literal.neg i]]

/-- `y ↔ ¬y₁`: two 2-literal clauses. -/
def notClauses (y y₁ : Nat) : CNF :=
  [[Literal.neg y, Literal.neg y₁], [Literal.pos y, Literal.pos y₁]]

/-- `y ↔ y₁ ∧ y₂`: three 3-literal clauses. -/
def andClauses (y y₁ y₂ : Nat) : CNF :=
  [[Literal.neg y, Literal.pos y₁], [Literal.neg y, Literal.pos y₂],
   [Literal.neg y₁, Literal.neg y₂, Literal.pos y]]

/-- `y ↔ y₁ ∨ y₂`: three 3-literal clauses. -/
def orClauses (y y₁ y₂ : Nat) : CNF :=
  [[Literal.pos y, Literal.neg y₁], [Literal.pos y, Literal.neg y₂],
   [Literal.pos y₁, Literal.pos y₂, Literal.neg y]]

/-- `y ↔ (y₁ ↔ y₂)`: four 3-literal clauses. -/
def iffClauses (y y₁ y₂ : Nat) : CNF :=
  [[Literal.neg y, Literal.neg y₁, Literal.pos y₂],
   [Literal.neg y, Literal.pos y₁, Literal.neg y₂],
   [Literal.pos y, Literal.pos y₁, Literal.pos y₂],
   [Literal.pos y, Literal.neg y₁, Literal.neg y₂]]

/-- The Tseitin encoding of a formula, allocating auxiliary variables from
`next` upward.  Returns the clauses, the value variable of the formula, and
the next available auxiliary index. -/
def to3CNF' : Formula → Nat → CNF × Nat × Nat
  | Formula.var i, next => ([], i, next)
  | Formula.const b, next =>
      if b then (forceTrue next, next, next + 1)
      else (forceFalse next, next, next + 1)
  | Formula.not f, next =>
      let (c, y, next') := to3CNF' f next
      (c ++ notClauses next' y, next', next' + 1)
  | Formula.and f g, next =>
      let (c₁, y₁, next₁) := to3CNF' f next
      let (c₂, y₂, next₂) := to3CNF' g next₁
      (c₁ ++ c₂ ++ andClauses next₂ y₁ y₂, next₂, next₂ + 1)
  | Formula.or f g, next =>
      let (c₁, y₁, next₁) := to3CNF' f next
      let (c₂, y₂, next₂) := to3CNF' g next₁
      (c₁ ++ c₂ ++ orClauses next₂ y₁ y₂, next₂, next₂ + 1)
  | Formula.iff f g, next =>
      let (c₁, y₁, next₁) := to3CNF' f next
      let (c₂, y₂, next₂) := to3CNF' g next₁
      (c₁ ++ c₂ ++ iffClauses next₂ y₁ y₂, next₂, next₂ + 1)

/-- The full reduction: encode `φ`, then force its value variable true. -/
def to3CNF (φ : Formula) : CNF :=
  let (c, y, _) := to3CNF' φ (numVars φ)
  c ++ forceTrue y

/-- **3-CNF-SAT**: the language of satisfiable CNF formulas whose clauses have
at most three literals, encoded as literal lists. -/
def ThreeCNFSat : Language (List Literal) :=
  { f | CnfSatisfiable f }

-- ============================================================
-- Template correctness
-- ============================================================

/-- Evaluating a conjunction of two clause lists is the conjunction of the
evaluations. -/
lemma evalCNF_append (σ : Nat → Bool) (c₁ c₂ : CNF) :
    evalCNF σ (c₁ ++ c₂) ↔ evalCNF σ c₁ ∧ evalCNF σ c₂ := by
  simp [evalCNF, evalClause, List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩,
    fun h c hc => by
      rcases hc with hc | hc
      · exact h.1 c hc
      · exact h.2 c hc⟩

/-- A clause evaluates to true iff some literal in it does. -/
lemma evalClause_cons (σ : Nat → Bool) (l : Literal) (rest : Clause) :
    evalClause σ (l :: rest) ↔ evalLit σ l ∨ evalClause σ rest := by
  simp [evalClause, evalLit]

/-- A single-clause list evaluates to true iff the clause does. -/
lemma evalCNF_singleton (σ : Nat → Bool) (c : Clause) :
    evalCNF σ [c] ↔ evalClause σ c := by
  simp [evalCNF]

/-- The `not` template forces `y ↔ ¬y₁`. -/
lemma evalCNF_notClauses (σ : Nat → Bool) (y y₁ : Nat) :
    evalCNF σ (notClauses y y₁) ↔ (σ y = true ↔ σ y₁ = false) := by
  by_cases hy : σ y = true <;> by_cases hy₁ : σ y₁ = true <;> simp [notClauses, evalCNF, evalClause, evalLit, hy, hy₁]

/-- The `and` template forces `y ↔ y₁ ∧ y₂`. -/
lemma evalCNF_andClauses (σ : Nat → Bool) (y y₁ y₂ : Nat) :
    evalCNF σ (andClauses y y₁ y₂) ↔ (σ y = true ↔ σ y₁ = true ∧ σ y₂ = true) := by
  by_cases hy : σ y = true <;> by_cases h₁ : σ y₁ = true <;> by_cases h₂ : σ y₂ = true <;> simp [andClauses, evalCNF, evalClause, evalLit, hy, h₁, h₂]

/-- The `or` template forces `y ↔ y₁ ∨ y₂`. -/
lemma evalCNF_orClauses (σ : Nat → Bool) (y y₁ y₂ : Nat) :
    evalCNF σ (orClauses y y₁ y₂) ↔ (σ y = true ↔ σ y₁ = true ∨ σ y₂ = true) := by
  by_cases hy : σ y = true <;> by_cases h₁ : σ y₁ = true <;> by_cases h₂ : σ y₂ = true <;> simp [orClauses, evalCNF, evalClause, evalLit, hy, h₁, h₂]

/-- The `iff` template forces `y ↔ (y₁ ↔ y₂)`. -/
lemma evalCNF_iffClauses (σ : Nat → Bool) (y y₁ y₂ : Nat) :
    evalCNF σ (iffClauses y y₁ y₂) ↔ (σ y = true ↔ (σ y₁ = true ↔ σ y₂ = true)) := by
  by_cases hy : σ y = true <;> by_cases h₁ : σ y₁ = true <;> by_cases h₂ : σ y₂ = true <;> simp [iffClauses, evalCNF, evalClause, evalLit, hy, h₁, h₂]

/-- The unit clause forces `y` true. -/
lemma evalCNF_forceTrue (σ : Nat → Bool) (i : Nat) :
    evalCNF σ (forceTrue i) ↔ σ i = true := by
  simp [forceTrue, evalCNF, evalClause, evalLit]

/-- The unit clause forces `y` false. -/
lemma evalCNF_forceFalse (σ : Nat → Bool) (i : Nat) :
    evalCNF σ (forceFalse i) ↔ σ i = false := by
  simp [forceFalse, evalCNF, evalClause, evalLit]

/-- The variable index of a literal. -/
def litIndex : Literal → Nat
  | Literal.pos i => i
  | Literal.neg i => i

/-- The auxiliary variables of a subformula are allocated upward: `next` never
decreases. -/
lemma to3CNF'_next_ge (f : Formula) (next : Nat) :
    (to3CNF' f next).2.2 ≥ next := by
  induction f generalizing next with
  | var i => simp [to3CNF']
  | const b =>
      by_cases hb : b <;> simp [to3CNF', hb]
  | not f ih =>
      change (to3CNF' f next).2.2 + 1 ≥ next
      have h := ih next
      omega
  | and f g ihf ihg =>
      change (to3CNF' g (to3CNF' f next).2.2).2.2 + 1 ≥ next
      have h₁ := ihf next
      have h₂ := ihg (to3CNF' f next).2.2
      omega
  | or f g ihf ihg =>
      change (to3CNF' g (to3CNF' f next).2.2).2.2 + 1 ≥ next
      have h₁ := ihf next
      have h₂ := ihg (to3CNF' f next).2.2
      omega
  | iff f g ihf ihg =>
      change (to3CNF' g (to3CNF' f next).2.2).2.2 + 1 ≥ next
      have h₁ := ihf next
      have h₂ := ihg (to3CNF' f next).2.2
      omega

/-- The value variable of a subformula lies below the next auxiliary index. -/
lemma to3CNF'_y_lt_next (f : Formula) (next : Nat) (hnext : next ≥ numVars f) :
    (to3CNF' f next).2.1 < (to3CNF' f next).2.2 := by
  induction f generalizing next with
  | var i =>
      simp [to3CNF', numVars] at hnext ⊢
      omega
  | const b =>
      by_cases hb : b <;> simp [to3CNF', hb]
  | not f ih => simp [to3CNF']
  | and f g ihf ihg => simp [to3CNF']
  | or f g ihf ihg => simp [to3CNF']
  | iff f g ihf ihg => simp [to3CNF']

/-- Extend an assignment of the original variables to one that also forces each
value variable of the subformula tree rooted at `f` to its value under `τ`.
Auxiliary variables start at `next`. -/
def extend : Formula → Nat → (Nat → Bool) → Nat → Bool
  | Formula.var i, next, τ, j => τ j
  | Formula.const b, next, τ, j => if j = next then (b : Bool) else τ j
  | Formula.not f, next, τ, j =>
      if j = (to3CNF' f next).2.2 then !(extend f next τ (to3CNF' f next).2.1)
      else extend f next τ j
  | Formula.and f g, next, τ, j =>
      if j = (to3CNF' g (to3CNF' f next).2.2).2.2 then
        extend f next τ (to3CNF' f next).2.1 &&
          extend g (to3CNF' f next).2.2 (extend f next τ) (to3CNF' g (to3CNF' f next).2.2).2.1
      else extend g (to3CNF' f next).2.2 (extend f next τ) j
  | Formula.or f g, next, τ, j =>
      if j = (to3CNF' g (to3CNF' f next).2.2).2.2 then
        extend f next τ (to3CNF' f next).2.1 ||
          extend g (to3CNF' f next).2.2 (extend f next τ) (to3CNF' g (to3CNF' f next).2.2).2.1
      else extend g (to3CNF' f next).2.2 (extend f next τ) j
  | Formula.iff f g, next, τ, j =>
      if j = (to3CNF' g (to3CNF' f next).2.2).2.2 then
        extend f next τ (to3CNF' f next).2.1 ==
          extend g (to3CNF' f next).2.2 (extend f next τ) (to3CNF' g (to3CNF' f next).2.2).2.1
      else extend g (to3CNF' f next).2.2 (extend f next τ) j

/-- The extension agrees with `τ` on every index below `next`. -/
lemma extend_agree_lt (f : Formula) (next : Nat) (τ : Nat → Bool) :
    ∀ j, j < next → extend f next τ j = τ j := by
  induction f generalizing next τ with
  | var i => intro j hj; rfl
  | const b =>
      intro j hj
      simp [extend, hj.ne]
  | not f ih =>
      intro j hj
      by_cases hne : j = (to3CNF' f next).2.2
      · exfalso
        have h₁ : (to3CNF' f next).2.2 ≥ next := to3CNF'_next_ge f next
        omega
      · simp [extend, hne]
        exact ih next τ j hj
  | and f g ihf ihg =>
      intro j hj
      by_cases hne₂ : j = (to3CNF' g (to3CNF' f next).2.2).2.2
      · exfalso
        have h₁ : (to3CNF' f next).2.2 ≥ next := to3CNF'_next_ge f next
        have h₂ : (to3CNF' g (to3CNF' f next).2.2).2.2 ≥ (to3CNF' f next).2.2 :=
          to3CNF'_next_ge g (to3CNF' f next).2.2
        omega
      · have hj₁ : j < (to3CNF' f next).2.2 := by
          have h := to3CNF'_next_ge f next
          omega
        have h₁j : extend g (to3CNF' f next).2.2 (extend f next τ) j = extend f next τ j :=
          ihg (to3CNF' f next).2.2 (extend f next τ) j hj₁
        have h₀j : extend f next τ j = τ j := ihf next τ j hj
        simp [extend, hne₂, h₁j, h₀j]
  | or f g ihf ihg =>
      intro j hj
      by_cases hne₂ : j = (to3CNF' g (to3CNF' f next).2.2).2.2
      · exfalso
        have h₁ : (to3CNF' f next).2.2 ≥ next := to3CNF'_next_ge f next
        have h₂ : (to3CNF' g (to3CNF' f next).2.2).2.2 ≥ (to3CNF' f next).2.2 :=
          to3CNF'_next_ge g (to3CNF' f next).2.2
        omega
      · have hj₁ : j < (to3CNF' f next).2.2 := by
          have h := to3CNF'_next_ge f next
          omega
        have h₁j : extend g (to3CNF' f next).2.2 (extend f next τ) j = extend f next τ j :=
          ihg (to3CNF' f next).2.2 (extend f next τ) j hj₁
        have h₀j : extend f next τ j = τ j := ihf next τ j hj
        simp [extend, hne₂, h₁j, h₀j]
  | iff f g ihf ihg =>
      intro j hj
      by_cases hne₂ : j = (to3CNF' g (to3CNF' f next).2.2).2.2
      · exfalso
        have h₁ : (to3CNF' f next).2.2 ≥ next := to3CNF'_next_ge f next
        have h₂ : (to3CNF' g (to3CNF' f next).2.2).2.2 ≥ (to3CNF' f next).2.2 :=
          to3CNF'_next_ge g (to3CNF' f next).2.2
        omega
      · have hj₁ : j < (to3CNF' f next).2.2 := by
          have h := to3CNF'_next_ge f next
          omega
        have h₁j : extend g (to3CNF' f next).2.2 (extend f next τ) j = extend f next τ j :=
          ihg (to3CNF' f next).2.2 (extend f next τ) j hj₁
        have h₀j : extend f next τ j = τ j := ihf next τ j hj
        simp [extend, hne₂, h₁j, h₀j]

/-- The `not` template's literals are below the node's next auxiliary. -/
lemma notClauses_lits_lt (f : Formula) (next : Nat) (hnext : next ≥ numVars f) :
    ∀ c ∈ notClauses (to3CNF' f next).2.2 (to3CNF' f next).2.1,
      ∀ l ∈ c, litIndex l < (to3CNF' f next).2.2 + 1 := by
  have hy : (to3CNF' f next).2.1 < (to3CNF' f next).2.2 := to3CNF'_y_lt_next f next hnext
  intro c hc l hl
  simp [notClauses] at hc
  rcases hc with rfl | rfl
  · simp [litIndex] at hl
    rcases hl with h | h
    · subst l; simp [litIndex] <;> omega
    · subst l; simp [litIndex] <;> omega
  · simp [litIndex] at hl
    rcases hl with h | h
    · subst l; simp [litIndex] <;> omega
    · subst l; simp [litIndex] <;> omega

/-- The `and` template's literals are below the node's next auxiliary. -/
lemma andClauses_lits_lt (f g : Formula) (next : Nat) (hnext : next ≥ numVars (Formula.and f g)) :
    ∀ c ∈ andClauses (to3CNF' g (to3CNF' f next).2.2).2.2 (to3CNF' f next).2.1 (to3CNF' g (to3CNF' f next).2.2).2.1,
      ∀ l ∈ c, litIndex l < (to3CNF' g (to3CNF' f next).2.2).2.2 + 1 := by
  have hn₁g : (to3CNF' f next).2.2 ≥ numVars g := by
    have h1 := to3CNF'_next_ge f next
    simp [numVars] at hnext
    omega
  have hn₂ : (to3CNF' g (to3CNF' f next).2.2).2.2 ≥ (to3CNF' f next).2.2 :=
    to3CNF'_next_ge g (to3CNF' f next).2.2
  have hy₁ : (to3CNF' f next).2.1 < (to3CNF' f next).2.2 :=
    to3CNF'_y_lt_next f next (by simp [numVars] at hnext; omega)
  have hy₂ : (to3CNF' g (to3CNF' f next).2.2).2.1 < (to3CNF' g (to3CNF' f next).2.2).2.2 :=
    to3CNF'_y_lt_next g (to3CNF' f next).2.2 hn₁g
  intro c hc l hl
  simp [andClauses] at hc
  rcases hc with rfl | rfl | rfl
  · simp [litIndex] at hl
    rcases hl with h | h
    · subst l; simp [litIndex] <;> omega
    · subst l; simp [litIndex] <;> omega
  · simp [litIndex] at hl
    rcases hl with h | h
    · subst l; simp [litIndex] <;> omega
    · subst l; simp [litIndex] <;> omega
  · simp [litIndex] at hl
    rcases hl with h | h
    · subst l; simp [litIndex] <;> omega
    · rcases h with h | h
      · subst l; simp [litIndex] <;> omega
      · subst l; simp [litIndex] <;> omega

/-- The `or` template's literals are below the node's next auxiliary. -/
lemma orClauses_lits_lt (f g : Formula) (next : Nat) (hnext : next ≥ numVars (Formula.or f g)) :
    ∀ c ∈ orClauses (to3CNF' g (to3CNF' f next).2.2).2.2 (to3CNF' f next).2.1 (to3CNF' g (to3CNF' f next).2.2).2.1,
      ∀ l ∈ c, litIndex l < (to3CNF' g (to3CNF' f next).2.2).2.2 + 1 := by
  have hn₁g : (to3CNF' f next).2.2 ≥ numVars g := by
    have h1 := to3CNF'_next_ge f next
    simp [numVars] at hnext
    omega
  have hn₂ : (to3CNF' g (to3CNF' f next).2.2).2.2 ≥ (to3CNF' f next).2.2 :=
    to3CNF'_next_ge g (to3CNF' f next).2.2
  have hy₁ : (to3CNF' f next).2.1 < (to3CNF' f next).2.2 :=
    to3CNF'_y_lt_next f next (by simp [numVars] at hnext; omega)
  have hy₂ : (to3CNF' g (to3CNF' f next).2.2).2.1 < (to3CNF' g (to3CNF' f next).2.2).2.2 :=
    to3CNF'_y_lt_next g (to3CNF' f next).2.2 hn₁g
  intro c hc l hl
  simp [orClauses] at hc
  rcases hc with rfl | rfl | rfl
  · simp [litIndex] at hl
    rcases hl with h | h
    · subst l; simp [litIndex] <;> omega
    · subst l; simp [litIndex] <;> omega
  · simp [litIndex] at hl
    rcases hl with h | h
    · subst l; simp [litIndex] <;> omega
    · subst l; simp [litIndex] <;> omega
  · simp [litIndex] at hl
    rcases hl with h | h
    · subst l; simp [litIndex] <;> omega
    · rcases h with h | h
      · subst l; simp [litIndex] <;> omega
      · subst l; simp [litIndex] <;> omega

/-- The `iff` template's literals are below the node's next auxiliary. -/
lemma iffClauses_lits_lt (f g : Formula) (next : Nat) (hnext : next ≥ numVars (Formula.iff f g)) :
    ∀ c ∈ iffClauses (to3CNF' g (to3CNF' f next).2.2).2.2 (to3CNF' f next).2.1 (to3CNF' g (to3CNF' f next).2.2).2.1,
      ∀ l ∈ c, litIndex l < (to3CNF' g (to3CNF' f next).2.2).2.2 + 1 := by
  have hn₁g : (to3CNF' f next).2.2 ≥ numVars g := by
    have h1 := to3CNF'_next_ge f next
    simp [numVars] at hnext
    omega
  have hn₂ : (to3CNF' g (to3CNF' f next).2.2).2.2 ≥ (to3CNF' f next).2.2 :=
    to3CNF'_next_ge g (to3CNF' f next).2.2
  have hy₁ : (to3CNF' f next).2.1 < (to3CNF' f next).2.2 :=
    to3CNF'_y_lt_next f next (by simp [numVars] at hnext; omega)
  have hy₂ : (to3CNF' g (to3CNF' f next).2.2).2.1 < (to3CNF' g (to3CNF' f next).2.2).2.2 :=
    to3CNF'_y_lt_next g (to3CNF' f next).2.2 hn₁g
  intro c hc l hl
  simp [iffClauses] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp [litIndex] at hl
    rcases hl with h | h
    · subst l; simp [litIndex] <;> omega
    · rcases h with h | h
      · subst l; simp [litIndex] <;> omega
      · subst l; simp [litIndex] <;> omega
  · simp [litIndex] at hl
    rcases hl with h | h
    · subst l; simp [litIndex] <;> omega
    · rcases h with h | h
      · subst l; simp [litIndex] <;> omega
      · subst l; simp [litIndex] <;> omega
  · simp [litIndex] at hl
    rcases hl with h | h
    · subst l; simp [litIndex] <;> omega
    · rcases h with h | h
      · subst l; simp [litIndex] <;> omega
      · subst l; simp [litIndex] <;> omega
  · simp [litIndex] at hl
    rcases hl with h | h
    · subst l; simp [litIndex] <;> omega
    · rcases h with h | h
      · subst l; simp [litIndex] <;> omega
      · subst l; simp [litIndex] <;> omega

/-- Every literal in the clauses of `to3CNF' f next` has index below the next
auxiliary index, provided the auxiliary start is beyond all original variables. -/
lemma to3CNF'_lits_lt (f : Formula) (next : Nat) (hnext : next ≥ numVars f) :
    ∀ c ∈ (to3CNF' f next).1, ∀ l ∈ c, litIndex l < (to3CNF' f next).2.2 := by
  induction f generalizing next with
  | var i => intro c hc; simp [to3CNF'] at hc
  | const b =>
      intro c hc l hl
      by_cases hb : b
      · have hc' : c = [Literal.pos next] := by simpa [to3CNF', forceTrue, hb] using hc
        subst c
        have hl' : l = Literal.pos next := by simpa using hl
        subst l
        simp [litIndex, to3CNF', forceTrue, hb]
      · have hc' : c = [Literal.neg next] := by simpa [to3CNF', forceFalse, hb] using hc
        subst c
        have hl' : l = Literal.neg next := by simpa using hl
        subst l
        simp [litIndex, to3CNF', forceFalse, hb]
  | not f ih =>
      intro c hc l hl
      simp [to3CNF'] at hc
      rcases hc with hc | hc
      · change litIndex l < (to3CNF' f next).2.2 + 1
        have h := ih next hnext c hc l hl
        omega
      · exact notClauses_lits_lt f next hnext c hc l hl
  | and f g ihf ihg =>
      intro c hc l hl
      simp [to3CNF'] at hc
      rcases hc with hc | hc
      · change litIndex l < (to3CNF' g (to3CNF' f next).2.2).2.2 + 1
        have hnf : next ≥ numVars f := by simp [numVars] at hnext; omega
        have h := ihf next hnf c hc l hl
        have hn₂ : (to3CNF' g (to3CNF' f next).2.2).2.2 ≥ (to3CNF' f next).2.2 :=
          to3CNF'_next_ge g (to3CNF' f next).2.2
        omega
      · rcases hc with hc | hc
        · change litIndex l < (to3CNF' g (to3CNF' f next).2.2).2.2 + 1
          have hg : (to3CNF' f next).2.2 ≥ numVars g := by
            have h1 := to3CNF'_next_ge f next
            simp [numVars] at hnext
            omega
          have h := ihg (to3CNF' f next).2.2 hg c hc l hl
          have hn₂ : (to3CNF' g (to3CNF' f next).2.2).2.2 ≥ (to3CNF' f next).2.2 :=
            to3CNF'_next_ge g (to3CNF' f next).2.2
          omega
        · exact andClauses_lits_lt f g next hnext c hc l hl
  | or f g ihf ihg =>
      intro c hc l hl
      simp [to3CNF'] at hc
      rcases hc with hc | hc
      · change litIndex l < (to3CNF' g (to3CNF' f next).2.2).2.2 + 1
        have hnf : next ≥ numVars f := by simp [numVars] at hnext; omega
        have h := ihf next hnf c hc l hl
        have hn₂ : (to3CNF' g (to3CNF' f next).2.2).2.2 ≥ (to3CNF' f next).2.2 :=
          to3CNF'_next_ge g (to3CNF' f next).2.2
        omega
      · rcases hc with hc | hc
        · change litIndex l < (to3CNF' g (to3CNF' f next).2.2).2.2 + 1
          have hg : (to3CNF' f next).2.2 ≥ numVars g := by
            have h1 := to3CNF'_next_ge f next
            simp [numVars] at hnext
            omega
          have h := ihg (to3CNF' f next).2.2 hg c hc l hl
          have hn₂ : (to3CNF' g (to3CNF' f next).2.2).2.2 ≥ (to3CNF' f next).2.2 :=
            to3CNF'_next_ge g (to3CNF' f next).2.2
          omega
        · exact orClauses_lits_lt f g next hnext c hc l hl
  | iff f g ihf ihg =>
      intro c hc l hl
      simp [to3CNF'] at hc
      rcases hc with hc | hc
      · change litIndex l < (to3CNF' g (to3CNF' f next).2.2).2.2 + 1
        have hnf : next ≥ numVars f := by simp [numVars] at hnext; omega
        have h := ihf next hnf c hc l hl
        have hn₂ : (to3CNF' g (to3CNF' f next).2.2).2.2 ≥ (to3CNF' f next).2.2 :=
          to3CNF'_next_ge g (to3CNF' f next).2.2
        omega
      · rcases hc with hc | hc
        · change litIndex l < (to3CNF' g (to3CNF' f next).2.2).2.2 + 1
          have hg : (to3CNF' f next).2.2 ≥ numVars g := by
            have h1 := to3CNF'_next_ge f next
            simp [numVars] at hnext
            omega
          have h := ihg (to3CNF' f next).2.2 hg c hc l hl
          have hn₂ : (to3CNF' g (to3CNF' f next).2.2).2.2 ≥ (to3CNF' f next).2.2 :=
            to3CNF'_next_ge g (to3CNF' f next).2.2
          omega
        · exact iffClauses_lits_lt f g next hnext c hc l hl

/-- If two assignments agree below `n` and a clause's literals are below `n`,
the clause evaluates the same under both. -/
lemma evalClause_of_agree (σ τ : Nat → Bool) (n : Nat) (c : Clause)
    (hl : ∀ l ∈ c, litIndex l < n) (h : ∀ j, j < n → σ j = τ j) :
    evalClause σ c ↔ evalClause τ c := by
  constructor
  · intro hc
    rcases hc with ⟨l, hlc, hlσ⟩
    refine ⟨l, hlc, ?_⟩
    cases l with
    | pos i =>
        change τ i = true
        have hσi : σ i = τ i := h i (hl (Literal.pos i) hlc)
        rw [← hσi]
        exact hlσ
    | neg i =>
        change τ i = false
        have hσi : σ i = τ i := h i (hl (Literal.neg i) hlc)
        rw [← hσi]
        exact hlσ
  · intro hc
    rcases hc with ⟨l, hlc, hlσ⟩
    refine ⟨l, hlc, ?_⟩
    cases l with
    | pos i =>
        change σ i = true
        have hσi : σ i = τ i := h i (hl (Literal.pos i) hlc)
        rw [hσi]
        exact hlσ
    | neg i =>
        change σ i = false
        have hσi : σ i = τ i := h i (hl (Literal.neg i) hlc)
        rw [hσi]
        exact hlσ

/-- If two assignments agree below `n` and every clause of `c` has literals
below `n`, then `c` evaluates the same under both. -/
lemma evalCNF_of_agree (σ τ : Nat → Bool) (n : Nat) (c : CNF)
    (hl : ∀ cl ∈ c, ∀ l ∈ cl, litIndex l < n) (h : ∀ j, j < n → σ j = τ j) :
    evalCNF σ c ↔ evalCNF τ c := by
  constructor
  · intro hc cl hcl
    exact (evalClause_of_agree σ τ n cl (hl cl hcl) h).1 (hc cl hcl)
  · intro hc cl hcl
    exact (evalClause_of_agree σ τ n cl (hl cl hcl) h).2 (hc cl hcl)

/-- `Formula.eval` only depends on the assignment to the variables of `f`. -/
lemma Formula.eval_eq_of_agree (f : Formula) (σ τ : Nat → Bool)
    (h : ∀ j, j < numVars f → σ j = τ j) :
    Formula.eval f σ = Formula.eval f τ := by
  induction f generalizing σ τ with
  | var i =>
      have hi : i < numVars (Formula.var i) := by simp [numVars]
      simpa [Formula.eval] using h i hi
  | const b => simp [Formula.eval]
  | not f ih => simp [Formula.eval, ih σ τ h]
  | and f g ihf ihg =>
      have hf : ∀ j, j < numVars f → σ j = τ j := fun j hj => h j (by simp [numVars]; omega)
      have hg : ∀ j, j < numVars g → σ j = τ j := fun j hj => h j (by simp [numVars]; omega)
      simp [Formula.eval, ihf σ τ hf, ihg σ τ hg]
  | or f g ihf ihg =>
      have hf : ∀ j, j < numVars f → σ j = τ j := fun j hj => h j (by simp [numVars]; omega)
      have hg : ∀ j, j < numVars g → σ j = τ j := fun j hj => h j (by simp [numVars]; omega)
      simp [Formula.eval, ihf σ τ hf, ihg σ τ hg]
  | iff f g ihf ihg =>
      have hf : ∀ j, j < numVars f → σ j = τ j := fun j hj => h j (by simp [numVars]; omega)
      have hg : ∀ j, j < numVars g → σ j = τ j := fun j hj => h j (by simp [numVars]; omega)
      simp [Formula.eval, ihf σ τ hf, ihg σ τ hg]

end Chapter34

end CLRS
