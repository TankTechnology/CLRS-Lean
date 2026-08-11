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
  `Formula.Satisfiable φ`, plus the input-length variant
  `cnfSatisfiable_to3CNF_len_iff` used by the machine.

**Current status**: semantic model, reduction, the satisfiability
preservation theorem (`cnfSatisfiable_to3CNF_iff`), and the list encoding
(`CNFSym`, `encCNF`, `decodeCNF`, `decodeCNF_encCNF`, and the language
`ThreeCNFSat`) are in place.  The reduction machine and its `outputsFun`
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

/-- The boolean version of `evalLit`, used where a decision (e.g. an `if`)
is needed.  `evalLitBool σ l = true` iff `evalLit σ l`. -/
def evalLitBool (σ : Nat → Bool) : Literal → Bool
  | Literal.pos i => σ i
  | Literal.neg i => !(σ i)

@[simp] lemma evalLitBool_eq_true (σ : Nat → Bool) (l : Literal) :
    evalLitBool σ l = true ↔ evalLit σ l := by
  cases l <;> simp [evalLitBool, evalLit]

@[simp] lemma evalLitBool_eq_false (σ : Nat → Bool) (l : Literal) :
    evalLitBool σ l = false ↔ ¬ evalLit σ l := by
  cases l <;> simp [evalLitBool, evalLit]

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

-- ============================================================
-- Satisfiability preservation of the Tseitin encoding
-- ============================================================

/-- `a = true ↔ (b = true ∧ c = true)` means `a` is the AND of `b`, `c`. -/
lemma eq_true_iff_and {a b c : Bool} : (a = true ↔ b = true ∧ c = true) ↔ a = (b && c) := by
  revert a b c
  decide

/-- `a = true ↔ (b = true ∨ c = true)` means `a` is the OR of `b`, `c`. -/
lemma eq_true_iff_or {a b c : Bool} : (a = true ↔ b = true ∨ c = true) ↔ a = (b || c) := by
  revert a b c
  decide

/-- `a = true ↔ b = false` means `a` is the negation of `b`. -/
lemma eq_true_iff_not {a b : Bool} : (a = true ↔ b = false) ↔ a = !b := by
  revert a b
  decide

/-- `a = true ↔ (b = true ↔ c = true)` means `a` is the equality of `b`, `c`. -/
lemma eq_true_iff_iff {a b c : Bool} : (a = true ↔ (b = true ↔ c = true)) ↔ a = (b == c) := by
  revert a b c
  decide

/-- `extend (not f)` agrees with `extend f` below `f`'s final auxiliary index. -/
lemma extend_not_agree_lt (f : Formula) (next : Nat) (σ : Nat → Bool) :
    ∀ j, j < (to3CNF' f next).2.2 →
      extend (Formula.not f) next σ j = extend f next σ j := by
  intro j hj
  by_cases hne : j = (to3CNF' f next).2.2
  · exfalso
    omega
  · simp [extend, hne]

/-- `extend (and f g)` agrees with `extend f` below `f`'s final auxiliary index. -/
lemma extend_and_agree_f_lt (f g : Formula) (next : Nat) (σ : Nat → Bool) :
    ∀ j, j < (to3CNF' f next).2.2 →
      extend (Formula.and f g) next σ j = extend f next σ j := by
  intro j hj
  by_cases hne : j = (to3CNF' g (to3CNF' f next).2.2).2.2
  · exfalso
    have hg := to3CNF'_next_ge g (to3CNF' f next).2.2
    omega
  · simp [extend, hne]
    exact extend_agree_lt g (to3CNF' f next).2.2 (extend f next σ) j hj

/-- `extend (and f g)` agrees with `extend g (extend f)` below `g`'s final index. -/
lemma extend_and_agree_g_lt (f g : Formula) (next : Nat) (σ : Nat → Bool) :
    ∀ j, j < (to3CNF' g (to3CNF' f next).2.2).2.2 →
      extend (Formula.and f g) next σ j = extend g (to3CNF' f next).2.2 (extend f next σ) j := by
  intro j hj
  by_cases hne : j = (to3CNF' g (to3CNF' f next).2.2).2.2
  · exfalso
    omega
  · simp [extend, hne]

/-- `extend (or f g)` agrees with `extend f` below `f`'s final auxiliary index. -/
lemma extend_or_agree_f_lt (f g : Formula) (next : Nat) (σ : Nat → Bool) :
    ∀ j, j < (to3CNF' f next).2.2 →
      extend (Formula.or f g) next σ j = extend f next σ j := by
  intro j hj
  by_cases hne : j = (to3CNF' g (to3CNF' f next).2.2).2.2
  · exfalso
    have hg := to3CNF'_next_ge g (to3CNF' f next).2.2
    omega
  · simp [extend, hne]
    exact extend_agree_lt g (to3CNF' f next).2.2 (extend f next σ) j hj

/-- `extend (or f g)` agrees with `extend g (extend f)` below `g`'s final index. -/
lemma extend_or_agree_g_lt (f g : Formula) (next : Nat) (σ : Nat → Bool) :
    ∀ j, j < (to3CNF' g (to3CNF' f next).2.2).2.2 →
      extend (Formula.or f g) next σ j = extend g (to3CNF' f next).2.2 (extend f next σ) j := by
  intro j hj
  by_cases hne : j = (to3CNF' g (to3CNF' f next).2.2).2.2
  · exfalso
    omega
  · simp [extend, hne]

/-- `extend (iff f g)` agrees with `extend f` below `f`'s final auxiliary index. -/
lemma extend_iff_agree_f_lt (f g : Formula) (next : Nat) (σ : Nat → Bool) :
    ∀ j, j < (to3CNF' f next).2.2 →
      extend (Formula.iff f g) next σ j = extend f next σ j := by
  intro j hj
  by_cases hne : j = (to3CNF' g (to3CNF' f next).2.2).2.2
  · exfalso
    have hg := to3CNF'_next_ge g (to3CNF' f next).2.2
    omega
  · simp [extend, hne]
    exact extend_agree_lt g (to3CNF' f next).2.2 (extend f next σ) j hj

/-- `extend (iff f g)` agrees with `extend g (extend f)` below `g`'s final index. -/
lemma extend_iff_agree_g_lt (f g : Formula) (next : Nat) (σ : Nat → Bool) :
    ∀ j, j < (to3CNF' g (to3CNF' f next).2.2).2.2 →
      extend (Formula.iff f g) next σ j = extend g (to3CNF' f next).2.2 (extend f next σ) j := by
  intro j hj
  by_cases hne : j = (to3CNF' g (to3CNF' f next).2.2).2.2
  · exfalso
    omega
  · simp [extend, hne]

/-- The extension forces each node's value variable to the value of its subformula. -/
lemma extend_valueVar (f : Formula) (next : Nat) (σ : Nat → Bool) (hnext : next ≥ numVars f) :
    extend f next σ (to3CNF' f next).2.1 = Formula.eval f σ := by
  induction f generalizing next σ with
  | var i => simp [extend, to3CNF', Formula.eval]
  | const b =>
      by_cases hb : b <;> simp [extend, to3CNF', Formula.eval, hb]
  | not f ih =>
      simp [extend, to3CNF', Formula.eval]
      rw [ih next σ hnext]
  | and f g ihf ihg =>
      have hfnext : next ≥ numVars f := by
        simp [numVars] at hnext
        omega
      have hfnext : next ≥ numVars f := by
        simp [numVars] at hnext
        omega
      have hgnext : (to3CNF' f next).2.2 ≥ numVars g := by
        have h1 := to3CNF'_next_ge f next
        simp [numVars] at hnext
        omega
      have hg : Formula.eval g (extend f next σ) = Formula.eval g σ := by
        apply Formula.eval_eq_of_agree
        intro j hj
        exact extend_agree_lt f next σ j (by
          have hng : next ≥ numVars g := by
            simp [numVars] at hnext
            omega
          omega)
      simp [extend, to3CNF', Formula.eval]
      rw [ihf next σ hfnext]
      rw [ihg (to3CNF' f next).2.2 (extend f next σ) hgnext]
      rw [hg]
  | or f g ihf ihg =>
      have hfnext : next ≥ numVars f := by
        simp [numVars] at hnext
        omega
      have hgnext : (to3CNF' f next).2.2 ≥ numVars g := by
        have h1 := to3CNF'_next_ge f next
        simp [numVars] at hnext
        omega
      have hg : Formula.eval g (extend f next σ) = Formula.eval g σ := by
        apply Formula.eval_eq_of_agree
        intro j hj
        exact extend_agree_lt f next σ j (by
          have hng : next ≥ numVars g := by
            simp [numVars] at hnext
            omega
          omega)
      simp [extend, to3CNF', Formula.eval]
      rw [ihf next σ hfnext]
      rw [ihg (to3CNF' f next).2.2 (extend f next σ) hgnext]
      rw [hg]
  | iff f g ihf ihg =>
      have hfnext : next ≥ numVars f := by
        simp [numVars] at hnext
        omega
      have hgnext : (to3CNF' f next).2.2 ≥ numVars g := by
        have h1 := to3CNF'_next_ge f next
        simp [numVars] at hnext
        omega
      have hg : Formula.eval g (extend f next σ) = Formula.eval g σ := by
        apply Formula.eval_eq_of_agree
        intro j hj
        exact extend_agree_lt f next σ j (by
          have hng : next ≥ numVars g := by
            simp [numVars] at hnext
            omega
          omega)
      simp [extend, to3CNF', Formula.eval]
      rw [ihf next σ hfnext]
      rw [ihg (to3CNF' f next).2.2 (extend f next σ) hgnext]
      rw [hg]

/-- The clauses of a subformula all hold under the extended assignment. -/
lemma evalCNF_extend (f : Formula) (next : Nat) (σ : Nat → Bool) (hnext : next ≥ numVars f) :
    evalCNF (extend f next σ) (to3CNF' f next).1 := by
  induction f generalizing next σ with
  | var i => simp [to3CNF', evalCNF]
  | const b =>
      by_cases hb : b
      · have h : extend (Formula.const true) next σ next = true := by simp [extend]
        simpa [to3CNF', hb] using (evalCNF_forceTrue (extend (Formula.const true) next σ) next).2 h
      · have h : extend (Formula.const false) next σ next = false := by simp [extend]
        simpa [to3CNF', hb] using (evalCNF_forceFalse (extend (Formula.const false) next σ) next).2 h
  | not f ih =>
      have hfnext : next ≥ numVars f := by simpa [numVars] using hnext
      have h1 : evalCNF (extend (Formula.not f) next σ) (to3CNF' f next).1 := by
        have h := evalCNF_of_agree (extend f next σ) (extend (Formula.not f) next σ)
          (to3CNF' f next).2.2 (to3CNF' f next).1 (to3CNF'_lits_lt f next hfnext)
          (fun j hj => (extend_not_agree_lt f next σ j hj).symm)
        exact h.1 (ih next σ hfnext)
      have h2 : evalCNF (extend (Formula.not f) next σ) (notClauses (to3CNF' f next).2.2 (to3CNF' f next).2.1) := by
        have hy : extend (Formula.not f) next σ (to3CNF' f next).2.1 = extend f next σ (to3CNF' f next).2.1 :=
          extend_not_agree_lt f next σ (to3CNF' f next).2.1 (to3CNF'_y_lt_next f next hfnext)
        rw [evalCNF_notClauses]
        have hne : extend (Formula.not f) next σ (to3CNF' f next).2.2 = !(extend f next σ (to3CNF' f next).2.1) := by
          simp [extend]
        rw [hne, hy]
        simp
      simpa [to3CNF'] using (evalCNF_append (extend (Formula.not f) next σ)
        (to3CNF' f next).1 (notClauses (to3CNF' f next).2.2 (to3CNF' f next).2.1)).2 ⟨h1, h2⟩
  | and f g ihf ihg =>
      have hfnext : next ≥ numVars f := by simp [numVars] at hnext; omega
      have hgnext₁ : (to3CNF' f next).2.2 ≥ numVars g := by
        have h1 := to3CNF'_next_ge f next
        simp [numVars] at hnext
        omega
      have h1 : evalCNF (extend (Formula.and f g) next σ) (to3CNF' f next).1 := by
        have h := evalCNF_of_agree (extend f next σ) (extend (Formula.and f g) next σ)
          (to3CNF' f next).2.2 (to3CNF' f next).1 (to3CNF'_lits_lt f next hfnext)
          (fun j hj => (extend_and_agree_f_lt f g next σ j hj).symm)
        exact h.1 (ihf next σ hfnext)
      have h2 : evalCNF (extend (Formula.and f g) next σ) (to3CNF' g (to3CNF' f next).2.2).1 := by
        have h := evalCNF_of_agree (extend g (to3CNF' f next).2.2 (extend f next σ))
          (extend (Formula.and f g) next σ)
          (to3CNF' g (to3CNF' f next).2.2).2.2 (to3CNF' g (to3CNF' f next).2.2).1
          (to3CNF'_lits_lt g (to3CNF' f next).2.2 hgnext₁)
          (fun j hj => (extend_and_agree_g_lt f g next σ j hj).symm)
        exact h.1 (ihg (to3CNF' f next).2.2 (extend f next σ) hgnext₁)
      have h3 : evalCNF (extend (Formula.and f g) next σ)
          (andClauses (to3CNF' g (to3CNF' f next).2.2).2.2
            (to3CNF' f next).2.1 (to3CNF' g (to3CNF' f next).2.2).2.1) := by
        rw [evalCNF_andClauses]
        have hne : extend (Formula.and f g) next σ (to3CNF' g (to3CNF' f next).2.2).2.2 =
            (extend f next σ (to3CNF' f next).2.1 &&
              extend g (to3CNF' f next).2.2 (extend f next σ) (to3CNF' g (to3CNF' f next).2.2).2.1) := by
          simp [extend]
        have hy₁ : extend (Formula.and f g) next σ (to3CNF' f next).2.1 = extend f next σ (to3CNF' f next).2.1 :=
          extend_and_agree_f_lt f g next σ (to3CNF' f next).2.1 (to3CNF'_y_lt_next f next hfnext)
        have hy₂ : extend (Formula.and f g) next σ (to3CNF' g (to3CNF' f next).2.2).2.1 =
            extend g (to3CNF' f next).2.2 (extend f next σ) (to3CNF' g (to3CNF' f next).2.2).2.1 :=
          extend_and_agree_g_lt f g next σ (to3CNF' g (to3CNF' f next).2.2).2.1
            (to3CNF'_y_lt_next g (to3CNF' f next).2.2 hgnext₁)
        rw [hne, hy₁, hy₂]
        simpa
      simpa [to3CNF'] using (evalCNF_append (extend (Formula.and f g) next σ)
        ((to3CNF' f next).1 ++ (to3CNF' g (to3CNF' f next).2.2).1)
        (andClauses (to3CNF' g (to3CNF' f next).2.2).2.2
          (to3CNF' f next).2.1 (to3CNF' g (to3CNF' f next).2.2).2.1)).2
        ⟨(evalCNF_append (extend (Formula.and f g) next σ)
          (to3CNF' f next).1 (to3CNF' g (to3CNF' f next).2.2).1).2 ⟨h1, h2⟩, h3⟩
  | or f g ihf ihg =>
      have hfnext : next ≥ numVars f := by simp [numVars] at hnext; omega
      have hgnext₁ : (to3CNF' f next).2.2 ≥ numVars g := by
        have h1 := to3CNF'_next_ge f next
        simp [numVars] at hnext
        omega
      have h1 : evalCNF (extend (Formula.or f g) next σ) (to3CNF' f next).1 := by
        have h := evalCNF_of_agree (extend f next σ) (extend (Formula.or f g) next σ)
          (to3CNF' f next).2.2 (to3CNF' f next).1 (to3CNF'_lits_lt f next hfnext)
          (fun j hj => (extend_or_agree_f_lt f g next σ j hj).symm)
        exact h.1 (ihf next σ hfnext)
      have h2 : evalCNF (extend (Formula.or f g) next σ) (to3CNF' g (to3CNF' f next).2.2).1 := by
        have h := evalCNF_of_agree (extend g (to3CNF' f next).2.2 (extend f next σ))
          (extend (Formula.or f g) next σ)
          (to3CNF' g (to3CNF' f next).2.2).2.2 (to3CNF' g (to3CNF' f next).2.2).1
          (to3CNF'_lits_lt g (to3CNF' f next).2.2 hgnext₁)
          (fun j hj => (extend_or_agree_g_lt f g next σ j hj).symm)
        exact h.1 (ihg (to3CNF' f next).2.2 (extend f next σ) hgnext₁)
      have h3 : evalCNF (extend (Formula.or f g) next σ)
          (orClauses (to3CNF' g (to3CNF' f next).2.2).2.2
            (to3CNF' f next).2.1 (to3CNF' g (to3CNF' f next).2.2).2.1) := by
        rw [evalCNF_orClauses]
        have hne : extend (Formula.or f g) next σ (to3CNF' g (to3CNF' f next).2.2).2.2 =
            (extend f next σ (to3CNF' f next).2.1 ||
              extend g (to3CNF' f next).2.2 (extend f next σ) (to3CNF' g (to3CNF' f next).2.2).2.1) := by
          simp [extend]
        have hy₁ : extend (Formula.or f g) next σ (to3CNF' f next).2.1 = extend f next σ (to3CNF' f next).2.1 :=
          extend_or_agree_f_lt f g next σ (to3CNF' f next).2.1 (to3CNF'_y_lt_next f next hfnext)
        have hy₂ : extend (Formula.or f g) next σ (to3CNF' g (to3CNF' f next).2.2).2.1 =
            extend g (to3CNF' f next).2.2 (extend f next σ) (to3CNF' g (to3CNF' f next).2.2).2.1 :=
          extend_or_agree_g_lt f g next σ (to3CNF' g (to3CNF' f next).2.2).2.1
            (to3CNF'_y_lt_next g (to3CNF' f next).2.2 hgnext₁)
        rw [hne, hy₁, hy₂]
        simpa
      simpa [to3CNF'] using (evalCNF_append (extend (Formula.or f g) next σ)
        ((to3CNF' f next).1 ++ (to3CNF' g (to3CNF' f next).2.2).1)
        (orClauses (to3CNF' g (to3CNF' f next).2.2).2.2
          (to3CNF' f next).2.1 (to3CNF' g (to3CNF' f next).2.2).2.1)).2
        ⟨(evalCNF_append (extend (Formula.or f g) next σ)
          (to3CNF' f next).1 (to3CNF' g (to3CNF' f next).2.2).1).2 ⟨h1, h2⟩, h3⟩
  | iff f g ihf ihg =>
      have hfnext : next ≥ numVars f := by simp [numVars] at hnext; omega
      have hgnext₁ : (to3CNF' f next).2.2 ≥ numVars g := by
        have h1 := to3CNF'_next_ge f next
        simp [numVars] at hnext
        omega
      have h1 : evalCNF (extend (Formula.iff f g) next σ) (to3CNF' f next).1 := by
        have h := evalCNF_of_agree (extend f next σ) (extend (Formula.iff f g) next σ)
          (to3CNF' f next).2.2 (to3CNF' f next).1 (to3CNF'_lits_lt f next hfnext)
          (fun j hj => (extend_iff_agree_f_lt f g next σ j hj).symm)
        exact h.1 (ihf next σ hfnext)
      have h2 : evalCNF (extend (Formula.iff f g) next σ) (to3CNF' g (to3CNF' f next).2.2).1 := by
        have h := evalCNF_of_agree (extend g (to3CNF' f next).2.2 (extend f next σ))
          (extend (Formula.iff f g) next σ)
          (to3CNF' g (to3CNF' f next).2.2).2.2 (to3CNF' g (to3CNF' f next).2.2).1
          (to3CNF'_lits_lt g (to3CNF' f next).2.2 hgnext₁)
          (fun j hj => (extend_iff_agree_g_lt f g next σ j hj).symm)
        exact h.1 (ihg (to3CNF' f next).2.2 (extend f next σ) hgnext₁)
      have h3 : evalCNF (extend (Formula.iff f g) next σ)
          (iffClauses (to3CNF' g (to3CNF' f next).2.2).2.2
            (to3CNF' f next).2.1 (to3CNF' g (to3CNF' f next).2.2).2.1) := by
        rw [evalCNF_iffClauses]
        have hne : extend (Formula.iff f g) next σ (to3CNF' g (to3CNF' f next).2.2).2.2 =
            (extend f next σ (to3CNF' f next).2.1 ==
              extend g (to3CNF' f next).2.2 (extend f next σ) (to3CNF' g (to3CNF' f next).2.2).2.1) := by
          simp [extend]
        have hy₁ : extend (Formula.iff f g) next σ (to3CNF' f next).2.1 = extend f next σ (to3CNF' f next).2.1 :=
          extend_iff_agree_f_lt f g next σ (to3CNF' f next).2.1 (to3CNF'_y_lt_next f next hfnext)
        have hy₂ : extend (Formula.iff f g) next σ (to3CNF' g (to3CNF' f next).2.2).2.1 =
            extend g (to3CNF' f next).2.2 (extend f next σ) (to3CNF' g (to3CNF' f next).2.2).2.1 :=
          extend_iff_agree_g_lt f g next σ (to3CNF' g (to3CNF' f next).2.2).2.1
            (to3CNF'_y_lt_next g (to3CNF' f next).2.2 hgnext₁)
        rw [hne, hy₁, hy₂]
        simp
      simpa [to3CNF'] using (evalCNF_append (extend (Formula.iff f g) next σ)
        ((to3CNF' f next).1 ++ (to3CNF' g (to3CNF' f next).2.2).1)
        (iffClauses (to3CNF' g (to3CNF' f next).2.2).2.2
          (to3CNF' f next).2.1 (to3CNF' g (to3CNF' f next).2.2).2.1)).2
        ⟨(evalCNF_append (extend (Formula.iff f g) next σ)
          (to3CNF' f next).1 (to3CNF' g (to3CNF' f next).2.2).1).2 ⟨h1, h2⟩, h3⟩

/-- Evaluating `f` under a restriction to `m ≥ numVars f` agrees with the
restriction to `numVars f`. -/
lemma eval_restrict_eq_of_le (f : Formula) {m : Nat} (σ : Nat → Bool) (hm : numVars f ≤ m) :
    Formula.eval f (fun j => if j < m then σ j else false) =
    Formula.eval f (fun j => if j < numVars f then σ j else false) := by
  apply Formula.eval_eq_of_agree
  intro j hj
  have hj' : j < m := by omega
  rw [if_pos hj']
  rw [if_pos hj]

/-- If the clauses of a subformula hold under `σ`, then `σ` gives the value
variable the value of the subformula (with the original variables read off `σ`). -/
lemma valueVar_of_clauses (f : Formula) (next : Nat) (σ : Nat → Bool) (hnext : next ≥ numVars f)
    (hclauses : evalCNF σ (to3CNF' f next).1) :
    σ (to3CNF' f next).2.1 = Formula.eval f (fun j => if j < numVars f then σ j else false) := by
  induction f generalizing next σ with
  | var i =>
      simp [to3CNF', Formula.eval, numVars] at hclauses ⊢
  | const b =>
      by_cases hb : b
      · have hc : evalCNF σ (forceTrue next) := by simpa [to3CNF', hb] using hclauses
        simpa [to3CNF', Formula.eval, hb] using (evalCNF_forceTrue σ next).1 hc
      · have hc : evalCNF σ (forceFalse next) := by simpa [to3CNF', hb] using hclauses
        simpa [to3CNF', Formula.eval, hb] using (evalCNF_forceFalse σ next).1 hc
  | not f ih =>
      have hfnext : next ≥ numVars f := by simpa [numVars] using hnext
      have hspl := (evalCNF_append σ (to3CNF' f next).1
        (notClauses (to3CNF' f next).2.2 (to3CNF' f next).2.1)).1 (by simpa [to3CNF'] using hclauses)
      rcases hspl with ⟨hcl1, hcl2⟩
      have hiy : σ (to3CNF' f next).2.1 = Formula.eval f (fun j => if j < numVars f then σ j else false) :=
        ih next σ hfnext hcl1
      have hne : σ (to3CNF' f next).2.2 = !(σ (to3CNF' f next).2.1) := by
        have ht := evalCNF_notClauses σ (to3CNF' f next).2.2 (to3CNF' f next).2.1
        exact (eq_true_iff_not).1 (ht.1 hcl2)
      change σ (to3CNF' f next).2.2 =
        Formula.eval (Formula.not f) (fun j => if j < numVars (Formula.not f) then σ j else false)
      rw [hne, hiy]
      simp [Formula.eval, numVars]
      rfl
  | and f g ihf ihg =>
      have hfnext : next ≥ numVars f := by simp [numVars] at hnext; omega
      have hgnext₁ : (to3CNF' f next).2.2 ≥ numVars g := by
        have h1 := to3CNF'_next_ge f next
        simp [numVars] at hnext
        omega
      have hspl := (evalCNF_append σ (to3CNF' f next).1
        ((to3CNF' g (to3CNF' f next).2.2).1 ++
          andClauses (to3CNF' g (to3CNF' f next).2.2).2.2
            (to3CNF' f next).2.1 (to3CNF' g (to3CNF' f next).2.2).2.1)).1
        (by simpa [to3CNF'] using hclauses)
      rcases hspl with ⟨hcl1, hrest⟩
      have hspl2 := (evalCNF_append σ (to3CNF' g (to3CNF' f next).2.2).1
        (andClauses (to3CNF' g (to3CNF' f next).2.2).2.2
          (to3CNF' f next).2.1 (to3CNF' g (to3CNF' f next).2.2).2.1)).1 hrest
      rcases hspl2 with ⟨hcl2, hcl3⟩
      have hiy₁ : σ (to3CNF' f next).2.1 = Formula.eval f (fun j => if j < numVars f then σ j else false) :=
        ihf next σ hfnext hcl1
      have hiy₂ : σ (to3CNF' g (to3CNF' f next).2.2).2.1 =
          Formula.eval g (fun j => if j < numVars g then σ j else false) :=
        ihg (to3CNF' f next).2.2 σ hgnext₁ hcl2
      have hne : σ (to3CNF' g (to3CNF' f next).2.2).2.2 =
          (σ (to3CNF' f next).2.1 && σ (to3CNF' g (to3CNF' f next).2.2).2.1) := by
        have ht := evalCNF_andClauses σ (to3CNF' g (to3CNF' f next).2.2).2.2
          (to3CNF' f next).2.1 (to3CNF' g (to3CNF' f next).2.2).2.1
        exact (eq_true_iff_and).1 (ht.1 hcl3)
      change σ (to3CNF' g (to3CNF' f next).2.2).2.2 =
        Formula.eval (Formula.and f g) (fun j => if j < numVars (Formula.and f g) then σ j else false)
      rw [hne, hiy₁, hiy₂]
      have hf : Formula.eval f (fun j => if j < numVars (Formula.and f g) then σ j else false) =
          Formula.eval f (fun j => if j < numVars f then σ j else false) := by
        exact eval_restrict_eq_of_le f σ (by
          change numVars f ≤ max (numVars f) (numVars g)
          exact Nat.le_max_left _ _)
      have hg : Formula.eval g (fun j => if j < numVars (Formula.and f g) then σ j else false) =
          Formula.eval g (fun j => if j < numVars g then σ j else false) := by
        exact eval_restrict_eq_of_le g σ (by
          change numVars g ≤ max (numVars f) (numVars g)
          exact Nat.le_max_right _ _)
      rw [← hf, ← hg]
      rfl
  | or f g ihf ihg =>
      have hfnext : next ≥ numVars f := by simp [numVars] at hnext; omega
      have hgnext₁ : (to3CNF' f next).2.2 ≥ numVars g := by
        have h1 := to3CNF'_next_ge f next
        simp [numVars] at hnext
        omega
      have hspl := (evalCNF_append σ (to3CNF' f next).1
        ((to3CNF' g (to3CNF' f next).2.2).1 ++
          orClauses (to3CNF' g (to3CNF' f next).2.2).2.2
            (to3CNF' f next).2.1 (to3CNF' g (to3CNF' f next).2.2).2.1)).1
        (by simpa [to3CNF'] using hclauses)
      rcases hspl with ⟨hcl1, hrest⟩
      have hspl2 := (evalCNF_append σ (to3CNF' g (to3CNF' f next).2.2).1
        (orClauses (to3CNF' g (to3CNF' f next).2.2).2.2
          (to3CNF' f next).2.1 (to3CNF' g (to3CNF' f next).2.2).2.1)).1 hrest
      rcases hspl2 with ⟨hcl2, hcl3⟩
      have hiy₁ : σ (to3CNF' f next).2.1 = Formula.eval f (fun j => if j < numVars f then σ j else false) :=
        ihf next σ hfnext hcl1
      have hiy₂ : σ (to3CNF' g (to3CNF' f next).2.2).2.1 =
          Formula.eval g (fun j => if j < numVars g then σ j else false) :=
        ihg (to3CNF' f next).2.2 σ hgnext₁ hcl2
      have hne : σ (to3CNF' g (to3CNF' f next).2.2).2.2 =
          (σ (to3CNF' f next).2.1 || σ (to3CNF' g (to3CNF' f next).2.2).2.1) := by
        have ht := evalCNF_orClauses σ (to3CNF' g (to3CNF' f next).2.2).2.2
          (to3CNF' f next).2.1 (to3CNF' g (to3CNF' f next).2.2).2.1
        exact (eq_true_iff_or).1 (ht.1 hcl3)
      change σ (to3CNF' g (to3CNF' f next).2.2).2.2 =
        Formula.eval (Formula.or f g) (fun j => if j < numVars (Formula.or f g) then σ j else false)
      rw [hne, hiy₁, hiy₂]
      have hf : Formula.eval f (fun j => if j < numVars (Formula.or f g) then σ j else false) =
          Formula.eval f (fun j => if j < numVars f then σ j else false) := by
        exact eval_restrict_eq_of_le f σ (by
          change numVars f ≤ max (numVars f) (numVars g)
          exact Nat.le_max_left _ _)
      have hg : Formula.eval g (fun j => if j < numVars (Formula.or f g) then σ j else false) =
          Formula.eval g (fun j => if j < numVars g then σ j else false) := by
        exact eval_restrict_eq_of_le g σ (by
          change numVars g ≤ max (numVars f) (numVars g)
          exact Nat.le_max_right _ _)
      rw [← hf, ← hg]
      rfl
  | iff f g ihf ihg =>
      have hfnext : next ≥ numVars f := by simp [numVars] at hnext; omega
      have hgnext₁ : (to3CNF' f next).2.2 ≥ numVars g := by
        have h1 := to3CNF'_next_ge f next
        simp [numVars] at hnext
        omega
      have hspl := (evalCNF_append σ (to3CNF' f next).1
        ((to3CNF' g (to3CNF' f next).2.2).1 ++
          iffClauses (to3CNF' g (to3CNF' f next).2.2).2.2
            (to3CNF' f next).2.1 (to3CNF' g (to3CNF' f next).2.2).2.1)).1
        (by simpa [to3CNF'] using hclauses)
      rcases hspl with ⟨hcl1, hrest⟩
      have hspl2 := (evalCNF_append σ (to3CNF' g (to3CNF' f next).2.2).1
        (iffClauses (to3CNF' g (to3CNF' f next).2.2).2.2
          (to3CNF' f next).2.1 (to3CNF' g (to3CNF' f next).2.2).2.1)).1 hrest
      rcases hspl2 with ⟨hcl2, hcl3⟩
      have hiy₁ : σ (to3CNF' f next).2.1 = Formula.eval f (fun j => if j < numVars f then σ j else false) :=
        ihf next σ hfnext hcl1
      have hiy₂ : σ (to3CNF' g (to3CNF' f next).2.2).2.1 =
          Formula.eval g (fun j => if j < numVars g then σ j else false) :=
        ihg (to3CNF' f next).2.2 σ hgnext₁ hcl2
      have hne : σ (to3CNF' g (to3CNF' f next).2.2).2.2 =
          (σ (to3CNF' f next).2.1 == σ (to3CNF' g (to3CNF' f next).2.2).2.1) := by
        have ht := evalCNF_iffClauses σ (to3CNF' g (to3CNF' f next).2.2).2.2
          (to3CNF' f next).2.1 (to3CNF' g (to3CNF' f next).2.2).2.1
        exact (eq_true_iff_iff).1 (ht.1 hcl3)
      change σ (to3CNF' g (to3CNF' f next).2.2).2.2 =
        Formula.eval (Formula.iff f g) (fun j => if j < numVars (Formula.iff f g) then σ j else false)
      rw [hne, hiy₁, hiy₂]
      have hf : Formula.eval f (fun j => if j < numVars (Formula.iff f g) then σ j else false) =
          Formula.eval f (fun j => if j < numVars f then σ j else false) := by
        exact eval_restrict_eq_of_le f σ (by
          change numVars f ≤ max (numVars f) (numVars g)
          exact Nat.le_max_left _ _)
      have hg : Formula.eval g (fun j => if j < numVars (Formula.iff f g) then σ j else false) =
          Formula.eval g (fun j => if j < numVars g then σ j else false) := by
        exact eval_restrict_eq_of_le g σ (by
          change numVars g ≤ max (numVars f) (numVars g)
          exact Nat.le_max_right _ _)
      rw [← hf, ← hg]
      rfl

/-- The Tseitin encoding of a formula is satisfiable iff the formula is
(allocating auxiliaries from `next`, provided it lies beyond the variables). -/
lemma cnfSatisfiable_to3CNF'_iff (f : Formula) (next : Nat) (hnext : next ≥ numVars f) :
    CnfSatisfiable ((to3CNF' f next).1 ++ forceTrue (to3CNF' f next).2.1) ↔ Formula.Satisfiable f := by
  constructor
  · intro h
    rcases h with ⟨σ, hσ⟩
    have hc := (evalCNF_append σ (to3CNF' f next).1 (forceTrue (to3CNF' f next).2.1)).1 hσ
    have hy : σ (to3CNF' f next).2.1 = true :=
      (evalCNF_forceTrue σ (to3CNF' f next).2.1).1 hc.2
    have heval := valueVar_of_clauses f next σ hnext hc.1
    rw [hy] at heval
    exact ⟨fun j => if j < numVars f then σ j else false, heval.symm⟩
  · intro h
    rcases h with ⟨σ, hσ⟩
    let τ := extend f next σ
    refine ⟨τ, ?_⟩
    have h1 : evalCNF τ (to3CNF' f next).1 := by
      simpa [τ] using evalCNF_extend f next σ hnext
    have hy : τ (to3CNF' f next).2.1 = true := by
      have h := extend_valueVar f next σ hnext
      simp [τ] at h ⊢
      rw [h]
      exact hσ
    have h2 : evalCNF τ (forceTrue (to3CNF' f next).2.1) :=
      (evalCNF_forceTrue τ (to3CNF' f next).2.1).2 hy
    exact (evalCNF_append τ (to3CNF' f next).1 (forceTrue (to3CNF' f next).2.1)).2 ⟨h1, h2⟩

/-- The full Tseitin reduction, allocating auxiliaries from an explicit start
`n` that lies beyond all variables of `φ`. -/
def to3CNF_len (φ : Formula) (n : Nat) : CNF :=
  let (c, y, _) := to3CNF' φ n
  c ++ forceTrue y

-- ============================================================
-- List encoding of CNF formulas
-- ============================================================

/-- The output alphabet of the reduction: clause and literal symbols. -/
inductive CNFSym : Type
  | clauseMark
  | posMark | negMark
  | varMark | endMark
deriving DecidableEq, Repr, Fintype, Inhabited

/-- The polarity marker of a literal. -/
def litSym (l : Literal) : CNFSym :=
  match l with | Literal.pos _ => CNFSym.posMark | Literal.neg _ => CNFSym.negMark

/-- Encode a literal as `polMark :: varMark :: (i + 1) endMark`s (unary index). -/
def encLit (l : Literal) : List CNFSym :=
  litSym l :: CNFSym.varMark :: List.replicate (litIndex l + 1) CNFSym.endMark

/-- Encode a clause as `clauseMark` followed by its literal encodings. -/
def encClause (c : Clause) : List CNFSym :=
  CNFSym.clauseMark :: c.flatMap encLit

/-- Encode a CNF formula as the concatenation of its clause encodings. -/
def encCNF (f : CNF) : List CNFSym :=
  f.flatMap encClause

/-- A suffix that does not begin with an `endMark`, so a variable's unary index
run cannot run into it.  Continuations after a literal encoding satisfy this. -/
def ValidSuffixCNF (syms : List CNFSym) : Prop :=
  syms.head? ≠ some CNFSym.endMark

lemma validSuffixCNF_nil : ValidSuffixCNF [] := by
  simp [ValidSuffixCNF]

lemma validSuffixCNF_encLit (l : Literal) (rest : List CNFSym) :
    ValidSuffixCNF (encLit l ++ rest) := by
  cases l <;> simp [encLit, litSym, ValidSuffixCNF]

lemma validSuffixCNF_bind_encLit (c : Clause) : ValidSuffixCNF (c.flatMap encLit) := by
  cases c with
  | nil => simp [ValidSuffixCNF]
  | cons l rest => cases l <;> simp [ValidSuffixCNF, encLit, litSym, List.flatMap]

/-- Consume a unary variable index: `endMark`s are counted from `i`. -/
def decodeCNFVarIdx : Nat → List CNFSym → Nat × List CNFSym
  | i, CNFSym.endMark :: rest => decodeCNFVarIdx (i + 1) rest
  | i, rest => (i, rest)

/-- `decodeCNFVarIdx` leaves a suffix no longer than its input. -/
lemma decodeCNFVarIdx_suffix_le (i : Nat) (syms : List CNFSym) :
    (decodeCNFVarIdx i syms).2.length ≤ syms.length := by
  induction syms generalizing i with
  | nil => simp [decodeCNFVarIdx]
  | cons s rest ih =>
      by_cases hs : s = CNFSym.endMark
      · subst s
        simp [decodeCNFVarIdx]
        have h := ih (i + 1)
        omega
      · simp [decodeCNFVarIdx, hs]

/-- `decodeCNFVarIdx` on a valid continuation leaves it untouched. -/
lemma decodeCNFVarIdx_valid (i : Nat) {rest : List CNFSym} (hv : ValidSuffixCNF rest) :
    decodeCNFVarIdx i rest = (i, rest) := by
  cases rest with
  | nil => simp [decodeCNFVarIdx]
  | cons s rest' =>
      have hsne : s ≠ CNFSym.endMark := by
        intro hse
        apply hv
        rw [hse]
        rfl
      by_cases hse : s = CNFSym.endMark
      · exfalso
        exact hsne hse
      · simp [decodeCNFVarIdx, hse]

/-- `decodeCNFVarIdx` consumes `j` `endMark`s, raising the index by `j`. -/
lemma decodeCNFVarIdx_replicate (i j : Nat) {rest : List CNFSym} (hv : ValidSuffixCNF rest) :
    decodeCNFVarIdx i (List.replicate j CNFSym.endMark ++ rest) = (i + j, rest) := by
  induction j generalizing i with
  | zero => simpa using decodeCNFVarIdx_valid i hv
  | succ j ih =>
      rw [List.replicate_succ, List.cons_append, decodeCNFVarIdx]
      have h := ih (i + 1)
      rw [h]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Decode one literal, consuming its polarity mark, `varMark`, and the first
`endMark` of its unary index.  Malformed input consumes one symbol as junk. -/
def decodeLit : List CNFSym → Literal × List CNFSym
  | CNFSym.posMark :: CNFSym.varMark :: CNFSym.endMark :: rest =>
      let (i, rest') := decodeCNFVarIdx 0 rest
      (Literal.pos i, rest')
  | CNFSym.negMark :: CNFSym.varMark :: CNFSym.endMark :: rest =>
      let (i, rest') := decodeCNFVarIdx 0 rest
      (Literal.neg i, rest')
  | _ :: rest => (Literal.pos 0, rest)
  | [] => (Literal.pos 0, [])

/-- `decodeLit` leaves a suffix strictly shorter than a nonempty input. -/
lemma decodeLit_suffix_lt (s : CNFSym) (rest : List CNFSym) :
    (decodeLit (s :: rest)).2.length < (s :: rest).length := by
  by_cases hs : s = CNFSym.posMark
  · subst s
    cases rest with
    | nil => simp [decodeLit]
    | cons s' rest' =>
        by_cases hs' : s' = CNFSym.varMark
        · subst s'
          cases rest' with
          | nil => simp [decodeLit]
          | cons s'' rest'' =>
              by_cases hs'' : s'' = CNFSym.endMark
              · subst s''
                simp [decodeLit]
                have h := decodeCNFVarIdx_suffix_le 0 rest''
                omega
              · simp [decodeLit, hs'']
        · simp [decodeLit, hs']
  · by_cases hneg : s = CNFSym.negMark
    · subst s
      cases rest with
      | nil => simp [decodeLit]
      | cons s' rest' =>
          by_cases hs' : s' = CNFSym.varMark
          · subst s'
            cases rest' with
            | nil => simp [decodeLit]
            | cons s'' rest'' =>
                by_cases hs'' : s'' = CNFSym.endMark
                · subst s''
                  simp [decodeLit]
                  have h := decodeCNFVarIdx_suffix_le 0 rest''
                  omega
                · simp [decodeLit, hs'']
          · simp [decodeLit, hs']
    · simp [decodeLit, hs, hneg]

/-- Decode the literals of one clause, stopping at the next `clauseMark` or the
end of the list. -/
def decodeLits : List CNFSym → Clause × List CNFSym
  | [] => ([], [])
  | CNFSym.clauseMark :: rest => ([], CNFSym.clauseMark :: rest)
  | l :: rest =>
      ((decodeLit (l :: rest)).1 :: (decodeLits (decodeLit (l :: rest)).2).1,
        (decodeLits (decodeLit (l :: rest)).2).2)
termination_by syms => syms.length
decreasing_by
  exact decodeLit_suffix_lt l rest

/-- `decodeLits` leaves a suffix no longer than its input. -/
lemma decodeLits_suffix_le (syms : List CNFSym) : (decodeLits syms).2.length ≤ syms.length := by
  let P : List CNFSym → Prop := fun l => (decodeLits l).2.length ≤ l.length
  have hwf : ∀ n : Nat, ∀ l : List CNFSym, l.length = n → P l := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro l hl
        cases l with
        | nil => simp [P, decodeLits.eq_1]
        | cons s rest =>
            by_cases hs : s = CNFSym.clauseMark
            · subst s
              simp [P, decodeLits.eq_2]
            · rcases hdec : decodeLit (s :: rest) with ⟨lit, rest'⟩
              have hb : (decodeLit (s :: rest)).2.length < (s :: rest).length :=
                decodeLit_suffix_lt s rest
              have hpr : (decodeLit (s :: rest)).2 = rest' := by
                rw [hdec]
              have hlt' : rest'.length < (s :: rest).length := by
                rwa [← hpr]
              have hih : (decodeLits rest').2.length ≤ rest'.length := by
                exact ih rest'.length (by omega) rest' rfl
              change (decodeLits (s :: rest)).2.length ≤ (s :: rest).length
              rw [decodeLits.eq_3]
              · simp
                rw [hpr]
                exact le_trans hih (Nat.le_of_lt hlt')
              · exact hs
  exact hwf syms.length syms rfl

/-- Decode a CNF formula (junk on malformed input). -/
def decodeCNF : List CNFSym → CNF
  | [] => []
  | CNFSym.clauseMark :: rest =>
      (decodeLits rest).1 :: decodeCNF (decodeLits rest).2
  | _ :: rest => decodeCNF rest
termination_by syms => syms.length
decreasing_by
  all_goals
    first
    | exact Nat.lt_succ_self rest.length
    | have hle := decodeLits_suffix_le rest
      have hlt : rest.length < (CNFSym.clauseMark :: rest).length := by simp
      omega

/-- A list that is empty or begins with `clauseMark`: a clause boundary. -/
def IsClauseBoundary (syms : List CNFSym) : Prop :=
  syms = [] ∨ syms.head? = some CNFSym.clauseMark

lemma isClauseBoundary_encCNF (f : CNF) : IsClauseBoundary (encCNF f) := by
  cases f with
  | nil => left; rfl
  | cons c rest => right; simp [encCNF, encClause]

/-- `decodeLits` on a clause boundary returns the empty clause. -/
lemma decodeLits_boundary (rest : List CNFSym) (hrest : IsClauseBoundary rest) :
    decodeLits rest = ([], rest) := by
  rcases hrest with hnil | hclause
  · subst hnil
    simp [decodeLits]
  · cases rest with
    | nil => contradiction
    | cons s rest' =>
        have hs : s = CNFSym.clauseMark := by simpa using hclause
        subst s
        simp [decodeLits]

/-- The continuation after a clause's literal encodings, followed by a clause
boundary, does not begin with an `endMark`. -/
lemma validSuffixCNF_flatMap_encLit_append (c : Clause) {rest : List CNFSym}
    (hrest : IsClauseBoundary rest) : ValidSuffixCNF (c.flatMap encLit ++ rest) := by
  cases c with
  | nil =>
      rcases hrest with hnil | hclause
      · subst hnil
        simp [ValidSuffixCNF]
      · cases rest with
        | nil => contradiction
        | cons s rest' =>
            have hs : s = CNFSym.clauseMark := by simpa using hclause
            subst s
            simp [ValidSuffixCNF]
  | cons l rest' =>
      cases l <;> simp [encLit, litSym, ValidSuffixCNF, List.flatMap]

/-- Decoding a literal's encoding recovers it. -/
lemma decodeLit_encLit (l : Literal) {rest : List CNFSym} (hv : ValidSuffixCNF rest) :
    decodeLit (encLit l ++ rest) = (l, rest) := by
  cases l with
  | pos i =>
      have hrep : List.replicate (i + 1) CNFSym.endMark ++ rest =
          CNFSym.endMark :: (List.replicate i CNFSym.endMark ++ rest) := by
        rw [show i + 1 = Nat.succ i by omega]
        simp [List.replicate_succ]
      have h : decodeCNFVarIdx 0 (List.replicate i CNFSym.endMark ++ rest) = (i, rest) := by
        simpa using decodeCNFVarIdx_replicate 0 i hv
      simp [encLit, litSym, litIndex]
      rw [hrep]
      simp [decodeLit, h]
  | neg i =>
      have hrep : List.replicate (i + 1) CNFSym.endMark ++ rest =
          CNFSym.endMark :: (List.replicate i CNFSym.endMark ++ rest) := by
        rw [show i + 1 = Nat.succ i by omega]
        simp [List.replicate_succ]
      have h : decodeCNFVarIdx 0 (List.replicate i CNFSym.endMark ++ rest) = (i, rest) := by
        simpa using decodeCNFVarIdx_replicate 0 i hv
      simp [encLit, litSym, litIndex]
      rw [hrep]
      simp [decodeLit, h]

/-- `decodeLits` consumes one literal's encoding, keeping the rest for later. -/
lemma decodeLits_encLit_cont (l : Literal) {X : List CNFSym} (hv : ValidSuffixCNF X) :
    decodeLits (encLit l ++ X) = (l :: (decodeLits X).1, (decodeLits X).2) := by
  cases l with
  | pos i =>
      have hrep : List.replicate (i + 1) CNFSym.endMark ++ X =
          CNFSym.endMark :: (List.replicate i CNFSym.endMark ++ X) := by
        rw [show i + 1 = Nat.succ i by omega]
        simp [List.replicate_succ]
      have h : decodeCNFVarIdx 0 (List.replicate i CNFSym.endMark ++ X) = (i, X) := by
        simpa using decodeCNFVarIdx_replicate 0 i hv
      simp [encLit, litSym, litIndex]
      rw [hrep]
      rw [decodeLits.eq_3]
      · simp [decodeLit]
        rw [h]
        simp
      · intro hcl
        cases hcl
  | neg i =>
      have hrep : List.replicate (i + 1) CNFSym.endMark ++ X =
          CNFSym.endMark :: (List.replicate i CNFSym.endMark ++ X) := by
        rw [show i + 1 = Nat.succ i by omega]
        simp [List.replicate_succ]
      have h : decodeCNFVarIdx 0 (List.replicate i CNFSym.endMark ++ X) = (i, X) := by
        simpa using decodeCNFVarIdx_replicate 0 i hv
      simp [encLit, litSym, litIndex]
      rw [hrep]
      rw [decodeLits.eq_3]
      · simp [decodeLit]
        rw [h]
        simp
      · intro hcl
        cases hcl

/-- `decodeLits` parses the literal encodings of a clause, leaving a clause
boundary untouched. -/
lemma decodeLits_bind_encLit (c : Clause) {rest : List CNFSym}
    (hrest : IsClauseBoundary rest) :
    decodeLits (c.flatMap encLit ++ rest) = (c, rest) := by
  induction c with
  | nil => simp [decodeLits_boundary, hrest]
  | cons l rest' ih =>
      have hv : ValidSuffixCNF (rest'.flatMap encLit ++ rest) :=
        validSuffixCNF_flatMap_encLit_append rest' hrest
      have hc := decodeLits_encLit_cont l hv
      rw [List.flatMap_cons, List.append_assoc]
      rw [hc, ih]

/-- Decoding an encoded CNF recovers it. -/
lemma decodeCNF_encCNF (f : CNF) : decodeCNF (encCNF f) = f := by
  induction f with
  | nil => simp [encCNF, decodeCNF.eq_1]
  | cons c rest ih =>
      have h := decodeLits_bind_encLit c (isClauseBoundary_encCNF rest)
      rw [encCNF, List.flatMap_cons, encClause, List.cons_append]
      rw [decodeCNF.eq_2]
      change (decodeLits (List.flatMap encLit c ++ encCNF rest)).1 ::
          decodeCNF (decodeLits (List.flatMap encLit c ++ encCNF rest)).2 = c :: rest
      rw [h]
      simp [ih]

/-- **3-CNF-SAT**: the language of satisfiable CNF formulas, encoded as symbol
lists (decoded via `decodeCNF`). -/
def ThreeCNFSat : Language CNFSym :=
  { syms | CnfSatisfiable (decodeCNF syms) }

/-- The input-length variant of the satisfiability theorem. -/
lemma cnfSatisfiable_to3CNF_len_iff (φ : Formula) (n : Nat) (hnext : n ≥ numVars φ) :
    CnfSatisfiable (to3CNF_len φ n) ↔ Formula.Satisfiable φ := by
  simpa [to3CNF_len] using cnfSatisfiable_to3CNF'_iff φ n hnext

/-- **Lemma 34.7 (semantic).**  `to3CNF φ` is satisfiable iff `φ` is. -/
theorem cnfSatisfiable_to3CNF_iff (φ : Formula) :
    CnfSatisfiable (to3CNF φ) ↔ Formula.Satisfiable φ := by
  have h := cnfSatisfiable_to3CNF'_iff φ (numVars φ) le_rfl
  simpa [to3CNF, to3CNF_len] using h

end Chapter34

end CLRS
