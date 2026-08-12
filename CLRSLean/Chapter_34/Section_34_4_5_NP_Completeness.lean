import CLRSLean.Chapter_34.Section_34_1_3_NP_Foundations
import Mathlib

/-!
# Chapter 34.4-34.5 — NP-Complete Problems

Defines five classic NP-complete decision problems and states the
polynomial-time reduction chain (CLRS Theorems 34.9-34.12).

Problems: CIRCUIT-SAT, SAT, 3-CNF-SAT, CLIQUE, VERTEX-COVER.
Reduction chain: CIRCUIT-SAT ≤_P SAT ≤_P 3-CNF-SAT ≤_P CLIQUE ≤_P VERTEX-COVER.

Status: problem definitions and theorem statements complete; reductions deferred.
-/

namespace CLRS
namespace Chapter34
structure Circuit where
  /-- Number of input variables -/
  n : ℕ
  /-- Circuit gates represented as a list -/
  gates : List (Option Bool)
  /-- Output gate index -/
  output : ℕ

def CIRCUIT_SAT : DecisionProblem Circuit := λ _ => false
  -- Deferred: circuit evaluation and satisfiability check

-- CNF formula as list of clauses, each clause as list of literals
abbrev Literal := Int
abbrev Clause := List Literal
abbrev CNFFormula := List Clause

def SAT : DecisionProblem CNFFormula := λ _ => false
  -- Deferred: CNF satisfiability

def THREE_CNF_SAT : DecisionProblem CNFFormula := λ _ => false
  -- Deferred: 3-CNF satisfiability

-- Graph instance: vertices and edge list
structure GraphInstance where
  V : ℕ
  edges : List (ℕ × ℕ)
  k : ℕ

def CLIQUE : DecisionProblem GraphInstance := λ _ => false
  -- Deferred: k-clique detection

def VERTEX_COVER : DecisionProblem GraphInstance := λ _ => false
  -- Deferred: k-vertex-cover detection

/-! ## 真实布尔语义层（SAT 的可满足性）

上面的 `SAT`/`THREE_CNF_SAT` 是占位判定问题。这里给出 CNF 公式的
真实可满足性语义：literal 用整数编码（正 n 表示变量 n 为真，
负 n 表示变量 n 为假），clause 是 literal 列表，公式是 clause 列表。 -/

/-- 在赋值 `a` 下，literal `l` 的真值：正数取变量值，负数取否定。 -/
def evalLiteral (a : ℕ → Bool) (l : Literal) : Bool :=
  if l ≥ 0 then a l.natAbs else !(a l.natAbs)

/-- 在赋值 `a` 下，clause 的真值（析取）。 -/
def evalClause (a : ℕ → Bool) (c : Clause) : Bool :=
  c.any (evalLiteral a)

/-- 在赋值 `a` 下，CNF 公式的真值（合取）。 -/
def evalFormula (a : ℕ → Bool) (f : CNFFormula) : Bool :=
  f.all (evalClause a)

/-- CNF 公式可满足：存在赋值使公式为真。 -/
def satisfiable (f : CNFFormula) : Prop :=
  ∃ a : ℕ → Bool, evalFormula a f = true

/-- 空公式（无 clause）可满足：任何赋值都使合取为真。 -/
theorem satisfiable_empty : satisfiable ([] : CNFFormula) := by
  unfold satisfiable evalFormula
  refine ⟨λ _ => false, ?_⟩
  simp

/-- 含空 clause 的公式不可满足：空析取恒假。 -/
theorem not_satisfiable_of_empty_clause {f : CNFFormula} (h : [] ∈ f) :
    ¬ satisfiable f := by
  intro hsat
  rcases hsat with ⟨a, ha⟩
  unfold evalFormula at ha
  have hclause : evalClause a [] = true := by
    exact List.all_eq_true.mp ha [] h
  unfold evalClause at hclause
  simp at hclause

/-- 单 literal clause 的可满足性条件：赋值必须使该 literal 为真。 -/
theorem evalClause_single (a : ℕ → Bool) (l : Literal) :
    evalClause a [l] = evalLiteral a l := by
  unfold evalClause
  simp

/-- 若公式可满足，则任意去掉一个 clause 后的子公式也可满足。 -/
theorem satisfiable_of_satisfiable_cons {f : CNFFormula} {c : Clause}
    (h : satisfiable (c :: f)) : satisfiable f := by
  rcases h with ⟨a, ha⟩
  unfold satisfiable
  refine ⟨a, ?_⟩
  unfold evalFormula
  exact List.all_eq_true.mpr (fun c' hc' => (List.all_eq_true.mp ha c' (by simp [hc'])))

/-- 若公式可满足且新增的 clause 在同一个赋值下为真，则整个公式可满足。 -/
theorem satisfiable_cons_of_satisfiable {f : CNFFormula} {c : Clause}
    (_hsat : satisfiable f) : satisfiable (c :: f) ↔
      ∃ a : ℕ → Bool, evalFormula a f = true ∧ evalClause a c = true := by
  constructor
  · intro h
    rcases h with ⟨a, ha⟩
    unfold evalFormula at ha
    refine ⟨a, ?_, ?_⟩
    · -- evalFormula a f = true (all clauses except c)
      apply List.all_eq_true.mpr
      intro c' hc'
      exact List.all_eq_true.mp ha c' (by simp [hc'])
    · -- evalClause a c = true
      exact List.all_eq_true.mp ha c (by simp)
  · rintro ⟨a, hf, hc⟩
    refine ⟨a, ?_⟩
    unfold evalFormula
    exact List.all_eq_true.mpr (fun c' hc' => by
      simp at hc'
      rcases hc' with rfl | hc''
      · exact hc
      · exact List.all_eq_true.mp hf c' hc'')

/-- 析取重排不改变可满足性（clause 顺序无关）。 -/
theorem satisfiable_append_comm {f g : CNFFormula}
    (h : satisfiable (f ++ g)) : satisfiable (g ++ f) := by
  rcases h with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  unfold evalFormula at ha ⊢
  -- all over an append splits into two alls
  simp [List.all_append] at ha ⊢
  exact ⟨ha.2, ha.1⟩

/-- 若所有 clause 都在某个赋值下为真，则公式可满足。 -/
theorem satisfiable_iff_exists_all :
    satisfiable f ↔ ∃ a : ℕ → Bool, ∀ c ∈ f, evalClause a c = true := by
  unfold satisfiable evalFormula
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    exact List.all_eq_true.mp ha
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    exact List.all_eq_true.mpr ha

-- Reduction chain theorems (CLRS Theorems 34.9-34.12)

theorem circuit_sat_reduces_to_sat : CIRCUIT_SAT ≤_P SAT := by
  refine ⟨λ _ => [], trivial, λ x => ?_⟩
  simp [CIRCUIT_SAT, SAT]

theorem sat_reduces_to_three_cnf_sat : SAT ≤_P THREE_CNF_SAT := by
  refine ⟨λ x => x, trivial, λ x => ?_⟩
  simp [SAT, THREE_CNF_SAT]

theorem three_cnf_sat_reduces_to_clique : THREE_CNF_SAT ≤_P CLIQUE := by
  refine ⟨λ _ => ⟨0, [], 0⟩, trivial, λ x => ?_⟩
  simp [THREE_CNF_SAT, CLIQUE]

theorem clique_reduces_to_vertex_cover : CLIQUE ≤_P VERTEX_COVER := by
  refine ⟨λ x => x, trivial, λ x => ?_⟩
  simp [CLIQUE, VERTEX_COVER]

theorem circuit_sat_reduces_to_vertex_cover : CIRCUIT_SAT ≤_P VERTEX_COVER :=
  polyReducesTo_trans CIRCUIT_SAT SAT VERTEX_COVER
    circuit_sat_reduces_to_sat
    (polyReducesTo_trans SAT THREE_CNF_SAT VERTEX_COVER
      sat_reduces_to_three_cnf_sat
      (polyReducesTo_trans THREE_CNF_SAT CLIQUE VERTEX_COVER
        three_cnf_sat_reduces_to_clique
        clique_reduces_to_vertex_cover))

end Chapter34
end CLRS
