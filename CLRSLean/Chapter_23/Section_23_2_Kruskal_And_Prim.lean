import CLRSLean.Chapter_23.Section_23_1_Growing_Minimum_Spanning_Trees

open Finset

/-!
# CLRS Section 23.2 - Kruskal and Prim

This section builds on the safe-edge theorem from Section 23.1.  It contains the
mathematical Kruskal pass, cut-certificate induction, finite-graph wrappers, and
the component-oracle interface.  It also isolates the sorted-edge-order
lightness argument used by CLRS: once previously processed edges are known not
to cross the current component cut, the current edge is light by sorted order.
Union-find implementation correctness is deliberately deferred: the current
proof works at the mathematical cycle-test interface level.

Main results:

- Theorem {lit}`lightest_crossing_of_sorted_prefix`: sorted edge order plus a
  processed-prefix exclusion invariant proves the lightness condition for a
  cut.
- Theorem {lit}`cut_certificate_of_component_oracle_sorted_prefix`: packages
  that sorted-order lightness proof into a component-oracle cut certificate.
- Theorem {lit}`kruskal_optimal`: safe-edge induction for the mathematical
  Kruskal pass.

Current gaps:

- Derive the processed-prefix exclusion invariant from a stronger exact
  component/cycle-test model.
- Prove the final selected edge set is a spanning tree from connectedness and
  a complete edge scan.
- Add Prim's theorem interface.
-/

namespace CLRS
namespace MST

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/-! ## Component-based cycle-test interface -/

/-- A mathematical component oracle for the current selected edge set.  It is
exactly the specification a union-find implementation should refine. -/
structure ComponentOracle (G : Graph V E) where
  component : Finset E → V → Finset V
  mem_self : ∀ A v, v ∈ component A v
  closed_src :
    ∀ A root e, e ∈ A → G.src e ∈ component A root → G.dst e ∈ component A root
  closed_dst :
    ∀ A root e, e ∈ A → G.dst e ∈ component A root → G.src e ∈ component A root

namespace ComponentOracle

omit [DecidableEq V] [DecidableEq E] in
theorem respects (C : ComponentOracle G) (A : Finset E) (root : V) :
    G.Respects (C.component A root) A := by
  intro e he hcross
  rcases hcross with ⟨hsrc, hdst⟩ | ⟨hdst, hsrc⟩
  · exact hdst (C.closed_src A root e he hsrc)
  · exact hsrc (C.closed_dst A root e he hdst)

end ComponentOracle

/-- The executable-style cycle test induced by a component oracle: accept an
edge iff its destination is outside the source component. -/
def acceptByComponent (G : Graph V E) (C : ComponentOracle G)
    (A : Finset E) (e : E) : Bool :=
  decide (G.dst e ∉ C.component A (G.src e))

omit [DecidableEq E] in
private theorem not_mem_component_of_accept {G : Graph V E} {C : ComponentOracle G}
    {A : Finset E} {e : E} (h : acceptByComponent G C A e = true) :
    G.dst e ∉ C.component A (G.src e) := by
  simpa [acceptByComponent] using h

/-- Accepted component edges induce the cut used in the CLRS proof. -/
theorem cut_certificate_of_component_oracle {G : Graph V E} {P : Problem E}
    {w : E → Nat} (C : ComponentOracle G) {A : Finset E} {e : E}
    (haccept : acceptByComponent G C A e = true)
    (hlight :
      ∀ f, G.Crosses (C.component A (G.src e)) f → w e ≤ w f)
    (hexchange :
      ∀ T, IsMSTExtending P w A T → e ∉ T →
        ∃ f, f ∈ T ∧ G.Crosses (C.component A (G.src e)) f ∧
          P.IsSpanningTree (insert e (T.erase f)) ∧
          A ⊆ insert e (T.erase f)) :
    CutCertificate G P w A (C.component A (G.src e)) e := by
  refine ⟨?_, C.respects A (G.src e), hlight, hexchange⟩
  exact Or.inl ⟨C.mem_self A (G.src e), not_mem_component_of_accept haccept⟩

/-! ## Sorted-order lightness certificates -/

/--
An edge list is sorted in nondecreasing weight order.

This CLRS-facing predicate is deliberately small: the head is no heavier than
every later edge, and the tail is sorted recursively.
-/
def WeightSorted (w : E → Nat) : List E → Prop
  | [] => True
  | e :: es => (∀ f, f ∈ es → w e ≤ w f) ∧ WeightSorted w es

omit [DecidableEq E] in
/-- A suffix of a sorted edge list is sorted. -/
theorem weightSorted_suffix_of_append (w : E → Nat)
    (processed rest : List E) :
    WeightSorted w (processed ++ rest) → WeightSorted w rest := by
  induction processed with
  | nil =>
      intro hsorted
      simpa using hsorted
  | cons _ processed ih =>
      intro hsorted
      exact ih hsorted.2

omit [DecidableEq E] in
/-- In a sorted nonempty edge list, the head is no heavier than any member. -/
theorem weightSorted_head_le_of_mem {w : E → Nat} {e f : E}
    {suffix : List E} (hsorted : WeightSorted w (e :: suffix))
    (hf : f ∈ e :: suffix) :
    w e ≤ w f := by
  rw [List.mem_cons] at hf
  rcases hf with hfe | hfSuffix
  · simp [hfe]
  · exact hsorted.1 f hfSuffix

omit [DecidableEq V] [DecidableEq E] in
/--
If every crossing edge appears in {lit}`processed ++ e :: suffix`, and the
processed edge prefix contains no crossing edge for the current cut, then every
crossing edge appears at or after {lit}`e`.
-/
theorem crossing_mem_current_suffix_of_prefix_excludes
    {G : Graph V E} {S : Finset V} {processed suffix : List E} {e f : E}
    (hall :
      ∀ g, G.Crosses S g → g ∈ processed ++ e :: suffix)
    (hprefix :
      ∀ g, g ∈ processed → ¬ G.Crosses S g)
    (hcross : G.Crosses S f) :
    f ∈ e :: suffix := by
  have hfAll := hall f hcross
  rcases List.mem_append.mp hfAll with hfPrefix | hfSuffix
  · exact False.elim ((hprefix f hfPrefix) hcross)
  · exact hfSuffix

omit [DecidableEq V] [DecidableEq E] in
/--
Sorted edge order plus the processed-prefix exclusion invariant proves the
lightness side condition for the current Kruskal cut.

This isolates the CLRS sorted-order argument from the graph-specific proof that
previously processed edges do not cross the current component cut.
-/
theorem lightest_crossing_of_sorted_prefix {G : Graph V E} {w : E → Nat}
    {S : Finset V} {processed suffix : List E} {e : E}
    (hsorted : WeightSorted w (processed ++ e :: suffix))
    (hall :
      ∀ f, G.Crosses S f → f ∈ processed ++ e :: suffix)
    (hprefix :
      ∀ f, f ∈ processed → ¬ G.Crosses S f) :
    ∀ f, G.Crosses S f → w e ≤ w f := by
  intro f hcross
  have hsuffixSorted :
      WeightSorted w (e :: suffix) :=
    weightSorted_suffix_of_append w processed (e :: suffix) hsorted
  have hfSuffix :
      f ∈ e :: suffix :=
    crossing_mem_current_suffix_of_prefix_excludes
      (G := G) (S := S) (processed := processed) (suffix := suffix)
      (e := e) hall hprefix hcross
  exact weightSorted_head_le_of_mem hsuffixSorted hfSuffix

/--
Component-oracle cut certificate where the lightness field is discharged from
sorted edge order and a processed-prefix exclusion invariant.
-/
theorem cut_certificate_of_component_oracle_sorted_prefix
    {G : Graph V E} {P : Problem E} {w : E → Nat} (C : ComponentOracle G)
    {A : Finset E} {e : E} {processed suffix : List E}
    (haccept : acceptByComponent G C A e = true)
    (hsorted : WeightSorted w (processed ++ e :: suffix))
    (hall :
      ∀ f, G.Crosses (C.component A (G.src e)) f →
        f ∈ processed ++ e :: suffix)
    (hprefix :
      ∀ f, f ∈ processed →
        ¬ G.Crosses (C.component A (G.src e)) f)
    (hexchange :
      ∀ T, IsMSTExtending P w A T → e ∉ T →
        ∃ f, f ∈ T ∧ G.Crosses (C.component A (G.src e)) f ∧
          P.IsSpanningTree (insert e (T.erase f)) ∧
          A ⊆ insert e (T.erase f)) :
    CutCertificate G P w A (C.component A (G.src e)) e := by
  exact cut_certificate_of_component_oracle C haccept
    (lightest_crossing_of_sorted_prefix hsorted hall hprefix)
    hexchange


/-! ## Kruskal-style safe-edge induction -/

/-- A mathematical Kruskal pass over a fixed edge order.

The Boolean `accept A e` abstracts the cycle test: when it returns true, the
edge is inserted into the current forest; otherwise it is skipped.
-/
def kruskal (accept : Finset E → E → Bool) : List E → Finset E → Finset E
  | [], A => A
  | e :: es, A => kruskal accept es (if accept A e then insert e A else A)

/-- The proof obligation needed by the abstract Kruskal induction: every edge
accepted by the cycle test is safe for the current prefix.  In a concrete graph
development this is discharged by a cut-property certificate. -/
structure KruskalCertificate (P : Problem E) (w : E → Nat)
    (accept : Finset E → E → Bool) : Prop where
  safe : ∀ A e, accept A e = true → SafeEdge P w A e

/-- A CLRS-style certificate for Kruskal: each accepted edge has a cut
certificate showing it is light across some cut respecting the current forest. -/
structure KruskalCutCertificate (G : Graph V E) (P : Problem E) (w : E → Nat)
    (accept : Finset E → E → Bool) : Prop where
  cut : ∀ A e, accept A e = true → ∃ S, CutCertificate G P w A S e

omit [DecidableEq V] in
theorem kruskal_certificate_of_cut_certificates {G : Graph V E} {P : Problem E}
    {w : E → Nat} {accept : Finset E → E → Bool}
    (cert : KruskalCutCertificate G P w accept) :
    KruskalCertificate P w accept := by
  refine ⟨?_⟩
  intro A e hacc
  rcases cert.cut A e hacc with ⟨S, hcut⟩
  exact safe_edge_of_lightest_crossing hcut

theorem kruskal_cut_certificate_of_component_oracle {G : Graph V E}
    {P : Problem E} {w : E → Nat} (C : ComponentOracle G)
    (hlight :
      ∀ A e, acceptByComponent G C A e = true →
        ∀ f, G.Crosses (C.component A (G.src e)) f → w e ≤ w f)
    (hexchange :
      ∀ A e, acceptByComponent G C A e = true →
        ∀ T, IsMSTExtending P w A T → e ∉ T →
          ∃ f, f ∈ T ∧ G.Crosses (C.component A (G.src e)) f ∧
            P.IsSpanningTree (insert e (T.erase f)) ∧
            A ⊆ insert e (T.erase f)) :
    KruskalCutCertificate G P w (acceptByComponent G C) := by
  refine ⟨?_⟩
  intro A e hacc
  exact ⟨C.component A (G.src e),
    cut_certificate_of_component_oracle C hacc
      (hlight A e hacc) (hexchange A e hacc)⟩

theorem kruskal_extends_start (accept : Finset E → E → Bool)
    (edges : List E) (A : Finset E) :
    A ⊆ kruskal accept edges A := by
  induction edges generalizing A with
  | nil =>
      simp [kruskal]
  | cons e es ih =>
      by_cases hacc : accept A e = true
      · have hA : A ⊆ insert e A := Finset.subset_insert e A
        exact hA.trans (by simpa [kruskal, hacc] using ih (insert e A))
      · have hfalse : accept A e = false := by
          cases h : accept A e <;> simp [h] at hacc ⊢
        simpa [kruskal, hfalse] using ih A

private theorem optimal_for_smaller_prefix {P : Problem E} {w : E → Nat}
    {A₀ A T T' : Finset E} (hA₀A : A₀ ⊆ A)
    (hcur : IsMSTExtending P w A T) (hbase : IsMSTExtending P w A₀ T)
    (hnew : IsMSTExtending P w A T') :
    IsMSTExtending P w A₀ T' := by
  refine ⟨hnew.tree, ?_, ?_⟩
  · exact hA₀A.trans hnew.includes
  · intro U hUtree hUincludes
    exact (hnew.optimal T hcur.tree hcur.includes).trans
      (hbase.optimal U hUtree hUincludes)

theorem kruskal_preserves_mst {P : Problem E} {w : E → Nat}
    {accept : Finset E → E → Bool} (cert : KruskalCertificate P w accept)
    (edges : List E) {A₀ A T : Finset E} (hA₀A : A₀ ⊆ A)
    (hcur : IsMSTExtending P w A T) (hbase : IsMSTExtending P w A₀ T) :
    ∃ T', IsMSTExtending P w (kruskal accept edges A) T' ∧
      IsMSTExtending P w A₀ T' := by
  induction edges generalizing A T with
  | nil =>
      exact ⟨T, by simpa [kruskal] using hcur, hbase⟩
  | cons e es ih =>
      by_cases hacc : accept A e = true
      · rcases cert.safe A e hacc T hcur with ⟨T₁, hnext, hprefix⟩
        have hbase₁ : IsMSTExtending P w A₀ T₁ :=
          optimal_for_smaller_prefix hA₀A hcur hbase hprefix
        have hA₀next : A₀ ⊆ insert e A :=
          hA₀A.trans (Finset.subset_insert e A)
        simpa [kruskal, hacc] using ih hA₀next hnext hbase₁
      · have hfalse : accept A e = false := by
          cases h : accept A e <;> simp [h] at hacc ⊢
        simpa [kruskal, hfalse] using ih hA₀A hcur hbase

/-- Mathematical Kruskal optimality.

If the accept rule only accepts safe edges, the initial prefix has an optimum,
and the final selected edge set is itself a maximal spanning tree, then the
Kruskal result is an optimum extending the initial prefix.  The final maximality
assumption is the graph-specific fact that a spanning tree cannot be properly
extended by another spanning tree; concrete graph modules can prove it from the
usual cardinality characterization of spanning trees.
-/
theorem kruskal_optimal {P : Problem E} {w : E → Nat}
    {accept : Finset E → E → Bool} (cert : KruskalCertificate P w accept)
    (edges : List E) {A₀ T₀ : Finset E}
    (hstart : IsMSTExtending P w A₀ T₀)
    (hfinal_tree : P.IsSpanningTree (kruskal accept edges A₀))
    (hfinal_maximal :
      ∀ T, P.IsSpanningTree T → kruskal accept edges A₀ ⊆ T →
        T = kruskal accept edges A₀) :
    IsMSTExtending P w A₀ (kruskal accept edges A₀) := by
  rcases kruskal_preserves_mst cert edges (Subset.rfl : A₀ ⊆ A₀) hstart hstart with
    ⟨T, hfinal, hglobal⟩
  have hT : T = kruskal accept edges A₀ :=
    hfinal_maximal T hfinal.tree hfinal.includes
  refine ⟨hfinal_tree, ?_, ?_⟩
  · simpa [← hT] using hglobal.includes
  · intro U hUtree hUincludes
    simpa [hT] using hglobal.optimal U hUtree hUincludes

omit [DecidableEq V] in
/-- Kruskal optimality stated directly from CLRS cut certificates. -/
theorem kruskal_optimal_of_cut_certificates {G : Graph V E} {P : Problem E}
    {w : E → Nat} {accept : Finset E → E → Bool}
    (cert : KruskalCutCertificate G P w accept) (edges : List E)
    {A₀ T₀ : Finset E} (hstart : IsMSTExtending P w A₀ T₀)
    (hfinal_tree : P.IsSpanningTree (kruskal accept edges A₀))
    (hfinal_maximal :
      ∀ T, P.IsSpanningTree T → kruskal accept edges A₀ ⊆ T →
        T = kruskal accept edges A₀) :
    IsMSTExtending P w A₀ (kruskal accept edges A₀) := by
  exact kruskal_optimal (kruskal_certificate_of_cut_certificates cert)
    edges hstart hfinal_tree hfinal_maximal

theorem kruskal_optimal_of_component_oracle {G : Graph V E} {P : Problem E}
    {w : E → Nat} (C : ComponentOracle G)
    (hlight :
      ∀ A e, acceptByComponent G C A e = true →
        ∀ f, G.Crosses (C.component A (G.src e)) f → w e ≤ w f)
    (hexchange :
      ∀ A e, acceptByComponent G C A e = true →
        ∀ T, IsMSTExtending P w A T → e ∉ T →
          ∃ f, f ∈ T ∧ G.Crosses (C.component A (G.src e)) f ∧
            P.IsSpanningTree (insert e (T.erase f)) ∧
            A ⊆ insert e (T.erase f))
    (edges : List E) {A₀ T₀ : Finset E}
    (hstart : IsMSTExtending P w A₀ T₀)
    (hfinal_tree : P.IsSpanningTree (kruskal (acceptByComponent G C) edges A₀))
    (hfinal_maximal :
      ∀ T, P.IsSpanningTree T → kruskal (acceptByComponent G C) edges A₀ ⊆ T →
        T = kruskal (acceptByComponent G C) edges A₀) :
    IsMSTExtending P w A₀ (kruskal (acceptByComponent G C) edges A₀) := by
  exact kruskal_optimal_of_cut_certificates
    (kruskal_cut_certificate_of_component_oracle C hlight hexchange)
    edges hstart hfinal_tree hfinal_maximal

/-- A verified executable cycle test.  A union-find implementation should
provide an `accept` function and prove that it agrees with the component oracle. -/
structure CycleTestImplementation (G : Graph V E) (C : ComponentOracle G) where
  accept : Finset E → E → Bool
  correct : ∀ A e, accept A e = acceptByComponent G C A e

/-- The canonical executable cycle test associated to a component oracle. -/
def componentCycleTest (G : Graph V E) (C : ComponentOracle G) :
    CycleTestImplementation G C where
  accept := acceptByComponent G C
  correct := by
    intro A e
    rfl

theorem kruskal_optimal_of_cycle_test {G : Graph V E} {P : Problem E}
    {w : E → Nat} {C : ComponentOracle G}
    (impl : CycleTestImplementation G C)
    (hlight :
      ∀ A e, impl.accept A e = true →
        ∀ f, G.Crosses (C.component A (G.src e)) f → w e ≤ w f)
    (hexchange :
      ∀ A e, impl.accept A e = true →
        ∀ T, IsMSTExtending P w A T → e ∉ T →
          ∃ f, f ∈ T ∧ G.Crosses (C.component A (G.src e)) f ∧
            P.IsSpanningTree (insert e (T.erase f)) ∧
            A ⊆ insert e (T.erase f))
    (edges : List E) {A₀ T₀ : Finset E}
    (hstart : IsMSTExtending P w A₀ T₀)
    (hfinal_tree : P.IsSpanningTree (kruskal impl.accept edges A₀))
    (hfinal_maximal :
      ∀ T, P.IsSpanningTree T → kruskal impl.accept edges A₀ ⊆ T →
        T = kruskal impl.accept edges A₀) :
    IsMSTExtending P w A₀ (kruskal impl.accept edges A₀) := by
  have hsame : impl.accept = acceptByComponent G C := by
    funext A e
    exact impl.correct A e
  have hlight' :
      ∀ A e, acceptByComponent G C A e = true →
        ∀ f, G.Crosses (C.component A (G.src e)) f → w e ≤ w f := by
    intro A e hacc
    exact hlight A e (by simpa [hsame] using hacc)
  have hexchange' :
      ∀ A e, acceptByComponent G C A e = true →
        ∀ T, IsMSTExtending P w A T → e ∉ T →
          ∃ f, f ∈ T ∧ G.Crosses (C.component A (G.src e)) f ∧
            P.IsSpanningTree (insert e (T.erase f)) ∧
            A ⊆ insert e (T.erase f) := by
    intro A e hacc
    exact hexchange A e (by simpa [hsame] using hacc)
  have hfinal_tree' :
      P.IsSpanningTree (kruskal (acceptByComponent G C) edges A₀) := by
    simpa [hsame] using hfinal_tree
  have hfinal_maximal' :
      ∀ T, P.IsSpanningTree T → kruskal (acceptByComponent G C) edges A₀ ⊆ T →
        T = kruskal (acceptByComponent G C) edges A₀ := by
    intro T hT hsub
    simpa [hsame] using hfinal_maximal T hT (by simpa [hsame] using hsub)
  simpa [hsame] using
    (kruskal_optimal_of_component_oracle (G := G) (P := P) (w := w) C
      hlight' hexchange' edges hstart hfinal_tree' hfinal_maximal')

namespace FiniteGraph

/-- Finite-graph Kruskal optimality.  The concrete spanning-tree definition
discharges the abstract maximality side condition. -/
theorem kruskal_optimal (G : FiniteGraph V E) {w : E → Nat}
    {accept : Finset E → E → Bool}
    (cert : KruskalCertificate G.toProblem w accept)
    (edges : List E) {A₀ T₀ : Finset E}
    (hstart : IsMSTExtending G.toProblem w A₀ T₀)
    (hfinal_tree : G.IsSpanningTree (kruskal accept edges A₀)) :
    IsMSTExtending G.toProblem w A₀ (kruskal accept edges A₀) := by
  exact CLRS.MST.kruskal_optimal cert edges hstart hfinal_tree
    (by
      intro T hT hsub
      exact G.spanning_tree_maximal hfinal_tree hT hsub)

theorem kruskal_optimal_of_component_oracle (G : FiniteGraph V E)
    {w : E → Nat} (C : ComponentOracle G.toGraph)
    (hlight :
      ∀ A e, acceptByComponent G.toGraph C A e = true →
        ∀ f, G.toGraph.Crosses (C.component A (G.src e)) f → w e ≤ w f)
    (hexchange :
      ∀ A e, acceptByComponent G.toGraph C A e = true →
        ∀ T, IsMSTExtending G.toProblem w A T → e ∉ T →
          ∃ f, f ∈ T ∧ G.toGraph.Crosses (C.component A (G.src e)) f ∧
            G.IsSpanningTree (insert e (T.erase f)) ∧
            A ⊆ insert e (T.erase f))
    (edges : List E) {A₀ T₀ : Finset E}
    (hstart : IsMSTExtending G.toProblem w A₀ T₀)
    (hfinal_tree : G.IsSpanningTree (kruskal (acceptByComponent G.toGraph C) edges A₀)) :
    IsMSTExtending G.toProblem w A₀
      (kruskal (acceptByComponent G.toGraph C) edges A₀) := by
  exact CLRS.MST.kruskal_optimal_of_component_oracle (G := G.toGraph)
    (P := G.toProblem) (w := w) C hlight hexchange edges hstart hfinal_tree
    (by
      intro T hT hsub
      exact G.spanning_tree_maximal hfinal_tree hT hsub)

theorem kruskal_optimal_of_cycle_test (G : FiniteGraph V E)
    {w : E → Nat} {C : ComponentOracle G.toGraph}
    (impl : CycleTestImplementation G.toGraph C)
    (hlight :
      ∀ A e, impl.accept A e = true →
        ∀ f, G.toGraph.Crosses (C.component A (G.src e)) f → w e ≤ w f)
    (hexchange :
      ∀ A e, impl.accept A e = true →
        ∀ T, IsMSTExtending G.toProblem w A T → e ∉ T →
          ∃ f, f ∈ T ∧ G.toGraph.Crosses (C.component A (G.src e)) f ∧
            G.IsSpanningTree (insert e (T.erase f)) ∧
            A ⊆ insert e (T.erase f))
    (edges : List E) {A₀ T₀ : Finset E}
    (hstart : IsMSTExtending G.toProblem w A₀ T₀)
    (hfinal_tree : G.IsSpanningTree (kruskal impl.accept edges A₀)) :
    IsMSTExtending G.toProblem w A₀ (kruskal impl.accept edges A₀) := by
  exact CLRS.MST.kruskal_optimal_of_cycle_test (G := G.toGraph)
    (P := G.toProblem) (w := w) impl hlight hexchange edges hstart hfinal_tree
    (by
      intro T hT hsub
      exact G.spanning_tree_maximal hfinal_tree hT hsub)

end FiniteGraph

end MST
end CLRS
