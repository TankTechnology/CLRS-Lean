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
- Theorem {lit}`processed_prefix_excludes_of_exact_component_kruskal`: exact
  components derive the processed-prefix exclusion invariant for a Kruskal
  prefix.
- Theorem {lit}`cut_certificate_of_exact_component_kruskal_prefix`: packages
  the exact-component prefix invariant into a sorted-order cut certificate.
- Theorem {lit}`FiniteGraph.kruskal_spans_of_complete_exact_component`: a
  complete Kruskal edge scan over a connected finite graph spans all vertices.
- Theorem {lit}`kruskal_optimal`: safe-edge induction for the mathematical
  Kruskal pass.

Current gaps:

- Refine the exact component model to an executable union-find implementation
  if implementation correctness becomes part of scope.
- Prove forest preservation for the component cycle test; the subset and
  spanning parts of the final-tree obligation are now proved for complete edge
  scans.
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

/-! ## Exact component oracles -/

/--
An exact component oracle returns precisely the vertices connected to the root
by the currently selected edge set.
-/
def ExactComponentOracle (G : Graph V E) (C : ComponentOracle G) : Prop :=
  ∀ A root v, v ∈ C.component A root ↔ G.ConnectedIn A root v

namespace Graph

omit [DecidableEq V] [DecidableEq E] in
/-- The undirected adjacency relation is symmetric. -/
theorem adjIn_symm {G : Graph V E} {A : Finset E} {u v : V}
    (h : G.AdjIn A u v) :
    G.AdjIn A v u := by
  rcases h with ⟨e, heA, hend⟩
  refine ⟨e, heA, ?_⟩
  rcases hend with ⟨hsrc, hdst⟩ | ⟨hsrc, hdst⟩
  · exact Or.inr ⟨hsrc, hdst⟩
  · exact Or.inl ⟨hsrc, hdst⟩

omit [DecidableEq V] [DecidableEq E] in
/-- Connectivity induced by selected undirected edges is symmetric. -/
theorem connected_symm {G : Graph V E} {A : Finset E} {u v : V}
    (h : G.ConnectedIn A u v) :
    G.ConnectedIn A v u := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hpath hadj ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.tail Relation.ReflTransGen.refl
          (Graph.adjIn_symm hadj))
        ih

omit [DecidableEq V] [DecidableEq E] in
/-- Connectivity induced by selected edges is transitive. -/
theorem connected_trans {G : Graph V E} {A : Finset E} {u v x : V}
    (huv : G.ConnectedIn A u v) (hvx : G.ConnectedIn A v x) :
    G.ConnectedIn A u x :=
  Relation.ReflTransGen.trans huv hvx

omit [DecidableEq V] [DecidableEq E] in
/-- Any selected edge connects its own endpoints. -/
theorem connected_of_mem_edge {G : Graph V E} {A : Finset E} {e : E}
    (he : e ∈ A) :
    G.ConnectedIn A (G.src e) (G.dst e) := by
  exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl
    ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩

omit [DecidableEq V] [DecidableEq E] in
/--
If every edge of {lit}`B` has endpoints already connected in {lit}`A`, then one
adjacency step in {lit}`B` can be simulated by an {lit}`A`-connection.
-/
theorem connected_of_adjIn_of_edge_connected {G : Graph V E} {A B : Finset E}
    (hedge : ∀ e, e ∈ B → G.ConnectedIn A (G.src e) (G.dst e))
    {u v : V} (hadj : G.AdjIn B u v) :
    G.ConnectedIn A u v := by
  rcases hadj with ⟨e, heB, hend⟩
  have hconn := hedge e heB
  rcases hend with ⟨hsrc, hdst⟩ | ⟨hsrc, hdst⟩
  · simpa [hsrc, hdst] using hconn
  · have hconn' := Graph.connected_symm hconn
    simpa [hsrc, hdst] using hconn'

omit [DecidableEq V] [DecidableEq E] in
/--
If every edge of {lit}`B` has endpoints connected in {lit}`A`, then every
{lit}`B`-path can be transported to an {lit}`A`-path.
-/
theorem connected_of_edgewise_connected {G : Graph V E} {A B : Finset E}
    (hedge : ∀ e, e ∈ B → G.ConnectedIn A (G.src e) (G.dst e))
    {u v : V} (h : G.ConnectedIn B u v) :
    G.ConnectedIn A u v := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ hadj ih =>
      exact Graph.connected_trans ih
        (Graph.connected_of_adjIn_of_edge_connected hedge hadj)

end Graph

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

omit [DecidableEq E] in
private theorem mem_component_of_reject {G : Graph V E} {C : ComponentOracle G}
    {A : Finset E} {e : E} (h : acceptByComponent G C A e = false) :
    G.dst e ∈ C.component A (G.src e) := by
  by_contra hmem
  have htrue : acceptByComponent G C A e = true := by
    simp [acceptByComponent, hmem]
  simp [h] at htrue

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

omit [DecidableEq V] [DecidableEq E] in
/--
An edge whose endpoints are already connected by the current selected edge set
cannot cross any exact component cut for that selected edge set.
-/
theorem not_crosses_component_of_connected {G : Graph V E}
    {C : ComponentOracle G} (hexact : ExactComponentOracle G C)
    {A : Finset E} {root : V} {e : E}
    (hconn : G.ConnectedIn A (G.src e) (G.dst e)) :
    ¬ G.Crosses (C.component A root) e := by
  intro hcross
  rcases hcross with ⟨hsrc, hdst⟩ | ⟨hdst, hsrc⟩
  · have hrootSrc : G.ConnectedIn A root (G.src e) :=
      (hexact A root (G.src e)).1 hsrc
    have hrootDst : G.ConnectedIn A root (G.dst e) :=
      Graph.connected_trans hrootSrc hconn
    exact hdst ((hexact A root (G.dst e)).2 hrootDst)
  · have hrootDst : G.ConnectedIn A root (G.dst e) :=
      (hexact A root (G.dst e)).1 hdst
    have hdstSrc : G.ConnectedIn A (G.dst e) (G.src e) :=
      Graph.connected_symm hconn
    have hrootSrc : G.ConnectedIn A root (G.src e) :=
      Graph.connected_trans hrootDst hdstSrc
    exact hsrc ((hexact A root (G.src e)).2 hrootSrc)

omit [DecidableEq V] [DecidableEq E] in
/--
If an edge is either selected already or internally connected by the selected
edge set, it cannot cross an exact component cut.
-/
theorem not_crosses_component_of_mem_or_connected {G : Graph V E}
    {C : ComponentOracle G} (hexact : ExactComponentOracle G C)
    {A : Finset E} {root : V} {e : E}
    (haccounted : e ∈ A ∨ G.ConnectedIn A (G.src e) (G.dst e)) :
    ¬ G.Crosses (C.component A root) e := by
  rcases haccounted with heA | hconn
  · exact C.respects A root e heA
  · exact not_crosses_component_of_connected hexact hconn

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

The Boolean {lit}`accept A e` abstracts the cycle test: when it returns true, the
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

/-- Kruskal never selects an edge outside the initial set or the scanned edge
list. -/
theorem kruskal_subset_of_start_and_edges (accept : Finset E → E → Bool)
    (edges : List E) {A B : Finset E}
    (hA : A ⊆ B) (hedges : ∀ e, e ∈ edges → e ∈ B) :
    kruskal accept edges A ⊆ B := by
  induction edges generalizing A with
  | nil =>
      simpa [kruskal] using hA
  | cons e es ih =>
      by_cases hacc : accept A e = true
      · have heB : e ∈ B := hedges e (by simp)
        have hinsert : insert e A ⊆ B := Finset.insert_subset heB hA
        have htail : ∀ f, f ∈ es → f ∈ B := by
          intro f hf
          exact hedges f (by simp [hf])
        simpa [kruskal, hacc] using ih hinsert htail
      · have hfalse : accept A e = false := by
          cases h : accept A e <;> simp [h] at hacc ⊢
        have htail : ∀ f, f ∈ es → f ∈ B := by
          intro f hf
          exact hedges f (by simp [hf])
        simpa [kruskal, hfalse] using ih hA htail

/--
After a Kruskal prefix has been processed by an exact component oracle, every
processed edge is accounted for: it is either selected in the current forest or
its endpoints are already connected in that forest.
-/
theorem processed_edge_mem_or_connected_of_exact_component_kruskal
    {G : Graph V E} (C : ComponentOracle G)
    (hexact : ExactComponentOracle G C) (processed : List E)
    (A : Finset E) :
    ∀ f, f ∈ processed →
      f ∈ kruskal (acceptByComponent G C) processed A ∨
        G.ConnectedIn (kruskal (acceptByComponent G C) processed A)
          (G.src f) (G.dst f) := by
  induction processed generalizing A with
  | nil =>
      intro f hf
      simp at hf
  | cons e es ih =>
      intro f hf
      rw [List.mem_cons] at hf
      by_cases hacc : acceptByComponent G C A e = true
      · rcases hf with hfe | hfes
        · left
          subst f
          have heInsert : e ∈ insert e A := Finset.mem_insert_self e A
          have hsubset :
              insert e A ⊆ kruskal (acceptByComponent G C) es (insert e A) :=
            kruskal_extends_start (acceptByComponent G C) es (insert e A)
          simpa [kruskal, hacc] using hsubset heInsert
        · simpa [kruskal, hacc] using ih (insert e A) f hfes
      · have hfalse : acceptByComponent G C A e = false := by
          cases h : acceptByComponent G C A e <;> simp [h] at hacc ⊢
        rcases hf with hfe | hfes
        · right
          subst f
          have hmem : G.dst e ∈ C.component A (G.src e) :=
            mem_component_of_reject hfalse
          have hconnA : G.ConnectedIn A (G.src e) (G.dst e) :=
            (hexact A (G.src e) (G.dst e)).1 hmem
          have hsubset : A ⊆ kruskal (acceptByComponent G C) es A :=
            kruskal_extends_start (acceptByComponent G C) es A
          have hconnFinal :
              G.ConnectedIn (kruskal (acceptByComponent G C) es A)
                (G.src e) (G.dst e) :=
            Graph.connected_mono hsubset hconnA
          simpa [kruskal, hfalse] using hconnFinal
        · simpa [kruskal, hfalse] using ih A f hfes

/--
After an exact-component Kruskal pass, every processed edge has connected
endpoints in the final selected set.
-/
theorem processed_edge_connected_of_exact_component_kruskal
    {G : Graph V E} (C : ComponentOracle G)
    (hexact : ExactComponentOracle G C) (processed : List E)
    (A : Finset E) :
    ∀ f, f ∈ processed →
      G.ConnectedIn (kruskal (acceptByComponent G C) processed A)
        (G.src f) (G.dst f) := by
  intro f hf
  rcases processed_edge_mem_or_connected_of_exact_component_kruskal C hexact
      processed A f hf with hmem | hconn
  · exact Graph.connected_of_mem_edge hmem
  · exact hconn

/--
Exact components derive the processed-prefix exclusion invariant needed by the
sorted-order Kruskal lightness proof.
-/
theorem processed_prefix_excludes_of_exact_component_kruskal
    {G : Graph V E} (C : ComponentOracle G)
    (hexact : ExactComponentOracle G C) (processed : List E)
    (A : Finset E) (root : V) :
    ∀ f, f ∈ processed →
      ¬ G.Crosses
        (C.component (kruskal (acceptByComponent G C) processed A) root) f := by
  intro f hf
  exact not_crosses_component_of_mem_or_connected hexact
    (processed_edge_mem_or_connected_of_exact_component_kruskal C hexact
      processed A f hf)

/--
Kruskal's sorted edge order proves lightness without a standalone prefix
exclusion hypothesis when the component oracle is exact.
-/
theorem lightest_crossing_of_exact_component_kruskal_prefix
    {G : Graph V E} {w : E → Nat} (C : ComponentOracle G)
    (hexact : ExactComponentOracle G C)
    {processed suffix : List E} {A : Finset E} {e : E}
    (hsorted : WeightSorted w (processed ++ e :: suffix))
    (hall :
      ∀ f,
        G.Crosses
            (C.component (kruskal (acceptByComponent G C) processed A)
              (G.src e)) f →
          f ∈ processed ++ e :: suffix) :
    ∀ f,
      G.Crosses
          (C.component (kruskal (acceptByComponent G C) processed A)
            (G.src e)) f →
        w e ≤ w f := by
  exact lightest_crossing_of_sorted_prefix hsorted hall
    (processed_prefix_excludes_of_exact_component_kruskal C hexact
      processed A (G.src e))

/--
Exact-component cut certificate for the current Kruskal edge.  This packages
the derived processed-prefix exclusion invariant with the sorted edge order.
-/
theorem cut_certificate_of_exact_component_kruskal_prefix
    {G : Graph V E} {P : Problem E} {w : E → Nat} (C : ComponentOracle G)
    (hexact : ExactComponentOracle G C)
    {processed suffix : List E} {A : Finset E} {e : E}
    (haccept :
      acceptByComponent G C
          (kruskal (acceptByComponent G C) processed A) e = true)
    (hsorted : WeightSorted w (processed ++ e :: suffix))
    (hall :
      ∀ f,
        G.Crosses
            (C.component (kruskal (acceptByComponent G C) processed A)
              (G.src e)) f →
          f ∈ processed ++ e :: suffix)
    (hexchange :
      ∀ T,
        IsMSTExtending P w
            (kruskal (acceptByComponent G C) processed A) T →
          e ∉ T →
            ∃ f, f ∈ T ∧
              G.Crosses
                  (C.component
                    (kruskal (acceptByComponent G C) processed A)
                    (G.src e)) f ∧
                P.IsSpanningTree (insert e (T.erase f)) ∧
                kruskal (acceptByComponent G C) processed A ⊆
                  insert e (T.erase f)) :
    CutCertificate G P w
      (kruskal (acceptByComponent G C) processed A)
      (C.component (kruskal (acceptByComponent G C) processed A) (G.src e))
      e := by
  exact cut_certificate_of_component_oracle C haccept
    (lightest_crossing_of_exact_component_kruskal_prefix C hexact
      hsorted hall)
    hexchange

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
provide an {lit}`accept` function and prove that it agrees with the component oracle. -/
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

/-- A finite-graph Kruskal run selects only graph edges, provided the initial
set and scanned list contain only graph edges. -/
theorem kruskal_subset_edges (G : FiniteGraph V E)
    {accept : Finset E → E → Bool} (edges : List E) {A : Finset E}
    (hA : A ⊆ G.edges) (hedges : ∀ e, e ∈ edges → e ∈ G.edges) :
    kruskal accept edges A ⊆ G.edges :=
  CLRS.MST.kruskal_subset_of_start_and_edges accept edges hA hedges

/--
If the edge list contains every graph edge and the full graph is connected,
then an exact-component Kruskal pass spans the finite graph.
-/
theorem kruskal_spans_of_complete_exact_component (G : FiniteGraph V E)
    (C : ComponentOracle G.toGraph) (hexact : ExactComponentOracle G.toGraph C)
    (edges : List E) (A : Finset E)
    (hcomplete : ∀ e, e ∈ G.edges → e ∈ edges)
    (hconnected : G.Spans G.edges) :
    G.Spans (kruskal (acceptByComponent G.toGraph C) edges A) := by
  intro u hu v hv
  refine Graph.connected_of_edgewise_connected ?_ (hconnected u hu v hv)
  intro e heG
  exact processed_edge_connected_of_exact_component_kruskal C hexact edges A e
    (hcomplete e heG)

/--
The remaining final-tree side condition for exact-component Kruskal is now only
forest preservation: subset and spanning are derived from the complete edge
scan and graph connectedness assumptions.
-/
theorem kruskal_spanning_tree_of_complete_exact_component
    (G : FiniteGraph V E) (C : ComponentOracle G.toGraph)
    (hexact : ExactComponentOracle G.toGraph C) (edges : List E)
    {A : Finset E}
    (hA : A ⊆ G.edges) (hedges : ∀ e, e ∈ edges → e ∈ G.edges)
    (hcomplete : ∀ e, e ∈ G.edges → e ∈ edges)
    (hconnected : G.Spans G.edges)
    (hforest : G.IsForest (kruskal (acceptByComponent G.toGraph C) edges A)) :
    G.IsSpanningTree (kruskal (acceptByComponent G.toGraph C) edges A) := by
  exact ⟨G.kruskal_subset_edges edges hA hedges,
    G.kruskal_spans_of_complete_exact_component C hexact edges A hcomplete
      hconnected,
    hforest⟩

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
