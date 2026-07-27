import Mathlib
import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs

/-! # Section 22.3 - Depth-First Search

This section gives a functional depth-first-search procedure on the finite graph
model from Section 22.1 and proves a basic correctness invariant: after DFS,
every vertex of the graph is black.  Timestamps, parent pointers, and vertex
colors (white/gray/black) are represented as functions, so the algorithm is
noncomputable because it iterates over {lit}`Finset.toList`.

The white-path theorem and the discovery-state infrastructure built on this
model are proved in the companion {lit}`Section_22_3_DFS.S1_WhitePath` and
{lit}`Section_22_3_DFS.S2_Intervals` modules.  The latter also proves the timestamp
form of the parenthesis theorem.  The ancestor characterization and unique
tree/back/forward/cross classification are proved in the downstream companion
modules.

## Implementation details

The detailed DFS proof layers remain available outside the main sidebar:

* [White-Path Theorem](CLRSLean/Chapter_22/Section_22_3_DFS/S1_WhitePath/)
* [Intervals and Timestamps](CLRSLean/Chapter_22/Section_22_3_DFS/S2_Intervals/)
* [Discovery-State Bridge](CLRSLean/Chapter_22/Section_22_3_DFS/S3_Bridge/)
* [SCC Preliminaries](CLRSLean/Chapter_22/Section_22_3_DFS/S4_SCC/)
* [Edge Classification](CLRSLean/Chapter_22/Section_22_3_DFS/S5_EdgeClassification/)
-/

namespace CLRS
namespace Chapter22

namespace Graph

variable {V : Type} [DecidableEq V]

/-- Vertex colors used by DFS. -/
inductive Color where
  | white | gray | black
  deriving DecidableEq, Inhabited

/-- Mutable DFS state: colors, discovery/finish times, parents, and a global clock. -/
structure DFSState (V : Type) [DecidableEq V] where
  color : V → Color
  d : V → Option Nat
  f : V → Option Nat
  parent : V → Option V
  time : Nat
  deriving Inhabited

namespace DFSState

/-- Change the color of one vertex. -/
def setColor (s : DFSState V) (v : V) (c : Color) : DFSState V :=
  { s with color := fun x => if x = v then c else s.color x }

/-- Record the discovery time of {lit}`v` and advance the clock. -/
def setDiscovery (s : DFSState V) (v : V) : DFSState V :=
  { s with d := fun x => if x = v then some s.time else s.d x, time := s.time + 1 }

/-- Record the finish time of {lit}`v` and advance the clock. -/
def setFinish (s : DFSState V) (v : V) : DFSState V :=
  { s with f := fun x => if x = v then some s.time else s.f x, time := s.time + 1 }

/-- Set the parent of {lit}`v` to {lit}`u`. -/
def setParent (s : DFSState V) (v u : V) : DFSState V :=
  { s with parent := fun x => if x = v then some u else s.parent x }

@[simp]
theorem setColor_color (s : DFSState V) (v x : V) (c : Color) :
    (s.setColor v c).color x = if x = v then c else s.color x := rfl

@[simp]
theorem setDiscovery_color (s : DFSState V) (v x : V) :
    (s.setDiscovery v).color x = s.color x := rfl

@[simp]
theorem setFinish_color (s : DFSState V) (v x : V) :
    (s.setFinish v).color x = s.color x := rfl

@[simp]
theorem setParent_color (s : DFSState V) (v u x : V) :
    (s.setParent v u).color x = s.color x := rfl

@[simp]
theorem setColor_d (s : DFSState V) (v x : V) (c : Color) :
    (s.setColor v c).d x = s.d x := rfl

@[simp]
theorem setDiscovery_d (s : DFSState V) (v x : V) :
    (s.setDiscovery v).d x = if x = v then some s.time else s.d x := rfl

@[simp]
theorem setFinish_d (s : DFSState V) (v x : V) :
    (s.setFinish v).d x = s.d x := rfl

@[simp]
theorem setParent_d (s : DFSState V) (v u x : V) :
    (s.setParent v u).d x = s.d x := rfl

@[simp]
theorem setColor_f (s : DFSState V) (v x : V) (c : Color) :
    (s.setColor v c).f x = s.f x := rfl

@[simp]
theorem setDiscovery_f (s : DFSState V) (v x : V) :
    (s.setDiscovery v).f x = s.f x := rfl

@[simp]
theorem setFinish_f (s : DFSState V) (v x : V) :
    (s.setFinish v).f x = if x = v then some s.time else s.f x := rfl

@[simp]
theorem setParent_f (s : DFSState V) (v u x : V) :
    (s.setParent v u).f x = s.f x := rfl

@[simp]
theorem setColor_parent (s : DFSState V) (v x : V) (c : Color) :
    (s.setColor v c).parent x = s.parent x := rfl

@[simp]
theorem setDiscovery_parent (s : DFSState V) (v x : V) :
    (s.setDiscovery v).parent x = s.parent x := rfl

@[simp]
theorem setFinish_parent (s : DFSState V) (v x : V) :
    (s.setFinish v).parent x = s.parent x := rfl

@[simp]
theorem setParent_parent (s : DFSState V) (v u x : V) :
    (s.setParent v u).parent x = if x = v then some u else s.parent x := rfl

@[simp]
theorem setColor_time (s : DFSState V) (v : V) (c : Color) :
    (s.setColor v c).time = s.time := rfl

@[simp]
theorem setDiscovery_time (s : DFSState V) (v : V) :
    (s.setDiscovery v).time = s.time + 1 := rfl

@[simp]
theorem setFinish_time (s : DFSState V) (v : V) :
    (s.setFinish v).time = s.time + 1 := rfl

@[simp]
theorem setParent_time (s : DFSState V) (v u : V) :
    (s.setParent v u).time = s.time := rfl

end DFSState

variable (G : Graph V)

/-- One DFS tree visit from a white source vertex {lit}`u`. -/
noncomputable def dfsVisit (fuel : Nat) (u : V) (s : DFSState V) : DFSState V :=
  match fuel with
  | 0 => s
  | fuel + 1 =>
      if s.color u = Color.white then
        let s := s.setColor u Color.gray |>.setDiscovery u
        let s := (G.adj u).toList.foldl (fun s' v =>
          if s'.color v = Color.white then dfsVisit fuel v (s'.setParent v u) else s') s
        s.setColor u Color.black |>.setFinish u
      else
        s

/-- Initial DFS state: all vertices are white and no times/parents are set. -/
def dfsInit : DFSState V := {
  color := fun _ => Color.white,
  d := fun _ => none,
  f := fun _ => none,
  parent := fun _ => none,
  time := 0
}

/-- Recursive DFS over a list of starting vertices. -/
noncomputable def dfsFromList (fuel : Nat) : List V → DFSState V → DFSState V
  | [], s => s
  | u :: us, s =>
      let s' := if s.color u = Color.white then dfsVisit G fuel u s else s
      dfsFromList fuel us s'

/-- Depth-first search over the whole graph. -/
noncomputable def dfs (G : Graph V) : DFSState V :=
  dfsFromList G (G.vertices.card + 1) G.vertices.toList dfsInit

section BasicProperties

/-- A DFS visit from a white vertex turns that vertex black (if fuel is positive). -/
theorem dfsVisit_blackens_u {fuel : Nat} {u : V} {s : DFSState V}
    (hwhite : s.color u = Color.white) :
    (dfsVisit G (fuel + 1) u s).color u = Color.black := by
  simp [dfsVisit, hwhite]

/-- A DFS visit never turns a black vertex back to white or gray. -/
theorem dfsVisit_preserves_black {fuel : Nat} {u x : V} {s : DFSState V}
    (hblack : s.color x = Color.black) :
    (dfsVisit G fuel u s).color x = Color.black := by
  induction fuel generalizing u s with
  | zero => simp [dfsVisit]; exact hblack
  | succ n ih =>
      by_cases h : s.color u = Color.white
      · -- u is white: the visit processes it and its neighbors
        simp [dfsVisit, h]
        by_cases hxu : x = u
        · subst hxu
          simp
        · let s1 := s.setColor u Color.gray |>.setDiscovery u
          have h2 : ∀ (s1 : DFSState V), s1.color x = Color.black →
              ((G.adj u).toList.foldl (fun s' v =>
                if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s') s1).color x = Color.black := by
            intro s1 hs1x
            induction (G.adj u).toList generalizing s1 with
            | nil => simp [hs1x]
            | cons w ws ih' =>
                simp
                split_ifs with hw
                · have hsp : (s1.setParent w u).color x = Color.black := by simp [hs1x]
                  have hrec : (dfsVisit G n w (s1.setParent w u)).color x = Color.black :=
                    ih (u := w) (s := s1.setParent w u) hsp
                  exact ih' (dfsVisit G n w (s1.setParent w u)) hrec
                · exact ih' s1 hs1x
          have hs1x : s1.color x = Color.black := by
            simp [s1, hxu, hblack]
          simp [s1, hxu, h2 s1 hs1x]
      · -- u is not white: the visit returns the state unchanged
        simp [dfsVisit, h]
        exact hblack

/-- A DFS visit does not introduce new gray vertices.  The temporary gray on the
source vertex is removed before the call returns. -/
theorem dfsVisit_no_new_gray {fuel : Nat} {u : V} {s : DFSState V} (w : V) :
    (dfsVisit G fuel u s).color w = Color.gray → s.color w = Color.gray := by
  induction fuel generalizing u s with
  | zero => simp [dfsVisit]
  | succ n ih =>
      by_cases h : s.color u = Color.white
      · -- u is white: the visit processes it and its neighbors
        simp [dfsVisit, h]
        by_cases hwu : w = u
        · -- the final step turns u black, so u cannot be gray in the output
          subst hwu
          simp
        · let s1 := s.setColor u Color.gray |>.setDiscovery u
          let step := fun (s' : DFSState V) (v : V) =>
            if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s'
          have hfold : ∀ (s1 : DFSState V),
              ((G.adj u).toList.foldl step s1).color w = Color.gray → s1.color w = Color.gray := by
            intro s1
            induction (G.adj u).toList generalizing s1 with
            | nil => simp
            | cons v vs ih' =>
                intro hy
                by_cases hv : s1.color v = Color.white
                · -- v is white, so the fold first recurses into v
                  let s' := dfsVisit G n v (s1.setParent v u)
                  have hstep : step s1 v = s' := by simp [step, hv, s']
                  have hy' : (List.foldl step s' vs).color w = Color.gray := by
                    simp [List.foldl, hstep] at hy
                    exact hy
                  have hs' : s'.color w = Color.gray → s1.color w = Color.gray := by
                    intro hz
                    have hrec := ih (u := v) (s := s1.setParent v u) hz
                    simpa using hrec
                  exact hs' (ih' s' hy')
                · -- v is not white, the fold leaves the state unchanged on this step
                  have hstep : step s1 v = s1 := by simp [step, hv]
                  have hy' : (List.foldl step s1 vs).color w = Color.gray := by
                    simp [List.foldl, hstep] at hy
                    exact hy
                  exact ih' s1 hy'
          intro hw
          simp [if_neg hwu] at hw
          have h1 := hfold s1 hw
          simp [s1, hwu] at h1
          exact h1
      · -- u is not white: the visit returns the state unchanged
        intro hw
        simp [dfsVisit, h] at hw ⊢
        exact hw

/-- A DFS visit from a white input vertex leaves it white or turns it black,
never gray. -/
theorem dfsVisit_white_stays_white_or_black {fuel : Nat} {u x : V} {s : DFSState V}
    (hwhite : s.color x = Color.white) (hnblack : (dfsVisit G fuel u s).color x ≠ Color.black) :
    (dfsVisit G fuel u s).color x = Color.white := by
  have hng : (dfsVisit G fuel u s).color x ≠ Color.gray := by
    intro h
    have := dfsVisit_no_new_gray G x h
    simp [hwhite] at this
  cases hcolor : (dfsVisit G fuel u s).color x with
  | white => rfl
  | gray => contradiction
  | black => contradiction

/-- If the input has no gray vertices, the output of a DFS visit has no gray
vertices either. -/
theorem dfsVisit_output_no_gray {fuel : Nat} {u : V} {s : DFSState V}
    (h : ∀ w, s.color w = Color.white ∨ s.color w = Color.black) :
    ∀ w, (dfsVisit G fuel u s).color w = Color.white ∨ (dfsVisit G fuel u s).color w = Color.black := by
  intro w
  by_cases hgray : (dfsVisit G fuel u s).color w = Color.gray
  · have h' := dfsVisit_no_new_gray G w hgray
    have hw := h w
    simp [h'] at hw
  · cases h' : (dfsVisit G fuel u s).color w with
    | gray => contradiction
    | white => simp
    | black => simp

/-- Recursive DFS over a list preserves black vertices. -/
theorem dfsFromList_preserves_black (s0 : DFSState V) (fuel : Nat) (vs : List V) {x : V}
    (hblack : s0.color x = Color.black) :
    (dfsFromList G fuel vs s0).color x = Color.black := by
  induction vs generalizing s0 with
  | nil => simpa [dfsFromList] using hblack
  | cons u us ih =>
      simp [dfsFromList]
      split_ifs
      · exact ih (dfsVisit G fuel u s0) (dfsVisit_preserves_black G hblack)
      · exact ih s0 hblack

/-- A positive DFS visit from a white vertex turns that vertex black. -/
theorem dfsVisit_blackens_u_pos {fuel : Nat} {u : V} {s : DFSState V}
    (hfuel : 0 < fuel) (hwhite : s.color u = Color.white) :
    (dfsVisit G fuel u s).color u = Color.black := by
  cases fuel with
  | zero => linarith
  | succ n => exact dfsVisit_blackens_u G hwhite

/-- One step of the inner {lit}`dfsVisit` fold preserves black vertices. -/
theorem dfsVisit_fold_step_preserves_black {n : Nat} {u x w : V} {s1 : DFSState V}
    (hb : s1.color x = Color.black) :
    ((if s1.color w = Color.white then dfsVisit G n w (s1.setParent w u) else s1).color x = Color.black) := by
  split_ifs with hw
  · have hsp : (s1.setParent w u).color x = Color.black := by simp [hb]
    exact dfsVisit_preserves_black G hsp
  · exact hb

/-- The inner fold of a DFS visit preserves black vertices. -/
theorem dfsVisit_fold_preserves_black {n : Nat} {u x : V} {s1 : DFSState V} {l : List V}
    (hb : s1.color x = Color.black) :
    (l.foldl (fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1).color x = Color.black := by
  induction l generalizing s1 with
  | nil =>
      exact hb
  | cons w ws ih =>
      simp
      exact ih (dfsVisit_fold_step_preserves_black G hb)

/-- The inner fold of a DFS visit does not introduce new gray vertices. -/
theorem dfsVisit_fold_no_new_gray {n : Nat} {u w : V} (s1 : DFSState V) {l : List V} :
    (List.foldl (fun (s' : DFSState V) (v : V) =>
        if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s') s1 l).color w = Color.gray →
    s1.color w = Color.gray := by
  induction l generalizing s1 with
  | nil =>
      intro h
      exact h
  | cons v vs ih =>
      simp
      by_cases hv : s1.color v = Color.white
      · simp [hv]
        intro hw
        by_cases hwv : w = v
        · subst w
          have hnotgray : (dfsVisit G n v (s1.setParent v u)).color v ≠ Color.gray := by
            by_cases hb : (dfsVisit G n v (s1.setParent v u)).color v = Color.black
            · rw [hb]; decide
            · have hwhite : (dfsVisit G n v (s1.setParent v u)).color v = Color.white :=
                dfsVisit_white_stays_white_or_black G (by simpa using hv) hb
              rw [hwhite]; decide
          have hrec : (dfsVisit G n v (s1.setParent v u)).color v = Color.gray :=
            ih (dfsVisit G n v (s1.setParent v u)) hw
          contradiction
        · have hrec : (dfsVisit G n v (s1.setParent v u)).color w = Color.gray :=
            ih (dfsVisit G n v (s1.setParent v u)) hw
          have hsp : (s1.setParent v u).color w = Color.gray :=
            dfsVisit_no_new_gray G w hrec
          simpa [hwv] using hsp
      · simp [hv]
        exact ih s1

/-- Recursive DFS over a list blackens every listed vertex while preserving the
white/black (no gray) invariant. -/
theorem dfsFromList_all_black (s0 : DFSState V)
    (h0 : ∀ w, s0.color w = Color.white ∨ s0.color w = Color.black)
    {fuel : Nat} (hfuel : 0 < fuel) (vs : List V) :
    (∀ z ∈ vs, (dfsFromList G fuel vs s0).color z = Color.black) ∧
      (∀ w, (dfsFromList G fuel vs s0).color w = Color.white ∨
            (dfsFromList G fuel vs s0).color w = Color.black) := by
  induction vs generalizing s0
  · constructor
    · simp
    · intro w; exact h0 w
  · rename_i head us ih
    let s' := if s0.color head = Color.white then dfsVisit G fuel head s0 else s0
    have hng' : ∀ w, s'.color w = Color.white ∨ s'.color w = Color.black := by
      simp [s']
      split_ifs with hwhite
      · apply dfsVisit_output_no_gray
        intro w
        cases h0 w <;> simp [*]
      · intro w; cases h0 w <;> simp [*]
    have ⟨ih1, ih2⟩ := ih s' hng'
    constructor
    · intro y hy
      simp at hy
      rcases hy with (rfl | hy)
      · -- y is the head of the list
        simp [dfsFromList]
        split_ifs with hwhite
        · have hblack : (dfsVisit G fuel y s0).color y = Color.black := dfsVisit_blackens_u_pos G hfuel hwhite
          exact dfsFromList_preserves_black G (dfsVisit G fuel y s0) fuel us hblack
        · have hblack : s0.color y = Color.black := by
            cases h0 y <;> tauto
          exact dfsFromList_preserves_black G s0 fuel us hblack
      · exact ih1 y hy
    · exact ih2

/-- After {lit}`dfs`, every vertex of the graph is black. -/
theorem dfs_all_black {v : V} (hv : v ∈ G.vertices) :
    (G.dfs).color v = Color.black := by
  simp [dfs, dfsInit]
  have hfuel : 0 < G.vertices.card + 1 := by linarith [Finset.card_pos.mpr ⟨v, hv⟩]
  have hblack := (dfsFromList_all_black G dfsInit (by simp [dfsInit]) hfuel G.vertices.toList).1
  exact hblack v (by simp [hv])

/-! ## Timestamp invariants -/

section Timestamps

/-- A gray vertex that is not the source of a DFS visit remains gray. -/
theorem dfsVisit_preserves_gray {fuel : Nat} {u x : V} {s : DFSState V}
    (hx : s.color x = Color.gray) (hne : x ≠ u) :
    (dfsVisit G fuel u s).color x = Color.gray := by
  induction fuel generalizing u x s with
  | zero => simp [dfsVisit]; exact hx
  | succ n ih =>
      simp [dfsVisit]
      split_ifs with hwhite
      · let s1 := s.setColor u Color.gray |>.setDiscovery u
        let s2 := List.foldl (fun (s' : DFSState V) (v : V) =>
            if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s') s1 (G.adj u).toList
        let s3 := s2.setColor u Color.black |>.setFinish u
        have hx1 : s1.color x = Color.gray := by
          simp [s1, hx, hne]
        have hx2 : s2.color x = Color.gray := by
          have hfold : ∀ (l : List V) (s' : DFSState V),
              s'.color x = Color.gray →
              (List.foldl (fun (s'' : DFSState V) (v : V) =>
                  if s''.color v = Color.white then dfsVisit G n v (s''.setParent v u) else s'') s' l).color x = Color.gray := by
            intro l s' hs'
            induction l generalizing s' with
            | nil => simpa
            | cons v vs ih' =>
                simp
                by_cases hv : s'.color v = Color.white
                · simp [hv]
                  apply ih' (dfsVisit G n v (s'.setParent v u))
                  have hsp : (s'.setParent v u).color x = Color.gray := by simp [hs']
                  have hne' : x ≠ v := by
                    intro h
                    subst x
                    simp [hs'] at hv
                  exact ih hsp hne'
                · simp [hv]
                  exact ih' s' hs'
          exact hfold (G.adj u).toList s1 hx1
        have : s3.color x = Color.gray := by
          simp [s3, hx2, hne]
        exact this
      · exact hx

/-- During a DFS visit, the source vertex stays gray until the final blackening
step. -/
theorem dfsVisit_u_stays_gray {fuel : Nat} {u : V} {s : DFSState V}
    (hfuel : 0 < fuel) (hwhite : s.color u = Color.white) :
    let s1 := s.setColor u Color.gray |>.setDiscovery u
    let s2 := List.foldl (fun (s' : DFSState V) (v : V) =>
        if s'.color v = Color.white then dfsVisit G (fuel - 1) v (s'.setParent v u) else s') s1 (G.adj u).toList
    s2.color u = Color.gray := by
  cases fuel with
  | zero => linarith
  | succ n =>
      let s1 := s.setColor u Color.gray |>.setDiscovery u
      have h1 : s1.color u = Color.gray := by simp [s1]
      have hfold : ∀ (l : List V) (s' : DFSState V),
          s'.color u = Color.gray →
          (List.foldl (fun (s'' : DFSState V) (v : V) =>
              if s''.color v = Color.white then dfsVisit G n v (s''.setParent v u) else s'') s' l).color u = Color.gray := by
        intro l s' hs'
        induction l generalizing s' with
        | nil => simpa
        | cons v vs ih' =>
            simp
            by_cases hv : s'.color v = Color.white
            · simp [hv]
              apply ih' (dfsVisit G n v (s'.setParent v u))
              have hsp : (s'.setParent v u).color u = Color.gray := by simp [hs']
              have hne : u ≠ v := by
                intro h
                subst u
                simp [hs'] at hv
              exact dfsVisit_preserves_gray G hsp hne
            · simp [hv]
              exact ih' s' hs'
      exact hfold (G.adj u).toList s1 h1

/-- The discovery time of {lit}`v` in {lit}`s`, defaulting to {lit}`0` if it has
not been set. -/
def discoveryTime (s : DFSState V) (v : V) : Nat := (s.d v).getD 0

/-- The finish time of {lit}`v` in {lit}`s`, defaulting to {lit}`0` if it has
not been set. -/
def finishTime (s : DFSState V) (v : V) : Nat := (s.f v).getD 0

/-- Timestamp invariant: colors are white/gray/black, every non-white vertex has
a discovery time, and every black vertex has a finish time. -/
def TimestampInvariant (s : DFSState V) : Prop :=
  (∀ v, s.color v = Color.white ∨ s.color v = Color.gray ∨ s.color v = Color.black) ∧
  (∀ v, s.color v ≠ Color.white → s.d v ≠ none) ∧
  (∀ v, s.color v = Color.black → s.f v ≠ none)

theorem TimestampInvariant_init : TimestampInvariant (dfsInit : DFSState V) := by
  simp [TimestampInvariant, dfsInit]

theorem setColor_white_preserves_TimestampInvariant {s : DFSState V} {v : V}
    (hinv : TimestampInvariant s) :
    TimestampInvariant (s.setColor v Color.white) := by
  rcases hinv with ⟨hng, hd, hf⟩
  constructor
  · intro w
    by_cases heq : w = v
    · simp [heq]
    · simp [heq]
      exact hng w
  constructor
  · intro w h
    by_cases heq : w = v
    · simp [heq] at h
    · simp [heq] at h ⊢
      exact hd w h
  · intro w h
    by_cases heq : w = v
    · simp [heq] at h
    · simp [heq] at h ⊢
      exact hf w h

/-- Graying a vertex and recording its discovery time preserves the invariant. -/
theorem grayAndDiscover_preserves_TimestampInvariant {s : DFSState V} {v : V}
    (hinv : TimestampInvariant s) :
    TimestampInvariant ((s.setColor v Color.gray).setDiscovery v) := by
  rcases hinv with ⟨hng, hd, hf⟩
  constructor
  · intro w
    by_cases heq : w = v
    · simp [heq]
    · simp [heq]
      exact hng w
  constructor
  · intro w h
    by_cases heq : w = v
    · simp [heq]
    · simp [heq] at h ⊢
      exact hd w h
  · intro w h
    by_cases heq : w = v
    · simp [heq] at h
    · simp [heq] at h ⊢
      exact hf w h

/-- Blackening a vertex and recording its finish time preserves the invariant. -/
theorem blackAndFinish_preserves_TimestampInvariant {s : DFSState V} {v : V}
    (hinv : TimestampInvariant s) (hgray : s.color v = Color.gray) :
    TimestampInvariant ((s.setColor v Color.black).setFinish v) := by
  rcases hinv with ⟨hng, hd, hf⟩
  constructor
  · intro w
    by_cases heq : w = v
    · simp [heq]
    · simp [heq]
      exact hng w
  constructor
  · intro w h
    by_cases heq : w = v
    · simp [heq]
      exact hd v (by simp [hgray])
    · simp [heq] at h ⊢
      exact hd w h
  · intro w h
    by_cases heq : w = v
    · simp [heq]
    · simp [heq] at h ⊢
      exact hf w h

theorem setParent_preserves_TimestampInvariant {s : DFSState V} {v p : V}
    (hinv : TimestampInvariant s) :
    TimestampInvariant (s.setParent v p) := by
  rcases hinv with ⟨hng, hd, hf⟩
  simp [TimestampInvariant]
  exact ⟨hng, hd, hf⟩

/-- A DFS visit from a white vertex preserves the timestamp invariant. -/
theorem dfsVisit_preserves_TimestampInvariant {fuel : Nat} {u : V} {s : DFSState V}
    (hfuel : 0 < fuel) (hinv : TimestampInvariant s) (hwhite : s.color u = Color.white) :
    TimestampInvariant (dfsVisit G fuel u s) := by
  induction fuel generalizing u s hinv hwhite with
  | zero => linarith
  | succ n ih =>
      simp [dfsVisit, hwhite]
      let s1 := s.setColor u Color.gray |>.setDiscovery u
      have hinv1 : TimestampInvariant s1 := grayAndDiscover_preserves_TimestampInvariant hinv
      let s2 := List.foldl (fun (s' : DFSState V) (v : V) =>
          if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s') s1 (G.adj u).toList
      have hinv2 : TimestampInvariant s2 := by
        have step : ∀ (s' : DFSState V) (x : V),
            TimestampInvariant s' → s'.color x = Color.white →
            TimestampInvariant (dfsVisit G n x (s'.setParent x u)) := by
          intro s' x hinv' hx
          by_cases hn0 : n = 0
          · simp [hn0, dfsVisit]
            exact setParent_preserves_TimestampInvariant hinv'
          · exact @ih x (s'.setParent x u) (by omega) (setParent_preserves_TimestampInvariant hinv') hx
        have hfold : ∀ (l : List V) (s' : DFSState V),
            TimestampInvariant s' →
            TimestampInvariant (List.foldl (fun (s'' : DFSState V) (v : V) =>
                if s''.color v = Color.white then dfsVisit G n v (s''.setParent v u) else s'') s' l) := by
          intro l s' hs'
          induction l generalizing s' with
          | nil => simpa using hs'
          | cons v vs ih' =>
              simp
              by_cases hv : s'.color v = Color.white
              · simp [hv]
                exact ih' (dfsVisit G n v (s'.setParent v u)) (step s' v hs' hv)
              · simp [hv]
                exact ih' s' hs'
        exact hfold (G.adj u).toList s1 hinv1
      have hgray : s2.color u = Color.gray := by
        apply dfsVisit_u_stays_gray G hfuel hwhite
      exact blackAndFinish_preserves_TimestampInvariant hinv2 hgray

/-- Recursive DFS over a list preserves the timestamp invariant. -/
theorem dfsFromList_preserves_TimestampInvariant {fuel : Nat} {s0 : DFSState V} {vs : List V}
    (hfuel : 0 < fuel) (hinv : TimestampInvariant s0) :
    TimestampInvariant (dfsFromList G fuel vs s0) := by
  induction vs generalizing s0
  · simpa [dfsFromList]
  · rename_i u us ih
    simp [dfsFromList]
    split_ifs with hwhite
    · exact ih (dfsVisit_preserves_TimestampInvariant G hfuel hinv hwhite)
    · exact ih hinv

/-- After {lit}`dfs`, every vertex has a defined discovery time. -/
theorem dfs_d_defined {v : V} (hv : v ∈ G.vertices) :
    (G.dfs).d v ≠ none := by
  have hfuel : 0 < G.vertices.card + 1 := by linarith [Finset.card_pos.mpr ⟨v, hv⟩]
  have hinv : TimestampInvariant G.dfs :=
    dfsFromList_preserves_TimestampInvariant G hfuel TimestampInvariant_init
  rcases hinv with ⟨_, hd, _⟩
  have hblack := G.dfs_all_black hv
  have hne : (G.dfs).color v ≠ Color.white := by simp [hblack]
  exact hd v hne

/-- After {lit}`dfs`, every vertex has a defined finish time. -/
theorem dfs_f_defined {v : V} (hv : v ∈ G.vertices) :
    (G.dfs).f v ≠ none := by
  have hfuel : 0 < G.vertices.card + 1 := by linarith [Finset.card_pos.mpr ⟨v, hv⟩]
  have hinv : TimestampInvariant G.dfs :=
    dfsFromList_preserves_TimestampInvariant G hfuel TimestampInvariant_init
  rcases hinv with ⟨_, _, hf⟩
  exact hf v (G.dfs_all_black hv)

/-- A DFS visit from {lit}`u` does not change the color of a vertex {lit}`v`
that is not white at the start and is not the source {lit}`u`. -/
theorem dfsVisit_preserves_not_white {fuel : Nat} {u v : V} {s : DFSState V}
    (hne : v ≠ u) (hnw : s.color v ≠ Color.white) :
    (dfsVisit G fuel u s).color v ≠ Color.white := by
  cases hcol : s.color v with
  | white => contradiction
  | gray =>
      have hgray := dfsVisit_preserves_gray (fuel := fuel) G hcol hne
      intro h
      rw [hgray] at h
      contradiction
  | black =>
      have hblack := dfsVisit_preserves_black (fuel := fuel) (u := u) G hcol
      intro h
      rw [hblack] at h
      contradiction

/-- The inner fold of a DFS visit never turns a non-white, non-source vertex
white. -/
theorem dfsVisit_fold_preserves_not_white {n : Nat} {u v : V} (s1 : DFSState V) {l : List V}
    (hne : v ≠ u) (hnw : s1.color v ≠ Color.white) :
    (List.foldl (fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 l).color v ≠ Color.white := by
  induction l generalizing s1 with
  | nil => simpa
  | cons w ws ih =>
      simp
      by_cases hw : s1.color w = Color.white
      · simp [hw]
        have hne' : v ≠ w := by
          intro h
          subst v
          contradiction
        have hnw' : (s1.setParent w u).color v ≠ Color.white := by
          simpa using hnw
        have hrec_nw := dfsVisit_preserves_not_white (fuel := n) G hne' hnw'
        exact ih (dfsVisit G n w (s1.setParent w u)) hrec_nw
      · simp [hw]
        exact ih s1 hnw


theorem dfsVisit_preserves_f_of_not_white {fuel : Nat} {u v : V} {s : DFSState V}
    (hne : v ≠ u) (hnw : s.color v ≠ Color.white) :
    (dfsVisit G fuel u s).f v = s.f v := by
  induction fuel generalizing u s with
  | zero => simp [dfsVisit]
  | succ n ih =>
      by_cases hwhite : s.color u = Color.white
      · let s1 := s.setColor u Color.gray |>.setDiscovery u
        let s2 := List.foldl (fun (s' : DFSState V) (w : V) =>
            if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 (G.adj u).toList
        let s3 := s2.setColor u Color.black |>.setFinish u
        have h_eq : (dfsVisit G (n + 1) u s).f v = s3.f v := by
          simp [dfsVisit, hwhite, s1, s2, s3]
        rw [h_eq]
        have h1 : s1.f v = s.f v := by simp [s1]
        have h2 : s2.f v = s1.f v := by
          have hfold : ∀ (l : List V) (s' : DFSState V),
              s'.f v = s1.f v ∧ s'.color v ≠ Color.white →
              (List.foldl (fun (s'' : DFSState V) (w : V) =>
                  if s''.color w = Color.white then dfsVisit G n w (s''.setParent w u) else s'') s' l).f v = s1.f v := by
            intro l s' hs'
            induction l generalizing s' with
            | nil => simpa using hs'.1
            | cons w ws ih' =>
                simp
                by_cases hw : s'.color w = Color.white
                · simp [hw]
                  apply ih'
                  constructor
                  · have hsp : (s'.setParent w u).f v = s'.f v := by simp
                    have hnw' : (s'.setParent w u).color v ≠ Color.white := by
                      simpa using hs'.2
                    have hne' : v ≠ w := by
                      by_contra h
                      rw [h] at hs'
                      exact hs'.2 hw
                    have hrec : (dfsVisit G n w (s'.setParent w u)).f v = (s'.setParent w u).f v :=
                      ih (u := w) (s := s'.setParent w u) hne' hnw'
                    rw [hrec, hsp]
                    exact hs'.1
                  · have hne' : v ≠ w := by
                      by_contra h
                      rw [h] at hs'
                      exact hs'.2 hw
                    have hnw' : (s'.setParent w u).color v ≠ Color.white := by
                      simpa using hs'.2
                    exact dfsVisit_preserves_not_white (fuel := n) G hne' hnw'
                · simp [hw]
                  exact ih' s' hs'
          have hs1 : s1.f v = s1.f v ∧ s1.color v ≠ Color.white := by
            constructor
            · rfl
            · simpa [s1, hne] using hnw
          exact hfold (G.adj u).toList s1 hs1
        have h3 : s3.f v = s2.f v := by
          simp [s3, hne]
        rw [h3, h2, h1]
      · simp [dfsVisit, hwhite]

/-- A DFS visit never moves the global clock backwards. -/
theorem dfsVisit_time_ge {fuel : Nat} {u : V} {s : DFSState V} :
    (dfsVisit G fuel u s).time ≥ s.time := by
  induction fuel generalizing u s with
  | zero => simp [dfsVisit]
  | succ n ih =>
      by_cases hwhite : s.color u = Color.white
      · simp [dfsVisit, hwhite]
        let s1 := s.setColor u Color.gray |>.setDiscovery u
        let s2 := List.foldl (fun (s' : DFSState V) (v : V) =>
            if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s') s1 (G.adj u).toList
        have hfold : s2.time ≥ s1.time := by
          have step : ∀ (s' : DFSState V) (v : V),
              (if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s').time ≥ s'.time := by
            intro s' v
            by_cases hv : s'.color v = Color.white
            · simp [hv]
              have h1 := ih (u := v) (s := s'.setParent v u)
              simp at h1 ⊢
              linarith
            · simp [hv]
          have : ∀ (l : List V) (s' : DFSState V),
              (List.foldl (fun (s'' : DFSState V) (v : V) =>
                  if s''.color v = Color.white then dfsVisit G n v (s''.setParent v u) else s'') s' l).time ≥ s'.time := by
            intro l s'
            induction l generalizing s' with
            | nil => simp
            | cons v vs ih' =>
                simp
                have hstep := step s' v
                have hfold := ih' (if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s')
                linarith
          exact this (G.adj u).toList s1
        have hs1 : s1.time = s.time + 1 := by simp [s1]
        have hs3 : (s2.setColor u Color.black |>.setFinish u).time = s2.time + 1 := by simp
        linarith
      · simp [dfsVisit, hwhite]

/-- The inner fold of a DFS visit never moves the global clock backwards. -/
theorem dfsVisit_fold_time_ge {n : Nat} {u : V} (s1 : DFSState V) {l : List V} :
    (List.foldl (fun (s' : DFSState V) (v : V) =>
        if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s') s1 l).time ≥ s1.time := by
  induction l generalizing s1 with
  | nil => simp
  | cons v vs ih =>
      simp
      by_cases hv : s1.color v = Color.white
      · simp [hv]
        have h1 := G.dfsVisit_time_ge (fuel := n) (u := v) (s := s1.setParent v u)
        simp at h1
        linarith [ih (dfsVisit G n v (s1.setParent v u))]
      · simp [hv]
        exact ih s1

/-- A DFS visit's source finishes strictly before the visit returns, i.e. before
the global clock after the visit. -/
theorem dfsVisit_source_finish_lt_time {fuel : Nat} {u : V} {s : DFSState V}
    (hfuel : 0 < fuel) (hwhite : s.color u = Color.white) :
    finishTime (dfsVisit G fuel u s) u < (dfsVisit G fuel u s).time := by
  cases fuel with
  | zero => linarith
  | succ n =>
      simp [dfsVisit, hwhite]
      let s1 := s.setColor u Color.gray |>.setDiscovery u
      let s2 := List.foldl (fun (s' : DFSState V) (v : V) =>
          if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s') s1 (G.adj u).toList
      let s3 := s2.setColor u Color.black |>.setFinish u
      simp [finishTime]

/-- A DFS visit preserves the discovery time of a vertex that is not white and
not its source. -/
theorem dfsVisit_preserves_d_of_not_white {fuel : Nat} {u v : V} {s : DFSState V}
    (hne : v ≠ u) (hnw : s.color v ≠ Color.white) :
    (dfsVisit G fuel u s).d v = s.d v := by
  induction fuel generalizing u s with
  | zero => simp [dfsVisit]
  | succ n ih =>
      by_cases hwhite : s.color u = Color.white
      · let s1 := s.setColor u Color.gray |>.setDiscovery u
        let s2 := List.foldl (fun (s' : DFSState V) (w : V) =>
            if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 (G.adj u).toList
        let s3 := s2.setColor u Color.black |>.setFinish u
        have h_eq : (dfsVisit G (n + 1) u s).d v = s3.d v := by
          simp [dfsVisit, hwhite, s1, s2, s3]
        rw [h_eq]
        have h1 : s1.d v = s.d v := by simp [s1, hne]
        have h2 : s2.d v = s1.d v := by
          have hfold : ∀ (l : List V) (s' : DFSState V),
              s'.d v = s1.d v ∧ s'.color v ≠ Color.white →
              (List.foldl (fun (s'' : DFSState V) (w : V) =>
                  if s''.color w = Color.white then dfsVisit G n w (s''.setParent w u) else s'') s' l).d v = s1.d v := by
            intro l s' hs'
            induction l generalizing s' with
            | nil => simpa using hs'.1
            | cons w ws ih' =>
                simp
                by_cases hw : s'.color w = Color.white
                · simp [hw]
                  apply ih'
                  constructor
                  · have hsp : (s'.setParent w u).d v = s'.d v := by simp
                    have hnw' : (s'.setParent w u).color v ≠ Color.white := by
                      simpa using hs'.2
                    have hne' : v ≠ w := by
                      by_contra h
                      rw [h] at hs'
                      exact hs'.2 hw
                    have hrec : (dfsVisit G n w (s'.setParent w u)).d v = (s'.setParent w u).d v :=
                      ih (u := w) (s := s'.setParent w u) hne' hnw'
                    rw [hrec, hsp]
                    exact hs'.1
                  · have hne' : v ≠ w := by
                      by_contra h
                      rw [h] at hs'
                      exact hs'.2 hw
                    have hnw' : (s'.setParent w u).color v ≠ Color.white := by
                      simpa using hs'.2
                    exact dfsVisit_preserves_not_white (fuel := n) G hne' hnw'
                · simp [hw]
                  exact ih' s' hs'
          have hs1 : s1.d v = s1.d v ∧ s1.color v ≠ Color.white := by
            constructor
            · rfl
            · simpa [s1, hne] using hnw
          exact hfold (G.adj u).toList s1 hs1
        have h3 : s3.d v = s2.d v := by
          simp [s3]
        rw [h3, h2, h1]
      · simp [dfsVisit, hwhite]

/-- The inner fold of a DFS visit preserves the discovery time of any vertex
that is not white at the start of the fold. -/
theorem dfsVisit_fold_preserves_d_of_not_white {n : Nat} {u v : V} (s1 : DFSState V) {l : List V}
    (hnw : s1.color v ≠ Color.white) :
    (List.foldl (fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 l).d v = s1.d v := by
  induction l generalizing s1 with
  | nil => simp
  | cons w ws ih =>
      simp
      by_cases hw : s1.color w = Color.white
      · simp [hw]
        have hne : v ≠ w := by
          intro h
          rw [h] at hnw
          simp [hw] at hnw
        have hsp : (s1.setParent w u).d v = s1.d v := by simp
        have hnw' : (s1.setParent w u).color v ≠ Color.white := by simpa using hnw
        have hrec : (dfsVisit G n w (s1.setParent w u)).d v = (s1.setParent w u).d v :=
          G.dfsVisit_preserves_d_of_not_white hne hnw'
        have hfold := ih (dfsVisit G n w (s1.setParent w u))
          (dfsVisit_preserves_not_white (fuel := n) G hne hnw')
        rw [hfold, hrec, hsp]
      · simp [hw]
        exact ih s1 hnw

/-- The inner fold of a DFS visit preserves the finish time of any vertex that is
not white at the start of the fold. -/
theorem dfsVisit_fold_preserves_f_of_not_white {n : Nat} {u v : V} (s1 : DFSState V) {l : List V}
    (hnw : s1.color v ≠ Color.white) :
    (List.foldl (fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 l).f v = s1.f v := by
  induction l generalizing s1 with
  | nil => simp
  | cons w ws ih =>
      simp
      by_cases hw : s1.color w = Color.white
      · simp [hw]
        have hne : v ≠ w := by
          intro h
          rw [h] at hnw
          simp [hw] at hnw
        have hsp : (s1.setParent w u).f v = s1.f v := by simp
        have hnw' : (s1.setParent w u).color v ≠ Color.white := by simpa using hnw
        have hrec : (dfsVisit G n w (s1.setParent w u)).f v = (s1.setParent w u).f v :=
          G.dfsVisit_preserves_f_of_not_white hne hnw'
        have hfold := ih (dfsVisit G n w (s1.setParent w u))
          (dfsVisit_preserves_not_white (fuel := n) G hne hnw')
        rw [hfold, hrec, hsp]
      · simp [hw]
        exact ih s1 hnw

/-- The inner fold of a DFS visit preserves the discovery time of any already-black
vertex. -/
theorem dfsVisit_fold_preserves_d_of_black {n : Nat} {u v : V} (s1 : DFSState V) {l : List V}
    (hb : s1.color v = Color.black) :
    (List.foldl (fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 l).d v = s1.d v := by
  induction l generalizing s1 with
  | nil => simp
  | cons w ws ih =>
      simp
      by_cases hw : s1.color w = Color.white
      · simp [hw]
        have hne : v ≠ w := by
          intro h
          rw [h] at hb
          simp [hw] at hb
        have hblack' : (s1.setParent w u).color v = Color.black := by simp [hb]
        have hnw : (s1.setParent w u).color v ≠ Color.white := by
          rw [hblack']
          decide
        have hsp : (s1.setParent w u).d v = s1.d v := by simp
        have hrec_d : (dfsVisit G n w (s1.setParent w u)).d v = (s1.setParent w u).d v :=
          G.dfsVisit_preserves_d_of_not_white hne hnw
        have hfold :
            (List.foldl (fun (s' : DFSState V) (w : V) =>
                if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s')
              (dfsVisit G n w (s1.setParent w u)) ws).d v = (dfsVisit G n w (s1.setParent w u)).d v :=
          ih (dfsVisit G n w (s1.setParent w u)) (G.dfsVisit_preserves_black hblack')
        rw [hfold, hrec_d, hsp]
      · simp [hw]
        exact ih s1 hb

/-- The inner fold of a DFS visit preserves the finish time of any already-black
vertex. -/
theorem dfsVisit_fold_preserves_f_of_black {n : Nat} {u v : V} (s1 : DFSState V) {l : List V}
    (hb : s1.color v = Color.black) :
    (List.foldl (fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 l).f v = s1.f v := by
  induction l generalizing s1 with
  | nil => simp
  | cons w ws ih =>
      simp
      by_cases hw : s1.color w = Color.white
      · simp [hw]
        have hne : v ≠ w := by
          intro h
          rw [h] at hb
          simp [hw] at hb
        have hblack' : (s1.setParent w u).color v = Color.black := by simp [hb]
        have hrec_black : (dfsVisit G n w (s1.setParent w u)).color v = Color.black :=
          G.dfsVisit_preserves_black hblack'
        have hnw : (s1.setParent w u).color v ≠ Color.white := by
          rw [hblack']
          decide
        have hsp : (s1.setParent w u).f v = s1.f v := by simp
        have hrec_f : (dfsVisit G n w (s1.setParent w u)).f v = (s1.setParent w u).f v :=
          G.dfsVisit_preserves_f_of_not_white hne hnw
        have hfold :
            (List.foldl (fun (s' : DFSState V) (w : V) =>
                if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s')
              (dfsVisit G n w (s1.setParent w u)) ws).f v =
              (dfsVisit G n w (s1.setParent w u)).f v :=
          ih (dfsVisit G n w (s1.setParent w u)) hrec_black
        rw [hfold, hrec_f, hsp]
      · simp [hw]
        exact ih s1 hb

/-- A DFS visit preserves the invariant that every parent edge points to a graph
neighbor of the child. -/
theorem dfsVisit_preserves_parent_edge {fuel : Nat} {u : V} {s : DFSState V}
    (hinv : ∀ x y, s.parent y = some x → G.Adj x y) :
    ∀ x y, (dfsVisit G fuel u s).parent y = some x →
      G.Adj x y := by
  induction fuel generalizing u s with
  | zero =>
      simpa [dfsVisit] using hinv
  | succ n ih =>
      by_cases hwhite : s.color u = Color.white
      · simp [dfsVisit, hwhite]
        let s1 := s.setColor u Color.gray |>.setDiscovery u
        let step := fun (s' : DFSState V) (w : V) =>
          if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s'
        have hinv_s1 : ∀ x y, s1.parent y = some x → G.Adj x y := by
          intro x y hparent
          exact hinv x y (by simpa [s1] using hparent)
        have hfold : ∀ (l : List V) (s' : DFSState V),
            (∀ w ∈ l, G.Adj u w) →
            (∀ x y, s'.parent y = some x → G.Adj x y) →
            ∀ x y, (List.foldl step s' l).parent y = some x → G.Adj x y := by
          intro l
          induction l with
          | nil =>
              intro s' _ hinv' x y hparent
              simpa [step] using hinv' x y hparent
          | cons w ws ih_ws =>
              intro s' hadj hinv' x y hparent
              have hw_adj : G.Adj u w := hadj w (by simp)
              have hws_adj : ∀ z ∈ ws, G.Adj u z := by
                intro z hz
                exact hadj z (by simp [hz])
              dsimp [step] at hparent
              by_cases hw : s'.color w = Color.white
              · rw [if_pos hw] at hparent
                have hinv_parent : ∀ x y, (s'.setParent w u).parent y = some x → G.Adj x y := by
                  intro x y hpy
                  by_cases hy : y = w
                  · subst y
                    simp at hpy
                    cases hpy
                    exact hw_adj
                  · have h_old : s'.parent y = some x := by
                      simpa [hy] using hpy
                    exact hinv' x y h_old
                exact ih_ws (dfsVisit G n w (s'.setParent w u)) hws_adj
                  (ih (u := w) (s := s'.setParent w u) hinv_parent) x y hparent
              · rw [if_neg hw] at hparent
                exact ih_ws s' hws_adj hinv' x y hparent
        have h_adj_list : ∀ w ∈ (G.adj u).toList, G.Adj u w := by
          intro w hw
          simpa [Adj] using (Finset.mem_toList.mp hw)
        exact hfold (G.adj u).toList s1 h_adj_list hinv_s1
      · simpa [dfsVisit, hwhite] using hinv

/-- In a state produced by DFS, every black vertex finished strictly before the
current clock value. -/
theorem dfsVisit_black_finish_lt_time {fuel : Nat} {u : V} {s : DFSState V}
    (hfuel : 0 < fuel) (hwhite : s.color u = Color.white)
    (hinv : ∀ v, s.color v = Color.black → finishTime s v < s.time) :
    ∀ v, (dfsVisit G fuel u s).color v = Color.black →
      finishTime (dfsVisit G fuel u s) v < (dfsVisit G fuel u s).time := by
  induction fuel generalizing u s hinv with
  | zero => linarith
  | succ n ih =>
      simp [dfsVisit, hwhite]
      let s1 := s.setColor u Color.gray |>.setDiscovery u
      let s2 := List.foldl (fun (s' : DFSState V) (v : V) =>
          if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s') s1 (G.adj u).toList
      let s3 := s2.setColor u Color.black |>.setFinish u
      have htime_s3 : s3.time > s.time := by
        have hs1 : s1.time = s.time + 1 := by simp [s1]
        have hs2 : s2.time ≥ s1.time := G.dfsVisit_fold_time_ge s1
        have hs3 : s3.time = s2.time + 1 := by simp [s3]
        linarith
      have hblack_s : ∀ v, s.color v = Color.black → finishTime s3 v < s3.time := by
        intro v hv
        have hne : v ≠ u := by
          intro heq
          rw [heq] at hv
          simp [hwhite] at hv
        have h2 : finishTime s3 v = finishTime s v := by
          have h3 : s3.f v = s.f v := by
            have h4 : (dfsVisit G (n + 1) u s).f v = s.f v :=
              dfsVisit_preserves_f_of_not_white G hne (by simp [hv])
            have h5 : dfsVisit G (n + 1) u s = s3 := by
              simp [dfsVisit, hwhite, s1, s2, s3]
            rw [h5] at h4
            exact h4
          simp [finishTime, h3]
        linarith [hinv v hv, htime_s3]
      have hsource : finishTime s3 u < s3.time := by
        have hfu : s3.f u = some s2.time := by simp [s3]
        have htime : s3.time = s2.time + 1 := by simp [s3]
        simp [finishTime, hfu]
        linarith [htime]
      have hfold : ∀ v, s2.color v = Color.black → finishTime s2 v < s2.time := by
        have fold_inv : ∀ (l : List V) (s' : DFSState V),
            (∀ v, s'.color v = Color.black → finishTime s' v < s'.time) →
            ∀ v, (List.foldl (fun (s'' : DFSState V) (v : V) =>
                if s''.color v = Color.white then dfsVisit G n v (s''.setParent v u) else s'') s' l).color v = Color.black →
              finishTime (List.foldl (fun (s'' : DFSState V) (v : V) =>
                  if s''.color v = Color.white then dfsVisit G n v (s''.setParent v u) else s'') s' l) v
                < (List.foldl (fun (s'' : DFSState V) (v : V) =>
                    if s''.color v = Color.white then dfsVisit G n v (s''.setParent v u) else s'') s' l).time := by
          intro l s' hs'
          induction l generalizing s' with
          | nil => simpa using hs'
          | cons w ws ih' =>
              simp
              by_cases hw : s'.color w = Color.white
              · simp [hw]
                let s0 := s'.setParent w u
                let s_rec := dfsVisit G n w s0
                have hsp : ∀ v, s0.color v = Color.black ↔ s'.color v = Color.black := by
                  intro v; simp [s0]
                have hsp_inv : ∀ v, s0.color v = Color.black → finishTime s0 v < s0.time := by
                  intro v hv
                  have hv' : s'.color v = Color.black := by
                    simpa [s0] using hv
                  have h1 : finishTime s0 v = finishTime s' v := by
                    simp [finishTime, s0]
                  have h2 : s0.time = s'.time := by
                    simp [s0]
                  rw [h1, h2]
                  exact hs' v hv'
                have hrec : ∀ v, s_rec.color v = Color.black → finishTime s_rec v < s_rec.time := by
                  intro v hv
                  by_cases hn0 : n = 0
                  · -- n = 0, the recursive call returns s0 unchanged
                    have h_eq : s_rec = s0 := by
                      simp [s_rec, s0, hn0, dfsVisit]
                    rw [h_eq] at hv ⊢
                    exact hsp_inv v hv
                  · -- n > 0
                    apply ih (u := w) (s := s0) (by omega) (by simpa [s0] using hw) hsp_inv v hv
                exact ih' s_rec hrec
              · simp [hw]
                exact ih' s' hs'
        have h1_inv : ∀ v, s1.color v = Color.black → finishTime s1 v < s1.time := by
          intro v hv
          have hne : v ≠ u := by
            intro heq
            rw [heq] at hv
            simp [s1] at hv
          have h2 : finishTime s1 v = finishTime s v := by
            simp [finishTime, s1]
          have h3 : s1.time = s.time + 1 := by simp [s1]
          have h4 : finishTime s v < s.time := hinv v (by simpa [s1, hne] using hv)
          rw [h2, h3]
          linarith
        exact fold_inv (G.adj u).toList s1 h1_inv
      intro v hv
      by_cases hvu : v = u
      · have h4 : s3.time = s2.time + 1 := by simp [s3]
        have hthis : finishTime s3 v < s3.time := by
          rw [show v = u by exact hvu]
          exact hsource
        linarith [hthis, h4]
      · have h2 : s2.color v = Color.black := hv hvu
        have h3 : finishTime s3 v = finishTime s2 v := by
          simp [finishTime, s3, hvu]
        have h4 : s3.time = s2.time + 1 := by simp [s3]
        have h5 : finishTime s2 v < s2.time := hfold v h2
        rw [h3]
        linarith [h4, h5]

/-- The inner fold of a DFS visit preserves the black-vertex finish-time
invariant: if the initial accumulator satisfies it, so does the final result. -/
theorem dfsVisit_fold_black_finish_lt_time {n : Nat} {u : V} {s1 : DFSState V} {l : List V}
    (hinv : ∀ v, s1.color v = Color.black → finishTime s1 v < s1.time) :
    ∀ v, (List.foldl (fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 l).color v = Color.black →
      finishTime (List.foldl (fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 l) v <
      (List.foldl (fun (s' : DFSState V) (w : V) =>
        if s'.color w = Color.white then dfsVisit G n w (s'.setParent w u) else s') s1 l).time := by
  intros v hv
  induction l generalizing s1 with
  | nil =>
      simpa using hinv v hv
  | cons w ws ih' =>
      simp at hv ⊢
      by_cases hw : s1.color w = Color.white
      · simp [hw] at hv ⊢
        let s0 := s1.setParent w u
        let s_rec := dfsVisit G n w s0
        have hsp_inv : ∀ v, s0.color v = Color.black → finishTime s0 v < s0.time := by
          intro v hv0
          have hv1 : s1.color v = Color.black := by
            simpa [s0] using hv0
          have h1 : finishTime s0 v = finishTime s1 v := by
            simp [finishTime, s0]
          have h2 : s0.time = s1.time := by
            simp [s0]
          rw [h1, h2]
          exact hinv v hv1
        have hrec : ∀ v, s_rec.color v = Color.black → finishTime s_rec v < s_rec.time := by
          intro v' hv'
          by_cases hn0 : n = 0
          · -- n = 0, the recursive call returns s0 unchanged
            have h_eq : s_rec = s0 := by
              simp [s_rec, s0, hn0, dfsVisit]
            rw [h_eq] at hv' ⊢
            exact hsp_inv v' hv'
          · -- n > 0
            apply dfsVisit_black_finish_lt_time G (by omega) (by simpa [s0] using hw) hsp_inv v' hv'
        exact ih' (s1 := s_rec) hrec hv
      · simp [hw] at hv ⊢
        exact ih' (s1 := s1) hinv hv

/-- After the neighbor-processing fold of a DFS visit (but before the source is
finished), every black vertex already has a finish time strictly less than the
current clock. -/
theorem dfsVisit_pre_finish_black_finish_lt_time {fuel : Nat} {u : V} {s : DFSState V}
    (hfuel : 0 < fuel) (_hwhite : s.color u = Color.white)
    (hinv : ∀ v, s.color v = Color.black → finishTime s v < s.time) :
    let s1 := s.setColor u Color.gray |>.setDiscovery u
    let s2 := List.foldl (fun (s' : DFSState V) (v : V) =>
        if s'.color v = Color.white then dfsVisit G (fuel - 1) v (s'.setParent v u) else s') s1 (G.adj u).toList
    ∀ v, s2.color v = Color.black → finishTime s2 v < s2.time := by
  cases fuel with
  | zero => linarith
  | succ n =>
      let s1 := s.setColor u Color.gray |>.setDiscovery u
      let s2 := List.foldl (fun (s' : DFSState V) (v : V) =>
          if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s') s1 (G.adj u).toList
      have h1_inv : ∀ v, s1.color v = Color.black → finishTime s1 v < s1.time := by
        intro v hv
        have hne : v ≠ u := by
          intro heq
          rw [heq] at hv
          simp [s1] at hv
        have h2 : finishTime s1 v = finishTime s v := by
          simp [finishTime, s1]
        have h3 : s1.time = s.time + 1 := by simp [s1]
        have h4 : finishTime s v < s.time := hinv v (by simpa [s1, hne] using hv)
        rw [h2, h3]
        linarith
      have fold_inv : ∀ (l : List V) (s' : DFSState V),
          (∀ v, s'.color v = Color.black → finishTime s' v < s'.time) →
          ∀ v, (List.foldl (fun (s'' : DFSState V) (v : V) =>
              if s''.color v = Color.white then dfsVisit G n v (s''.setParent v u) else s'') s' l).color v = Color.black →
            finishTime (List.foldl (fun (s'' : DFSState V) (v : V) =>
                if s''.color v = Color.white then dfsVisit G n v (s''.setParent v u) else s'') s' l) v
              < (List.foldl (fun (s'' : DFSState V) (v : V) =>
                  if s''.color v = Color.white then dfsVisit G n v (s''.setParent v u) else s'') s' l).time := by
        intro l s' hs'
        induction l generalizing s' with
        | nil => simpa using hs'
        | cons w ws ih' =>
            simp
            by_cases hw : s'.color w = Color.white
            · simp [hw]
              let s0 := s'.setParent w u
              let s_rec := dfsVisit G n w s0
              have hsp : ∀ v, s0.color v = Color.black ↔ s'.color v = Color.black := by
                intro v; simp [s0]
              have hsp_inv : ∀ v, s0.color v = Color.black → finishTime s0 v < s0.time := by
                intro v hv
                have hv' : s'.color v = Color.black := by
                  simpa [s0] using hv
                have h1 : finishTime s0 v = finishTime s' v := by
                  simp [finishTime, s0]
                have h2 : s0.time = s'.time := by
                  simp [s0]
                rw [h1, h2]
                exact hs' v hv'
              have hrec : ∀ v, s_rec.color v = Color.black → finishTime s_rec v < s_rec.time := by
                intro v hv
                by_cases hn0 : n = 0
                · -- n = 0, the recursive call returns s0 unchanged
                  have h_eq : s_rec = s0 := by
                    simp [s_rec, s0, hn0, dfsVisit]
                  rw [h_eq] at hv ⊢
                  exact hsp_inv v hv
                · -- n > 0
                  exact dfsVisit_black_finish_lt_time G (by omega) (by simpa [s0] using hw) hsp_inv v hv
              exact ih' s_rec hrec
            · simp [hw]
              exact ih' s' hs'
      exact fold_inv (G.adj u).toList s1 h1_inv

/-- In a DFS visit from a white source, every vertex that is white before the visit
and black after it finishes strictly before the source. -/
theorem dfsVisit_finish_lt_source_finish {fuel : Nat} {u : V} {s : DFSState V} {w : V}
    (hfuel : 0 < fuel) (hwhite : s.color u = Color.white)
    (hinv : ∀ v, s.color v = Color.black → finishTime s v < s.time)
    (_hw : s.color w = Color.white)
    (hb : (dfsVisit G fuel u s).color w = Color.black)
    (hne : w ≠ u) :
    finishTime (dfsVisit G fuel u s) w < finishTime (dfsVisit G fuel u s) u := by
  cases fuel with
  | zero => linarith
  | succ n =>
      let s_out := dfsVisit G (n + 1) u s
      let s1 := s.setColor u Color.gray |>.setDiscovery u
      let s2 := List.foldl (fun (s' : DFSState V) (v : V) =>
          if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s') s1 (G.adj u).toList
      let s3 := s2.setColor u Color.black |>.setFinish u
      have hs' : dfsVisit G (n + 1) u s = s3 := by
        simp [dfsVisit, hwhite, s1, s2, s3]
      rw [hs'] at hb ⊢
      have hw_black_s2 : s2.color w = Color.black := by
        have : s3.color w = Color.black := hb
        simp [s3, hne] at this
        exact this
      have hfold := dfsVisit_pre_finish_black_finish_lt_time G hfuel hwhite hinv
      have h1 : finishTime s3 w = finishTime s2 w := by
        simp [finishTime, s3, hne]
      have h2 : finishTime s2 w < s2.time := hfold w hw_black_s2
      have h3 : finishTime s3 u = s2.time := by
        simp [finishTime, s3]
      rw [h1, h3]
      exact h2

/-- Recursive DFS preserves the black-vertex finish-time invariant. -/
theorem dfsFromList_black_finish_lt_time {fuel : Nat} {s0 : DFSState V} {vs : List V}
    (hfuel : 0 < fuel)
    (hinv : ∀ v, s0.color v = Color.black → finishTime s0 v < s0.time) :
    ∀ v, (dfsFromList G fuel vs s0).color v = Color.black →
      finishTime (dfsFromList G fuel vs s0) v < (dfsFromList G fuel vs s0).time := by
  induction vs generalizing s0
  · simpa [dfsFromList]
  · rename_i u us ih
    simp [dfsFromList]
    split_ifs with hwhite
    · exact ih (dfsVisit_black_finish_lt_time G hfuel hwhite hinv)
    · exact ih hinv

/-- After {lit}`dfs`, every vertex has a finish time strictly less than the final
clock. -/
theorem dfs_black_finish_lt_time {v : V} (hv : v ∈ G.vertices) :
    finishTime (G.dfs) v < (G.dfs).time := by
  have hfuel : 0 < G.vertices.card + 1 := by linarith [Finset.card_pos.mpr ⟨v, hv⟩]
  have hblack := G.dfs_all_black hv
  exact dfsFromList_black_finish_lt_time G hfuel (by
    intro w hw
    have h1 : dfsInit.color w = Color.white := rfl
    rw [h1] at hw
    nomatch hw
  ) v hblack

/-- For every black vertex, discovery time is less than finish time. -/
def DiscoveryFinishInvariant (s : DFSState V) : Prop :=
  ∀ v, s.color v = Color.black → discoveryTime s v < finishTime s v

/-- A DFS visit from a white vertex preserves the discovery<finish invariant. -/
theorem dfsVisit_discovery_lt_finish {fuel : Nat} {u : V} {s : DFSState V}
    (hfuel : 0 < fuel) (hwhite : s.color u = Color.white)
    (hinv : DiscoveryFinishInvariant s) :
    DiscoveryFinishInvariant (dfsVisit G fuel u s) := by
  induction fuel generalizing u s hinv hwhite with
  | zero => linarith
  | succ n ih =>
      simp [dfsVisit, hwhite]
      let s1 := s.setColor u Color.gray |>.setDiscovery u
      let step := fun (s' : DFSState V) (v : V) =>
        if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s'
      let s2 := List.foldl step s1 (G.adj u).toList
      let s3 := s2.setColor u Color.black |>.setFinish u
      intro v hv
      by_cases hvu : v = u
      · -- The source is discovered before it is finished.
        rw [hvu]
        have hdu : discoveryTime s3 u = s.time := by
          have h1 : s3.d u = some s.time := by
            have h2 : s2.d u = s1.d u := G.dfsVisit_fold_preserves_d_of_not_white s1 (by simp [s1])
            have h3 : s1.d u = some s.time := by simp [s1]
            simp [s3, h2, h3]
          simp [discoveryTime, h1]
        have hfu : finishTime s3 u = s2.time := by
          simp [finishTime, s3]
        have hge : s2.time ≥ s1.time := G.dfsVisit_fold_time_ge s1
        have hs1 : s1.time = s.time + 1 := by simp [s1]
        rw [hdu, hfu]
        linarith [hge, hs1]
      · -- Every other black vertex is processed inside the neighbor fold.
        have hblack_s2 : s2.color v = Color.black := by
          have : s3.color v = Color.black := hv
          simp [s3, hvu] at this
          exact this
        have h1 : discoveryTime s3 v = discoveryTime s2 v := by
          simp [discoveryTime, s3]
        have h2 : finishTime s3 v = finishTime s2 v := by
          simp [finishTime, s3, if_neg hvu]
        have hinv_s1 : ∀ x, s1.color x = Color.black → discoveryTime s1 x < finishTime s1 x := by
          intro x hx
          have hne : x ≠ u := by
            intro heq
            rw [heq] at hx
            simp [s1] at hx
          have hd : discoveryTime s1 x = discoveryTime s x := by
            simp [discoveryTime, s1, hne]
          have hf : finishTime s1 x = finishTime s x := by
            simp [finishTime, s1]
          rw [hd, hf]
          exact hinv x (by simpa [s1, hne] using hx)
        have fold_inv : ∀ (l : List V) (s' : DFSState V),
            (∀ x, s'.color x = Color.black → discoveryTime s' x < finishTime s' x) →
            ∀ x, (List.foldl step s' l).color x = Color.black →
              discoveryTime (List.foldl step s' l) x < finishTime (List.foldl step s' l) x := by
          intro l s' hs' x hx
          induction l generalizing s' with
          | nil => simpa using hs' x hx
          | cons w ws ih' =>
              simp [step] at hx ⊢
              by_cases hw : s'.color w = Color.white
              · simp [hw] at hx ⊢
                let s0 := s'.setParent w u
                let s_rec := dfsVisit G n w s0
                have hsp_inv : ∀ x, s0.color x = Color.black → discoveryTime s0 x < finishTime s0 x := by
                  intro y hy
                  have hy1 : s'.color y = Color.black := by simpa [s0] using hy
                  simp [discoveryTime, finishTime, s0]
                  exact hs' y hy1
                have hrec : ∀ x, s_rec.color x = Color.black → discoveryTime s_rec x < finishTime s_rec x := by
                  intro y hy
                  by_cases hn0 : n = 0
                  · have h_eq : s_rec = s0 := by
                      simp [s_rec, s0, hn0, dfsVisit]
                    rw [h_eq] at hy ⊢
                    exact hsp_inv y hy
                  · exact ih (u := w) (s := s0) (by omega) (by simpa [s0] using hw) hsp_inv y hy
                exact ih' s_rec hrec hx
              · simp [hw] at hx ⊢
                exact ih' s' hs' hx
        have hfold := fold_inv (G.adj u).toList s1 hinv_s1 v hblack_s2
        rw [h1, h2]
        exact hfold

/-- Recursive DFS over a list preserves the discovery<finish invariant. -/
theorem dfsFromList_discovery_lt_finish {fuel : Nat} {s0 : DFSState V} {vs : List V}
    (hfuel : 0 < fuel) (hinv : DiscoveryFinishInvariant s0) :
    DiscoveryFinishInvariant (dfsFromList G fuel vs s0) := by
  induction vs generalizing s0
  · simpa [dfsFromList]
  · rename_i u us ih
    simp [dfsFromList]
    split_ifs with hwhite
    · exact ih (dfsVisit_discovery_lt_finish G hfuel hwhite hinv)
    · exact ih hinv

/-- After {lit}`dfs`, every vertex has a discovery time strictly less than its
finish time. -/
theorem dfs_discovery_lt_finish {v : V} (hv : v ∈ G.vertices) :
    discoveryTime (G.dfs) v < finishTime (G.dfs) v := by
  have hfuel : 0 < G.vertices.card + 1 := by linarith [Finset.card_pos.mpr ⟨v, hv⟩]
  have hinv : DiscoveryFinishInvariant G.dfs :=
    dfsFromList_discovery_lt_finish G hfuel (by
      intro w hw
      have h1 : dfsInit.color w = Color.white := rfl
      rw [h1] at hw
      nomatch hw
    )
  exact hinv v (G.dfs_all_black hv)

end Timestamps

end BasicProperties

end Graph

end Chapter22
end CLRS
