import Mathlib
import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs

/-! # Section 22.3 - Depth-First Search

This section gives a functional depth-first-search procedure on the finite graph
model from Section 22.1 and proves a basic correctness invariant: after DFS,
every vertex of the graph is black.  Timestamps, parent pointers, and vertex
colors (white/gray/black) are represented as functions, so the algorithm is
noncomputable because it iterates over {lit}`Finset.toList`.

The classic parenthesis theorem and white-path theorem are stated as the next
targets on this DFS model.
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
  | nil => simpa
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

/-- One step of the inner `dfsVisit` fold preserves black vertices. -/
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
  | nil => simpa
  | cons w ws ih =>
      simp
      exact ih (dfsVisit_fold_step_preserves_black G hb)

/-- The inner fold of a DFS visit does not introduce new gray vertices. -/
theorem dfsVisit_fold_no_new_gray {n : Nat} {u w : V} (s1 : DFSState V) {l : List V} :
    (List.foldl (fun (s' : DFSState V) (v : V) =>
        if s'.color v = Color.white then dfsVisit G n v (s'.setParent v u) else s') s1 l).color w = Color.gray →
    s1.color w = Color.gray := by
  induction l generalizing s1 with
  | nil => simpa
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

end BasicProperties

end Graph

end Chapter22
end CLRS
