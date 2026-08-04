import Mathlib.Tactic

/-!
# CLRS Chapter 27 — Execution-Attached Work and Span

This module gives the parallel algorithms in §§27.2–27.4 a small executable
cost layer.  A computation carries its value together with exact natural-number
work and span.  Sequential composition adds both costs; balanced parallel
composition adds work across branches, takes the maximum branch span, and
charges one unit for each fork/join node.

The four-way and eight-way combinators use balanced binary trees.  Their values
therefore have shapes {lit}`((a, b), (c, d))` and
{lit}`(((a, b), (c, d)), ((e, f), (g, h)))`, respectively.
-/

namespace CLRS
namespace Chapter27

universe u v

/-- An executable value annotated with its exact work and span costs. -/
structure Costed (α : Type u) where
  value : α
  work : ℕ
  span : ℕ
deriving Repr, DecidableEq

namespace Costed

/-- Lift a value without charging any work or span. -/
def pure (x : α) : Costed α := ⟨x, 0, 0⟩

/-- Attach explicitly supplied work and span costs to a value. -/
def charge (work span : ℕ) (x : α) : Costed α := ⟨x, work, span⟩

/-- Transform the result of a computation without changing its costs. -/
def map (f : α → β) (x : Costed α) : Costed β :=
  ⟨f x.value, x.work, x.span⟩

/-- Run two computations sequentially, adding both work and span. -/
def seq (x : Costed α) (f : α → Costed β) : Costed β :=
  let y := f x.value
  ⟨y.value, x.work + y.work, x.span + y.span⟩

/-- Run two independent computations in parallel.

The work is the sum of branch work plus one fork/join node.  The span follows
the slower branch and likewise includes the fork/join node.
-/
def par (x : Costed α) (y : Costed β) : Costed (α × β) :=
  ⟨(x.value, y.value), x.work + y.work + 1, max x.span y.span + 1⟩

/-- Balanced four-way parallel composition using three binary parallel nodes.
The returned tuple has the explicit shape {lit}`((a, b), (c, d))`. -/
def par4 (a b c d : Costed α) : Costed ((α × α) × (α × α)) :=
  par (par a b) (par c d)

/-- Balanced eight-way parallel composition using seven binary parallel nodes.
The returned tuple has the explicit shape
{lit}`(((a, b), (c, d)), ((e, f), (g, h)))`. -/
def par8 (a b c d e f g h : Costed α) :
    Costed (((α × α) × (α × α)) × ((α × α) × (α × α))) :=
  par (par4 a b c d) (par4 e f g h)

@[simp] theorem pure_value (x : α) : (pure x).value = x := rfl

@[simp] theorem pure_work (x : α) : (pure x).work = 0 := rfl

@[simp] theorem pure_span (x : α) : (pure x).span = 0 := rfl

@[simp] theorem charge_value (work span : ℕ) (x : α) :
    (charge work span x).value = x := rfl

@[simp] theorem charge_work (work span : ℕ) (x : α) :
    (charge work span x).work = work := rfl

@[simp] theorem charge_span (work span : ℕ) (x : α) :
    (charge work span x).span = span := rfl

@[simp] theorem map_value (f : α → β) (x : Costed α) :
    (map f x).value = f x.value := rfl

@[simp] theorem map_work (f : α → β) (x : Costed α) :
    (map f x).work = x.work := rfl

@[simp] theorem map_span (f : α → β) (x : Costed α) :
    (map f x).span = x.span := rfl

@[simp] theorem seq_value (x : Costed α) (f : α → Costed β) :
    (seq x f).value = (f x.value).value := by
  simp [seq]

@[simp] theorem seq_work (x : Costed α) (f : α → Costed β) :
    (seq x f).work = x.work + (f x.value).work := by
  simp [seq]

@[simp] theorem seq_span (x : Costed α) (f : α → Costed β) :
    (seq x f).span = x.span + (f x.value).span := by
  simp [seq]

@[simp] theorem par_value (x : Costed α) (y : Costed β) :
    (par x y).value = (x.value, y.value) := rfl

@[simp] theorem par_work (x : Costed α) (y : Costed β) :
    (par x y).work = x.work + y.work + 1 := rfl

@[simp] theorem par_span (x : Costed α) (y : Costed β) :
    (par x y).span = max x.span y.span + 1 := rfl

@[simp] theorem par4_value (a b c d : Costed α) :
    (par4 a b c d).value = ((a.value, b.value), (c.value, d.value)) := by
  rfl

@[simp] theorem par4_work (a b c d : Costed α) :
    (par4 a b c d).work = a.work + b.work + c.work + d.work + 3 := by
  simp [par4]
  omega

@[simp] theorem par4_span (a b c d : Costed α) :
    (par4 a b c d).span = max (max a.span b.span) (max c.span d.span) + 2 := by
  simp [par4]

@[simp] theorem par8_value (a b c d e f g h : Costed α) :
    (par8 a b c d e f g h).value =
      (((a.value, b.value), (c.value, d.value)),
        ((e.value, f.value), (g.value, h.value))) := by
  rfl

@[simp] theorem par8_work (a b c d e f g h : Costed α) :
    (par8 a b c d e f g h).work =
      a.work + b.work + c.work + d.work + e.work + f.work + g.work + h.work + 7 := by
  simp [par8]
  omega

@[simp] theorem par8_span (a b c d e f g h : Costed α) :
    (par8 a b c d e f g h).span =
      max (max (max a.span b.span) (max c.span d.span))
          (max (max e.span f.span) (max g.span h.span)) + 3 := by
  simp [par8]

end Costed

end Chapter27
end CLRS
