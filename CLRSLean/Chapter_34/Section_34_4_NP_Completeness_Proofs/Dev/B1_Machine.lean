import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SatTo3CNFSat

/-!
# Dev B1: the machine tapes, alphabet, and states

Development split of `SatTo3CNFMachine`: the TM2 machine tapes `K`, frames
`Frame`, tape alphabet `Γk`, move/restore operations `Op`, program labels
`Label`, states `St`, and the phase-start stack abbreviation `stk`.

The machine program `prog`, the step relation `Sstep`, and the step lemmas
live in `Dev.B1_Prog` and `Dev.B1_Steps`.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

/-- The machine tapes. -/
inductive K : Type
  | inK | temp | cnt | val | frm | scr | o | out
deriving DecidableEq, Fintype, Inhabited

/-- A continuation frame: an operator waiting for its children. -/
inductive Frame : Type
  | top
  | not
  | and₁ | and₂
  | or₁ | or₂
  | iff₁ | iff₂
deriving DecidableEq, Fintype, Inhabited

/-- The alphabet of each tape.  `val` holds value variables as runs of `true`s
followed by a `false` separator (index `y` is `y + 1` `true`s). -/
abbrev Γk : K → Type
  | K.inK => FormulaSym
  | K.temp => FormulaSym
  | K.cnt => Unit
  | K.val => Bool
  | K.frm => Frame
  | K.scr => Unit
  | K.o => CNFSym
  | K.out => CNFSym

/-- A move/restore operation: emit an auxiliary reference, build a value
variable, or emit/pop a value-variable reference, or park/restore a value
variable on the `temp` tape. -/
inductive Op : Type
  | auxEmit | makeVal | varEmit | varPop | park | unpark
deriving DecidableEq, Fintype, Inhabited

/-- The program labels. -/
inductive Label : Type
  | count | reorder | done
  | rd | rdVar | pv0 | pv | reduce | const | constFalse | constEmit | constMake
  | emitNot | not₂ | not₃ | not₄ | not₅ | not₆
  | emitAnd | and₂ | and₃ | and₄ | and₅ | and₆ | and₇ | and₈ | and₉ | and₁₀ | and₁₁ | and₁₂
    | and₁₃ | and₁₄ | and₁₅ | and₁₆
  | emitOr | or₂ | or₃ | or₄ | or₅ | or₆ | or₇ | or₈ | or₉ | or₁₀ | or₁₁ | or₁₂
    | or₁₃ | or₁₄ | or₁₅ | or₁₆
  | emitIff | iff₂ | iff₃ | iff₄ | iff₅ | iff₆ | iff₇ | iff₈ | iff₉ | iff₁₀
    | iff₁₁ | iff₁₂ | iff₁₃ | iff₁₄ | iff₁₅ | iff₁₆ | iff₁₇ | iff₁₈ | iff₁₉ | iff₂₀ | iff₂₁
    | iff₂₂ | iff₂₃ | iff₂₄ | iff₂₅ | iff₂₆ | iff₂₇ | iff₂₈ | iff₂₉ | iff₃₀
  | emitTrue | emitTrueRestore
  | moveCnt | restoreCnt | moveVal | restoreVal | parkVal | parkRest | unparkVal
  | copyOut | clearIn | clearCnt
deriving DecidableEq, Fintype, Inhabited

/-- The machine states. -/
inductive St : Type
  | init | done
  | count | reorder
  | rd (s : FormulaSym)
  | pv | reduce
  | and₁Done | or₁Done | iff₁Done
  | mv (go : Label) (k : Op) | rs (go : Label) (k : Op)
  | rsDone (go : Label) (k : Op)
  | emitNot | emitAnd | emitOr | emitIff
  | emitTrue
  | constLoop
  | copySym (s : CNFSym)
deriving DecidableEq, Fintype, Inhabited

/-- The full stack contents at the start of a phase. -/
abbrev stk (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) : ∀ k : K, List (Γk k) :=
  fun k => match k with
  | K.inK => inp | K.temp => T | K.cnt => List.replicate c ()
  | K.val => V | K.frm => F | K.scr => S
  | K.o => O | K.out => U

end TM3CNF

end Turing

end Chapter34

end CLRS
