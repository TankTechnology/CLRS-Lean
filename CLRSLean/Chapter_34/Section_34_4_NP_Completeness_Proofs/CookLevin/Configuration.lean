import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.ReachableAlphabet

/-!
# CLRS Section 34.4 - Bounded configurations and stuttering runs

Cook--Levin circuits describe a finite execution tableau.  This file gives the
finite code used for one row, proves honest encoding and decoding theorems, and
turns a bounded halting run into an exact-length stuttering run.  It also proves
a uniform stack-height bound that counts every push along a bundled TM2
statement path.

Main results:

- Theorems {lit}`decodeCfg_encodeCfg` and {lit}`encodeCfg_decodeCfg`: canonical
  bounded configuration codes round-trip in both directions.
- Theorem {lit}`evalsToInTime_iff_stutter_accepts`: a bounded halting witness is
  equivalent to an exact stuttering horizon.
- Theorem {lit}`stack_length_iterate_le`: every tableau row fits a linear stack
  height bound.

Current gaps:

- None for the finite configuration and stuttering model; circuitization is the
  next module.
-/

open Computability StateTransition

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

noncomputable section

/-! ## Finite row codes -/

/-- Number of program labels in the bundled finite control. -/
def labelCount (tm : _root_.Turing.FinTM2) : Nat :=
  @Fintype.card tm.Λ tm.ΛFin

/-- Number of internal states in the bundled finite control. -/
def stateCount (tm : _root_.Turing.FinTM2) : Nat :=
  @Fintype.card tm.σ tm.σFin

/-- A bundled machine has at least one label because it stores a main label. -/
theorem labelCount_pos (tm : _root_.Turing.FinTM2) : 0 < labelCount tm := by
  letI := tm.ΛFin
  exact Fintype.card_pos_iff.mpr ⟨tm.main⟩

/-- A bundled machine has at least one state because it stores an initial state. -/
theorem stateCount_pos (tm : _root_.Turing.FinTM2) : 0 < stateCount tm := by
  letI := tm.σFin
  exact Fintype.card_pos_iff.mpr ⟨tm.initialState⟩

/-- A stack row has a bounded height and one finite code per tableau cell.

The final symbol code, whose value is {lit}`alphabetSize`, is reserved for blank
cells. -/
structure BoundedStack (alphabetSize H : Nat) where
  height : Fin (H + 1)
  cells : Fin H → Fin (alphabetSize + 1)
deriving DecidableEq, Fintype

private instance finTM2StackIndexFintype (tm : _root_.Turing.FinTM2) : Fintype tm.K :=
  tm.kFin

/-- A finite tableau row.  The final label code is reserved for {lean}`none`;
the separate halted bit is retained because the circuit layer will constrain
it explicitly and validity couples the two representations. -/
structure BoundedCfg (tm : _root_.Turing.FinTM2) (H : Nat) where
  halted : Bool
  label : Fin (labelCount tm + 1)
  state : Fin (stateCount tm)
  stack : ∀ k : tm.K, BoundedStack (reachableAlphabet tm k).card H
deriving Fintype

/-- Equality of bounded rows is decidable without requiring any full stack
alphabet to be decidable or finite. -/
noncomputable instance boundedCfgDecidableEq (tm : _root_.Turing.FinTM2) (H : Nat) :
    DecidableEq (BoundedCfg tm H) := Classical.decEq _

/-- Canonical noncomputable code for a program label. -/
noncomputable def labelEquivFin (tm : _root_.Turing.FinTM2) :
    tm.Λ ≃ Fin (labelCount tm) := by
  letI := tm.ΛFin
  exact Fintype.equivFin _

/-- Canonical noncomputable code for an internal state. -/
noncomputable def stateEquivFin (tm : _root_.Turing.FinTM2) :
    tm.σ ≃ Fin (stateCount tm) := by
  letI := tm.σFin
  exact Fintype.equivFin _

/-- Canonical noncomputable code for one symbol in the finite reachable
program support of a stack. -/
noncomputable def alphabetEquivFin (tm : _root_.Turing.FinTM2) (k : tm.K) :
    {a : tm.Γ k // a ∈ reachableAlphabet tm k} ≃
      Fin (reachableAlphabet tm k).card := by
  classical
  letI : Fintype {a : tm.Γ k // a ∈ reachableAlphabet tm k} :=
    Fintype.ofFinite _
  simpa only [Fintype.card_coe] using
    (Fintype.equivFin {a : tm.Γ k // a ∈ reachableAlphabet tm k})

/-- A bounded stack code is canonical exactly when its active prefix is
nonblank and every cell outside that prefix is blank. -/
def BoundedStack.Valid {alphabetSize H : Nat}
    (code : BoundedStack alphabetSize H) : Prop :=
  ∀ i, (code.cells i).val < alphabetSize ↔ i.val < code.height.val

/-- A bounded row is canonical when every stack is canonical and the halted
bit agrees exactly with the reserved {lean}`none` label code. -/
def BoundedCfg.Valid {tm : _root_.Turing.FinTM2} {H : Nat}
    (code : BoundedCfg tm H) : Prop :=
  (code.halted = true ↔ code.label.val = labelCount tm) ∧
    ∀ k, (code.stack k).Valid

/-! ## Stack and finite-control codecs -/

/-- Encode a supported alphabet symbol, leaving the final code for blanks. -/
noncomputable def encodeAlphabetSymbol (tm : _root_.Turing.FinTM2) (k : tm.K)
    (a : tm.Γ k) (ha : a ∈ reachableAlphabet tm k) :
    Fin ((reachableAlphabet tm k).card + 1) :=
  Fin.castLE (Nat.le_succ _) (alphabetEquivFin tm k ⟨a, ha⟩)

/-- Decode a nonblank symbol code back into the original stack alphabet. -/
noncomputable def decodeAlphabetSymbol (tm : _root_.Turing.FinTM2) (k : tm.K)
    (code : Fin ((reachableAlphabet tm k).card + 1))
    (hcode : code.val < (reachableAlphabet tm k).card) : tm.Γ k :=
  (alphabetEquivFin tm k).symm ⟨code.val, hcode⟩

/-- Encode an optional label, using the last code for {lean}`none`. -/
noncomputable def encodeLabel (tm : _root_.Turing.FinTM2) :
    Option tm.Λ → Fin (labelCount tm + 1)
  | none => ⟨labelCount tm, Nat.lt_succ_self _⟩
  | some label => Fin.castLE (Nat.le_succ _) (labelEquivFin tm label)

/-- Decode a label code, interpreting the reserved last code as {lean}`none`. -/
noncomputable def decodeLabel (tm : _root_.Turing.FinTM2)
    (code : Fin (labelCount tm + 1)) : Option tm.Λ :=
  if h : code.val < labelCount tm then
    some ((labelEquivFin tm).symm ⟨code.val, h⟩)
  else none

/-- Optional labels round-trip through the reserved finite label code. -/
theorem decodeLabel_encodeLabel (tm : _root_.Turing.FinTM2) (label : Option tm.Λ) :
    decodeLabel tm (encodeLabel tm label) = label := by
  cases label with
  | none => simp [decodeLabel, encodeLabel]
  | some label =>
      simp [decodeLabel, encodeLabel, (labelEquivFin tm label).isLt]

/-- Every finite label code is canonical. -/
theorem encodeLabel_decodeLabel (tm : _root_.Turing.FinTM2)
    (code : Fin (labelCount tm + 1)) :
    encodeLabel tm (decodeLabel tm code) = code := by
  unfold decodeLabel
  split_ifs with h
  · apply Fin.ext
    simp [encodeLabel]
  · apply Fin.ext
    simp only [encodeLabel]
    omega

/-- Canonically encode a stack list known to lie in program support and fit in
the selected height. -/
noncomputable def encodeBoundedStack (tm : _root_.Turing.FinTM2) (k : tm.K)
    (xs : List (tm.Γ k))
    (halphabet : ∀ a, a ∈ xs → a ∈ reachableAlphabet tm k)
    {H : Nat} (hheight : xs.length ≤ H) :
    BoundedStack (reachableAlphabet tm k).card H where
  height := ⟨xs.length, Nat.lt_succ_iff.mpr hheight⟩
  cells i := if hi : i.val < xs.length then
      encodeAlphabetSymbol tm k (xs.get ⟨i.val, hi⟩)
        (halphabet _ (xs.get_mem ⟨i.val, hi⟩))
    else
      ⟨(reachableAlphabet tm k).card, Nat.lt_succ_self _⟩

/-- A stack produced by {name}`encodeBoundedStack` has exactly the canonical active
nonblank prefix. -/
theorem encodeBoundedStack_valid (tm : _root_.Turing.FinTM2) (k : tm.K)
    (xs : List (tm.Γ k))
    (halphabet : ∀ a, a ∈ xs → a ∈ reachableAlphabet tm k)
    {H : Nat} (hheight : xs.length ≤ H) :
    (encodeBoundedStack tm k xs halphabet hheight).Valid := by
  intro i
  simp only [encodeBoundedStack]
  split_ifs with hi
  · simp [encodeAlphabetSymbol, hi]
  · simp [hi]

/-- Convert an index below a coded height into a physical tableau-cell index. -/
def BoundedStack.activeIndex {alphabetSize H : Nat}
    (code : BoundedStack alphabetSize H) (i : Fin code.height.val) : Fin H :=
  ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ code.height.isLt)⟩

/-- Decode a valid bounded stack into the original symbol alphabet. -/
noncomputable def decodeBoundedStack (tm : _root_.Turing.FinTM2) (k : tm.K)
    {H : Nat} (code : BoundedStack (reachableAlphabet tm k).card H)
    (hvalid : code.Valid) : List (tm.Γ k) :=
  List.ofFn fun i : Fin code.height.val =>
    decodeAlphabetSymbol tm k (code.cells (code.activeIndex i))
      ((hvalid (code.activeIndex i)).mpr i.isLt)

/-- Decoding returns precisely the height recorded in a valid stack code. -/
theorem decodeBoundedStack_length (tm : _root_.Turing.FinTM2) (k : tm.K)
    {H : Nat} (code : BoundedStack (reachableAlphabet tm k).card H)
    (hvalid : code.Valid) :
    (decodeBoundedStack tm k code hvalid).length = code.height.val := by
  simp [decodeBoundedStack]

/-- Decoding an encoded bounded stack recovers the original list. -/
theorem decodeBoundedStack_encode (tm : _root_.Turing.FinTM2) (k : tm.K)
    (xs : List (tm.Γ k))
    (halphabet : ∀ a, a ∈ xs → a ∈ reachableAlphabet tm k)
    {H : Nat} (hheight : xs.length ≤ H) :
    decodeBoundedStack tm k (encodeBoundedStack tm k xs halphabet hheight)
      (encodeBoundedStack_valid tm k xs halphabet hheight) = xs := by
  apply List.ext_get_iff.mpr
  constructor
  · simp [decodeBoundedStack, encodeBoundedStack]
  · intro n h₁ h₂
    simp [decodeBoundedStack, encodeBoundedStack, BoundedStack.activeIndex,
      decodeAlphabetSymbol, encodeAlphabetSymbol]

private theorem boundedStack_ext {alphabetSize H : Nat}
    {left right : BoundedStack alphabetSize H}
    (hheight : left.height = right.height)
    (hcells : left.cells = right.cells) : left = right := by
  cases left
  cases right
  simp_all

/-- Re-encoding the decoded contents of a valid bounded stack recovers the
entire raw code, including all blank cells. -/
theorem encodeBoundedStack_decode (tm : _root_.Turing.FinTM2) (k : tm.K)
    {H : Nat} (code : BoundedStack (reachableAlphabet tm k).card H)
    (hvalid : code.Valid) :
    encodeBoundedStack tm k (decodeBoundedStack tm k code hvalid)
      (fun a ha => by
        simp only [decodeBoundedStack, List.mem_ofFn] at ha
        rcases ha with ⟨i, rfl⟩
        exact (alphabetEquivFin tm k).symm
          ⟨(code.cells (code.activeIndex i)).val,
            (hvalid (code.activeIndex i)).mpr i.isLt⟩ |>.property)
      (by simpa [decodeBoundedStack] using Nat.le_of_lt_succ code.height.isLt) = code := by
  apply boundedStack_ext
  · apply Fin.ext
    simp [encodeBoundedStack, decodeBoundedStack]
  · funext i
    apply Fin.ext
    simp only [encodeBoundedStack, decodeBoundedStack_length]
    split_ifs with hi
    · simp [decodeBoundedStack, BoundedStack.activeIndex, encodeAlphabetSymbol,
        decodeAlphabetSymbol]
    · have hblank := (hvalid i).not.mpr hi
      have hcellLt := (code.cells i).isLt
      have hblankVal : (code.cells i).val = (reachableAlphabet tm k).card := by
        omega
      simp [hblankVal]

/-! ## Configuration encoding and decoding -/

/-- Boolean view of whether an optional machine label is halted. -/
def labelHalted {α : Type} : Option α → Bool
  | none => true
  | some _ => false

/-- Encode an alphabet-bounded machine configuration whose stacks fit in the
selected tableau height. -/
noncomputable def encodeCfg (tm : _root_.Turing.FinTM2) {c : tm.Cfg}
    (hc : CfgAlphabetBounded tm c) {H : Nat}
    (hheight : ∀ k, (c.stk k).length ≤ H) : BoundedCfg tm H where
  halted := labelHalted c.l
  label := encodeLabel tm c.l
  state := stateEquivFin tm c.var
  stack k := encodeBoundedStack tm k (c.stk k) (hc k) (hheight k)

/-- Every encoded machine configuration is a canonical bounded row. -/
theorem encodeCfg_valid (tm : _root_.Turing.FinTM2) {c : tm.Cfg}
    (hc : CfgAlphabetBounded tm c) {H : Nat}
    (hheight : ∀ k, (c.stk k).length ≤ H) :
    (encodeCfg tm hc hheight).Valid := by
  rcases c with ⟨label, state, stackFn⟩
  constructor
  · cases label with
    | none => simp [encodeCfg, labelHalted, encodeLabel]
    | some label =>
        constructor
        · simp [encodeCfg, labelHalted]
        · intro heq
          have hlt := (labelEquivFin tm label).isLt
          simp only [encodeCfg, encodeLabel] at heq
          change (labelEquivFin tm label).val = labelCount tm at heq
          omega
  · intro k
    exact encodeBoundedStack_valid tm k (stackFn k) (hc k) (hheight k)

/-- Decode a canonical bounded row to a machine configuration. -/
noncomputable def decodeCfg (tm : _root_.Turing.FinTM2) {H : Nat}
    (code : BoundedCfg tm H) (hvalid : code.Valid) : tm.Cfg where
  l := decodeLabel tm code.label
  var := (stateEquivFin tm).symm code.state
  stk k := decodeBoundedStack tm k (code.stack k) (hvalid.2 k)

/-- Reject a noncanonical raw row and decode a canonical one. -/
noncomputable def decodeCfg? (tm : _root_.Turing.FinTM2) {H : Nat}
    (code : BoundedCfg tm H) : Option tm.Cfg := by
  classical
  exact if h : code.Valid then some (decodeCfg tm code h) else none

/-- A decoded row uses only symbols in the fixed machine's finite support. -/
theorem decoded_alphabetBounded (tm : _root_.Turing.FinTM2) {H : Nat}
    (code : BoundedCfg tm H) (hvalid : code.Valid) :
    CfgAlphabetBounded tm (decodeCfg tm code hvalid) := by
  intro k a ha
  simp only [decodeCfg, decodeBoundedStack, List.mem_ofFn] at ha
  rcases ha with ⟨i, rfl⟩
  exact (alphabetEquivFin tm k).symm
    ⟨((code.stack k).cells ((code.stack k).activeIndex i)).val,
      ((hvalid.2 k) ((code.stack k).activeIndex i)).mpr i.isLt⟩ |>.property

/-- Every decoded stack has height at most the selected tableau height. -/
theorem decoded_stack_length_le (tm : _root_.Turing.FinTM2) {H : Nat}
    (code : BoundedCfg tm H) (hvalid : code.Valid) (k : tm.K) :
    ((decodeCfg tm code hvalid).stk k).length ≤ H := by
  rw [decodeCfg, decodeBoundedStack_length]
  exact Nat.le_of_lt_succ (code.stack k).height.isLt

private theorem tm2Cfg_ext {tm : _root_.Turing.FinTM2} {left right : tm.Cfg}
    (hlabel : left.l = right.l) (hstate : left.var = right.var)
    (hstacks : left.stk = right.stk) : left = right := by
  cases left
  cases right
  simp_all

private theorem boundedCfg_ext {tm : _root_.Turing.FinTM2} {H : Nat}
    {left right : BoundedCfg tm H}
    (hhalted : left.halted = right.halted)
    (hlabel : left.label = right.label)
    (hstate : left.state = right.state)
    (hstacks : left.stack = right.stack) : left = right := by
  cases left
  cases right
  simp_all

/-- Decoding an encoded bounded machine configuration recovers the original
configuration exactly. -/
theorem decodeCfg_encodeCfg (tm : _root_.Turing.FinTM2) {c : tm.Cfg}
    (hc : CfgAlphabetBounded tm c) {H : Nat}
    (hheight : ∀ k, (c.stk k).length ≤ H) :
    decodeCfg tm (encodeCfg tm hc hheight) (encodeCfg_valid tm hc hheight) = c := by
  apply tm2Cfg_ext
  · exact decodeLabel_encodeLabel tm c.l
  · exact (stateEquivFin tm).symm_apply_apply c.var
  · funext k
    exact decodeBoundedStack_encode tm k (c.stk k) (hc k) (hheight k)

private theorem labelHalted_decodeLabel (tm : _root_.Turing.FinTM2)
    {H : Nat} (code : BoundedCfg tm H) (hvalid : code.Valid) :
    labelHalted (decodeLabel tm code.label) = code.halted := by
  unfold decodeLabel
  split_ifs with hlt
  · have hne : code.label.val ≠ labelCount tm := Nat.ne_of_lt hlt
    have hnot : code.halted ≠ true := by
      intro htrue
      exact hne (hvalid.1.mp htrue)
    have hfalse : code.halted = false := by
      cases h : code.halted
      · rfl
      · exact False.elim (hnot h)
    simp [labelHalted, hfalse]
  · have hle := Nat.le_of_not_gt hlt
    have heq : code.label.val = labelCount tm := by
      omega
    have htrue : code.halted = true := hvalid.1.mpr heq
    simp [labelHalted, htrue]

/-- Encoding the proof-indexed decoding of a valid row recovers every bit of
the original raw row. -/
theorem encodeCfg_decodeCfg (tm : _root_.Turing.FinTM2) {H : Nat}
    (code : BoundedCfg tm H) (hvalid : code.Valid) :
    encodeCfg tm (decoded_alphabetBounded tm code hvalid)
      (decoded_stack_length_le tm code hvalid) = code := by
  apply boundedCfg_ext
  · exact labelHalted_decodeLabel tm code hvalid
  · exact encodeLabel_decodeLabel tm code.label
  · exact (stateEquivFin tm).apply_symm_apply code.state
  · funext k
    exact encodeBoundedStack_decode tm k (code.stack k) (hvalid.2 k)

/-! ## Exact stuttering horizons -/

/-- Total transition used by a Cook--Levin tableau: genuine machine steps are
taken, while a halted configuration repeats forever. -/
def stutterStep (tm : _root_.Turing.FinTM2) (c : tm.Cfg) : tm.Cfg :=
  (tm.step c).getD c

/-- A bundled TM2 step is absent exactly at its reserved {lean}`none` label. -/
theorem step_eq_none_iff_label_none (tm : _root_.Turing.FinTM2) (c : tm.Cfg) :
    tm.step c = none ↔ c.l = none := by
  rcases c with ⟨label, state, stackFn⟩
  cases label with
  | none =>
      constructor <;> intro _ <;> rfl
  | some label =>
      simp [_root_.Turing.FinTM2.step, _root_.Turing.TM2.step]

/-- Halted configurations are stable under the total stuttering step. -/
theorem stutterStep_halted (tm : _root_.Turing.FinTM2) {c : tm.Cfg}
    (hhalted : c.l = none) : stutterStep tm c = c := by
  have hnone := (step_eq_none_iff_label_none tm c).mpr hhalted
  unfold stutterStep
  change (tm.step c).getD c = c
  rw [hnone]
  rfl

/-- One stuttering transition preserves the finite program-support alphabet. -/
theorem stutterStep_alphabetBounded (tm : _root_.Turing.FinTM2) {c : tm.Cfg}
    (hc : CfgAlphabetBounded tm c) :
    CfgAlphabetBounded tm (stutterStep tm c) := by
  cases hstep : tm.step c with
  | none =>
      change CfgAlphabetBounded tm ((tm.step c).getD c)
      rw [hstep]
      exact hc
  | some c' =>
      change CfgAlphabetBounded tm ((tm.step c).getD c)
      rw [hstep]
      exact step_alphabetBounded tm hc hstep

/-- Every finite stuttering prefix preserves the finite program-support
alphabet. -/
theorem stutter_iterate_alphabetBounded (tm : _root_.Turing.FinTM2)
    {c : tm.Cfg} (hc : CfgAlphabetBounded tm c) (t : Nat) :
    CfgAlphabetBounded tm ((stutterStep tm)^[t] c) := by
  induction t generalizing c with
  | zero => simpa using hc
  | succ t ih =>
      rw [Function.iterate_succ_apply]
      exact ih (stutterStep_alphabetBounded tm hc)

private theorem optionStep_none_iterate (tm : _root_.Turing.FinTM2) (t : Nat) :
    (flip bind tm.step)^[t] (none : Option tm.Cfg) = none := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply]
      exact ih

private theorem evalsInSteps_stutter (tm : _root_.Turing.FinTM2)
    {c c' : tm.Cfg} {t : Nat}
    (hsteps : (flip bind tm.step)^[t] (some c) = some c') :
    (stutterStep tm)^[t] c = c' := by
  induction t generalizing c with
  | zero =>
      simp only [Function.iterate_zero_apply, Option.some.injEq] at hsteps
      exact hsteps
  | succ t ih =>
      rw [Function.iterate_succ_apply] at hsteps ⊢
      change (flip bind tm.step)^[t] (tm.step c) = some c' at hsteps
      cases hstep : tm.step c with
      | none =>
          rw [hstep, optionStep_none_iterate] at hsteps
          contradiction
      | some next =>
          rw [hstep] at hsteps
          change (stutterStep tm)^[t] ((tm.step c).getD c) = c'
          rw [hstep]
          exact ih hsteps

private theorem iterate_eq_of_fixed {α : Type} (f : α → α) {a : α}
    (hfixed : f a = a) (t : Nat) : f^[t] a = a := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply, hfixed, ih]

private theorem pad_stutter_halted (tm : _root_.Turing.FinTM2)
    {c haltedCfg : tm.Cfg} {steps horizon : Nat}
    (hhalted : haltedCfg.l = none) (hle : steps ≤ horizon)
    (hrun : (stutterStep tm)^[steps] c = haltedCfg) :
    (stutterStep tm)^[horizon] c = haltedCfg := by
  have hsum : horizon - steps + steps = horizon := Nat.sub_add_cancel hle
  rw [← hsum, Function.iterate_add_apply, hrun]
  exact iterate_eq_of_fixed (stutterStep tm)
    (stutterStep_halted tm hhalted) (horizon - steps)

private def oneStepInTime (tm : _root_.Turing.FinTM2) {c next : tm.Cfg}
    (hstep : tm.step c = some next) :
    EvalsToInTime tm.step c (some next) 1 where
  toEvalsTo := ⟨1, by
    simp only [Function.iterate_one, flip]
    exact hstep⟩
  steps_le_m := Nat.le_refl 1

private theorem stutter_iterate_to_evalsToInTime (tm : _root_.Turing.FinTM2)
    {c haltedCfg : tm.Cfg} (_hhalted : haltedCfg.l = none) (horizon : Nat)
    (hrun : (stutterStep tm)^[horizon] c = haltedCfg) :
    Nonempty (EvalsToInTime tm.step c (some haltedCfg) horizon) := by
  induction horizon generalizing c with
  | zero =>
      simp only [Function.iterate_zero_apply] at hrun
      subst c
      exact ⟨EvalsToInTime.refl tm.step haltedCfg⟩
  | succ horizon ih =>
      by_cases hc : c.l = none
      · have hfixed := stutterStep_halted tm hc
        rw [Function.iterate_succ_apply, hfixed,
          iterate_eq_of_fixed (stutterStep tm) hfixed] at hrun
        subst c
        exact ⟨
          { toEvalsTo := (EvalsToInTime.refl tm.step haltedCfg).toEvalsTo
            steps_le_m := Nat.zero_le _ }⟩
      · have hsome : ∃ next, tm.step c = some next := by
          cases hstep : tm.step c with
          | none => exact False.elim (hc ((step_eq_none_iff_label_none tm c).mp hstep))
          | some next => exact ⟨next, rfl⟩
        rcases hsome with ⟨next, hstep⟩
        rw [Function.iterate_succ_apply] at hrun
        have hstutter : stutterStep tm c = next := by
          unfold stutterStep
          rw [hstep]
          rfl
        rw [hstutter] at hrun
        rcases ih hrun with ⟨htail⟩
        exact ⟨EvalsToInTime.trans tm.step 1 horizon c next (some haltedCfg)
          (oneStepInTime tm hstep) htail⟩

/-- A run reaching a halted target within {lit}`horizon` steps is equivalent to an
exact {lit}`horizon`-step stuttering run.  The halted-target premise is essential:
{name}`EvalsToInTime` itself also admits zero-step witnesses for nonhalted targets. -/
theorem evalsToInTime_iff_stutter_accepts (tm : _root_.Turing.FinTM2)
    {c haltedCfg : tm.Cfg} (hhalted : haltedCfg.l = none) (horizon : Nat) :
    Nonempty (EvalsToInTime tm.step c (some haltedCfg) horizon) ↔
      (stutterStep tm)^[horizon] c = haltedCfg := by
  constructor
  · rintro ⟨hrun⟩
    apply pad_stutter_halted tm hhalted hrun.steps_le_m
    exact evalsInSteps_stutter tm hrun.evals_in_steps
  · exact stutter_iterate_to_evalsToInTime tm hhalted horizon

/-- Output witnesses have the same exact-horizon stuttering characterization
at the canonical {name}`Turing.haltList` target. -/
theorem tm2OutputsInTime_iff_stutter_haltList (tm : _root_.Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (horizon : Nat) :
    Nonempty (_root_.Turing.TM2OutputsInTime tm input (some output) horizon) ↔
      (stutterStep tm)^[horizon] (_root_.Turing.initList tm input) =
        _root_.Turing.haltList tm output := by
  exact evalsToInTime_iff_stutter_accepts tm (by rfl) horizon

/-! ## Uniform stack-height bounds -/

/-- Maximum number of pushes onto one selected stack along any complete path
through a statement tree.  Sequential continuations add their pushes and a
branch takes the larger arm. -/
def stmtMaxPushes (tm : _root_.Turing.FinTM2) (selected : tm.K) :
    _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ → Nat
  | push stack _ continuation =>
      (if stack = selected then 1 else 0) + stmtMaxPushes tm selected continuation
  | peek _ _ continuation | pop _ _ continuation | load _ continuation =>
      stmtMaxPushes tm selected continuation
  | branch _ left right =>
      max (stmtMaxPushes tm selected left) (stmtMaxPushes tm selected right)
  | goto _ | halt => 0

/-- One statement path grows the selected stack by at most its complete-path
push count. -/
theorem stepAux_stack_length_le (tm : _root_.Turing.FinTM2)
    (selected : tm.K) (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (state : tm.σ) (stackFn : ∀ k, List (tm.Γ k)) :
    ((_root_.Turing.TM2.stepAux q state stackFn).stk selected).length ≤
      (stackFn selected).length + stmtMaxPushes tm selected q := by
  induction q generalizing state stackFn with
  | push stack emit continuation ih =>
      simp only [_root_.Turing.TM2.stepAux]
      have hbound := ih state (Function.update stackFn stack (emit state :: stackFn stack))
      by_cases heq : stack = selected
      · subst stack
        simpa [stmtMaxPushes, Nat.add_assoc] using hbound
      · simpa [stmtMaxPushes, heq, Function.update_of_ne (Ne.symm heq)] using hbound
  | peek stack update continuation ih =>
      simpa [stmtMaxPushes] using
        ih (update state (stackFn stack).head?) stackFn
  | pop stack update continuation ih =>
      simp only [_root_.Turing.TM2.stepAux]
      have hbound := ih (update state (stackFn stack).head?)
        (Function.update stackFn stack (stackFn stack).tail)
      by_cases heq : stack = selected
      · subst stack
        simp only [Function.update_self] at hbound
        have htail : (stackFn selected).tail.length ≤ (stackFn selected).length := by
          simp
        exact le_trans hbound (Nat.add_le_add_right htail _)
      · simpa [Function.update_of_ne (Ne.symm heq), stmtMaxPushes] using hbound
  | load update continuation ih =>
      simpa [stmtMaxPushes] using ih (update state) stackFn
  | branch test left right ihLeft ihRight =>
      cases htest : test state
      · simp only [_root_.Turing.TM2.stepAux, htest]
        exact le_trans (ihRight state stackFn)
          (Nat.add_le_add_left (Nat.le_max_right _ _) _)
      · simp only [_root_.Turing.TM2.stepAux, htest]
        exact le_trans (ihLeft state stackFn)
          (Nat.add_le_add_left (Nat.le_max_left _ _) _)
  | goto jump => simp [stmtMaxPushes]
  | halt => simp [stmtMaxPushes]

/-- Uniform per-transition push bound, maximized over every finite program
label and every finite stack index. -/
noncomputable def maxPushesPerStep (tm : _root_.Turing.FinTM2) : Nat := by
  letI := tm.ΛFin
  letI := tm.kFin
  classical
  exact Finset.univ.sup fun label : tm.Λ =>
    Finset.univ.sup fun k : tm.K => stmtMaxPushes tm k (tm.m label)

/-- Every program statement's selected-stack count is below the uniform
machine bound. -/
theorem stmtMaxPushes_le_maxPushesPerStep (tm : _root_.Turing.FinTM2)
    (label : tm.Λ) (k : tm.K) :
    stmtMaxPushes tm k (tm.m label) ≤ maxPushesPerStep tm := by
  letI := tm.ΛFin
  letI := tm.kFin
  classical
  unfold maxPushesPerStep
  exact le_trans (Finset.le_sup (f := fun k : tm.K => stmtMaxPushes tm k (tm.m label))
      (Finset.mem_univ k))
    (Finset.le_sup (f := fun label : tm.Λ =>
      Finset.univ.sup fun k : tm.K => stmtMaxPushes tm k (tm.m label))
      (Finset.mem_univ label))

/-- One genuine bundled-machine transition grows each stack by at most the
uniform program bound. -/
theorem step_stack_length_le (tm : _root_.Turing.FinTM2) {c next : tm.Cfg}
    (hstep : tm.step c = some next) (k : tm.K) :
    (next.stk k).length ≤ (c.stk k).length + maxPushesPerStep tm := by
  rcases c with ⟨label, state, stackFn⟩
  cases label with
  | none =>
      simp [_root_.Turing.FinTM2.step, _root_.Turing.TM2.step] at hstep
  | some label =>
      simp only [_root_.Turing.FinTM2.step, _root_.Turing.TM2.step] at hstep
      have hcfg : _root_.Turing.TM2.stepAux (tm.m label) state stackFn = next :=
        Option.some.inj hstep
      subst next
      exact le_trans (stepAux_stack_length_le tm k (tm.m label) state stackFn)
        (Nat.add_le_add_left (stmtMaxPushes_le_maxPushesPerStep tm label k) _)

/-- One total stuttering transition satisfies the same uniform stack bound. -/
theorem stutterStep_stack_length_le (tm : _root_.Turing.FinTM2) (c : tm.Cfg)
    (k : tm.K) :
    ((stutterStep tm c).stk k).length ≤
      (c.stk k).length + maxPushesPerStep tm := by
  cases hstep : tm.step c with
  | none =>
      change (((tm.step c).getD c).stk k).length ≤ _
      rw [hstep]
      simp
  | some next =>
      change (((tm.step c).getD c).stk k).length ≤ _
      rw [hstep]
      exact step_stack_length_le tm hstep k

/-- Iterating the stuttering transition grows each stack by at most the initial
height plus time times the uniform push bound. -/
theorem stutter_iterate_stack_length_le (tm : _root_.Turing.FinTM2)
    (c : tm.Cfg) (t : Nat) (k : tm.K) :
    (((stutterStep tm)^[t] c).stk k).length ≤
      (c.stk k).length + t * maxPushesPerStep tm := by
  induction t generalizing c with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply]
      calc
        (((stutterStep tm)^[t] (stutterStep tm c)).stk k).length ≤
            ((stutterStep tm c).stk k).length + t * maxPushesPerStep tm := ih _
        _ ≤ ((c.stk k).length + maxPushesPerStep tm) +
            t * maxPushesPerStep tm :=
          Nat.add_le_add_right (stutterStep_stack_length_le tm c k) _
        _ = (c.stk k).length + (t + 1) * maxPushesPerStep tm := by
          simp only [Nat.add_mul, one_mul]
          omega

private theorem initList_stack_length_le (tm : _root_.Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((_root_.Turing.initList tm input).stk k).length ≤ input.length := by
  unfold _root_.Turing.initList
  dsimp only
  split
  · next h => cases h; simp
  · simp

/-- The canonical input execution fits the tableau height
{lean}`input.length + t * maxPushesPerStep tm` at row {lit}`t`. -/
theorem stack_length_iterate_le (tm : _root_.Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) (t : Nat) (k : tm.K) :
    (((stutterStep tm)^[t] (_root_.Turing.initList tm input)).stk k).length ≤
      input.length + t * maxPushesPerStep tm := by
  exact le_trans (stutter_iterate_stack_length_le tm
      (_root_.Turing.initList tm input) t k)
    (Nat.add_le_add_right (initList_stack_length_le tm input k) _)

/-- Every row no later than a fixed horizon fits the horizon's uniform
configuration height. -/
theorem stack_length_at_horizon_le (tm : _root_.Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) {t horizon : Nat} (ht : t ≤ horizon)
    (k : tm.K) :
    (((stutterStep tm)^[t] (_root_.Turing.initList tm input)).stk k).length ≤
      input.length + horizon * maxPushesPerStep tm := by
  exact le_trans (stack_length_iterate_le tm input t k)
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ ht) _)

end

end CLRS.Chapter34.Turing.CookLevin
