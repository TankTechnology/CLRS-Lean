import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StackPrimitives

/-!
# CLRS Section 34.4 - Canonical bounded-stack semantics

This module connects pure Boolean stack primitives to canonical bounded-stack
codes and lists over the original machine alphabet.

Main results:

- {lit}`StackBits.Represents` packages a canonical bounded-stack code, its
  exact Boolean encoding, and its decoded machine-alphabet list.
- {lit}`pushStackBits_represents`, {lit}`peekStackBits_represents`, and
  {lit}`popStackBits_represents` give list-level semantics to the pure stack
  primitives.
- {lit}`evalBundle_stack_represents` projects a successfully decoded complete
  tableau row to the semantic representation of each machine stack.

Current gaps:

- Circuit allocation and recursive statement semantics are supplied by the
  downstream {lit}`StackCircuits` and {lit}`StatementCircuits` layers;
  {lit}`TransitionCircuits` supplies finite-label dispatch and local correctness.
- Fresh row allocation and exact boundary constraints are supplied downstream;
  polynomial bounds and verified whole-tableau assembly remain.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Canonical Boolean encodings -/

/-- Project a bounded stack code to one-hot Boolean height and cell bundles. -/
def encodeBoundedStackBits {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (code : BoundedStack (reachableAlphabet tm k).card W) : StackBits tm W k where
  height := encodeOneHot code.height
  cell i := encodeOneHot (code.cells i)

/-- The height projection selects exactly the bounded code's height. -/
@[simp] theorem encodeBoundedStackBits_height
    {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (code : BoundedStack (reachableAlphabet tm k).card W)
    (height : Fin (W + 1)) :
    (encodeBoundedStackBits code).height height =
      encodeOneHot code.height height := rfl

/-- Every cell projection selects exactly the bounded code's symbol code. -/
@[simp] theorem encodeBoundedStackBits_cell
    {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (code : BoundedStack (reachableAlphabet tm k).card W) (cell : Fin W)
    (symbol : Fin ((reachableAlphabet tm k).card + 1)) :
    (encodeBoundedStackBits code).cell cell symbol =
      encodeOneHot (code.cells cell) symbol := rfl

/-- Every projected bounded stack is raw one-hot decodable. -/
theorem encodeBoundedStackBits_rawDecodable
    {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (code : BoundedStack (reachableAlphabet tm k).card W) :
    (encodeBoundedStackBits code).RawDecodable := by
  refine ⟨oneHot_encodeOneHot code.height, ?_⟩
  intro i
  exact oneHot_encodeOneHot (code.cells i)

/-! ## Representation relation -/

namespace StackBits

namespace Represents

/-- Proof-carrying data witnessing that one Boolean stack represents one
machine-alphabet list. -/
structure Witness {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (stack : StackBits tm W k) (xs : List (tm.Γ k)) where
  /-- Canonical finite stack code underlying the Boolean bundle. -/
  code : BoundedStack (reachableAlphabet tm k).card W
  /-- The finite code has an active nonblank prefix and blank suffix. -/
  valid : code.Valid
  /-- The Boolean bundle is exactly the one-hot projection of the code. -/
  bits_eq : stack = encodeBoundedStackBits code
  /-- Proof-indexed decoding returns the represented original-alphabet list. -/
  decode_eq : decodeBoundedStack tm k code valid = xs

end Represents

/-- A Boolean stack represents a machine-alphabet list when there is
proof-carrying data showing that it is exactly the one-hot projection of a
valid bounded-stack code whose proof-indexed decoding is that list. -/
def Represents {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (stack : StackBits tm W k) (xs : List (tm.Γ k)) : Prop :=
  Nonempty (Represents.Witness stack xs)

namespace Represents

/-- Every semantically represented stack is independently one-hot decodable. -/
theorem rawDecodable {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    {stack : StackBits tm W k} {xs : List (tm.Γ k)}
    (hrep : stack.Represents xs) : stack.RawDecodable := by
  rcases hrep with ⟨⟨code, _, hbits, _⟩⟩
  rw [hbits]
  exact encodeBoundedStackBits_rawDecodable code

/-- Encoding a supported list that fits the fixed width gives its canonical
Boolean representation. -/
theorem of_encode {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (xs : List (tm.Γ k))
    (halphabet : ∀ a, a ∈ xs → a ∈ reachableAlphabet tm k)
    (hheight : xs.length ≤ W) :
    (encodeBoundedStackBits
      (encodeBoundedStack tm k xs halphabet hheight)).Represents xs := by
  exact ⟨
    { code := encodeBoundedStack tm k xs halphabet hheight
      valid := encodeBoundedStack_valid tm k xs halphabet hheight
      bits_eq := rfl
      decode_eq := decodeBoundedStack_encode tm k xs halphabet hheight }⟩

/-- Every semantic representation normalizes to an encoding of its represented
list, for suitable support and width proofs. -/
theorem eq_encode {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    {stack : StackBits tm W k} {xs : List (tm.Γ k)}
    (hrep : stack.Represents xs) :
    ∃ (halphabet : ∀ a, a ∈ xs → a ∈ reachableAlphabet tm k)
      (hheight : xs.length ≤ W),
      stack = encodeBoundedStackBits
        (encodeBoundedStack tm k xs halphabet hheight) := by
  rcases hrep with ⟨⟨code, hvalid, hbits, hdecode⟩⟩
  subst xs
  let halphabet : ∀ a,
      a ∈ decodeBoundedStack tm k code hvalid →
        a ∈ reachableAlphabet tm k := by
    intro a ha
    simp only [decodeBoundedStack, List.mem_ofFn] at ha
    rcases ha with ⟨i, rfl⟩
    exact (alphabetEquivFin tm k).symm
      ⟨(code.cells (code.activeIndex i)).val,
        (hvalid (code.activeIndex i)).mpr i.isLt⟩ |>.property
  let hheight : (decodeBoundedStack tm k code hvalid).length ≤ W := by
    rw [decodeBoundedStack_length]
    exact Nat.le_of_lt_succ code.height.isLt
  refine ⟨halphabet, hheight, ?_⟩
  have hcode := encodeBoundedStack_decode tm k code hvalid
  rw [hbits]
  exact congrArg encodeBoundedStackBits hcode.symm

end Represents

end StackBits

/-- A represented stack has room for one more symbol exactly when its decoded
list is strictly shorter than the fixed width, including width zero. -/
theorem represents_hasCapacity_iff
    {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    {stack : StackBits tm W k} {xs : List (tm.Γ k)}
    (hrep : stack.Represents xs) :
    stack.HasCapacity ↔ xs.length < W := by
  rcases hrep.eq_encode with ⟨halphabet, hheight, hbits⟩
  rw [hbits]
  simp [StackBits.HasCapacity, encodeBoundedStackBits, encodeBoundedStack,
    encodeOneHot, Fin.ext_iff]
  omega

private theorem encodeAlphabetSymbol_eq_encodeHeadCode
    {tm : _root_.Turing.FinTM2} {k : tm.K}
    (symbol : SupportedSymbol tm k) :
    encodeAlphabetSymbol tm k symbol.val symbol.property =
      encodeHeadCode (some symbol) := by
  apply Fin.ext
  rfl

/-! ## List semantics of pure stack operations -/

/-- Peeking a represented stack decodes exactly to the list head, with an empty
list producing the well-formed inner {lean}`none`. -/
theorem peekStackBits_represents
    {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    {stack : StackBits tm W k} {xs : List (tm.Γ k)}
    (hrep : stack.Represents xs) :
    decodeHeadValue? (peekStackBits W stack) = some xs.head? := by
  rcases hrep.eq_encode with ⟨halphabet, hheight, hbits⟩
  rw [hbits]
  cases W with
  | zero =>
      have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst xs
      simp
  | succ W =>
      cases xs with
      | nil =>
          simp [peekStackBits, encodeBoundedStackBits, encodeBoundedStack]
          change decodeHeadValue? (encodeHeadBits (tm := tm) (k := k) none) =
            some none
          simp
      | cons symbol tail =>
          let supported : SupportedSymbol tm k :=
            ⟨symbol, halphabet symbol (by simp)⟩
          have hcell :
              (encodeBoundedStackBits
                (encodeBoundedStack tm k (symbol :: tail) halphabet hheight)).cell 0 =
                encodeHeadBits (some supported) := by
            funext code
            simp only [encodeBoundedStackBits, encodeBoundedStack]
            rw [dif_pos (by simp)]
            change encodeOneHot (encodeAlphabetSymbol tm k symbol _) code =
              encodeOneHot (encodeHeadCode (some supported)) code
            rw [encodeAlphabetSymbol_eq_encodeHeadCode supported]
          rw [peekStackBits_of_pos, hcell]
          simp [supported]

/-- Popping an exactly encoded bounded stack produces the exact canonical
encoding of its list tail. -/
theorem popStackBits_encodeBoundedStackBits
    {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (xs : List (tm.Γ k))
    (halphabet : ∀ a, a ∈ xs → a ∈ reachableAlphabet tm k)
    (hheight : xs.length ≤ W)
    (htailAlphabet : ∀ a, a ∈ xs.tail → a ∈ reachableAlphabet tm k)
    (htailHeight : xs.tail.length ≤ W) :
    (popStackBits W
      (encodeBoundedStackBits
        (encodeBoundedStack tm k xs halphabet hheight))).stack =
      encodeBoundedStackBits
        (encodeBoundedStack tm k xs.tail htailAlphabet htailHeight) := by
  cases W with
  | zero =>
      have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst xs
      simp
  | succ W =>
      have htailLe : xs.tail.length ≤ W := by
        cases xs with
        | nil => simp
        | cons symbol tail =>
            simp only [List.tail_cons]
            simp only [List.length_cons] at hheight
            omega
      apply StackBundle.ext
      · funext i
        by_cases hizero : i = 0
        · subst i
          rw [popStackBits_height_zero]
          cases xs with
          | nil =>
              simp [encodeBoundedStackBits, encodeBoundedStack, encodeOneHot]
          | cons symbol tail =>
              cases tail with
              | nil =>
                  simp [encodeBoundedStackBits, encodeBoundedStack, encodeOneHot]
              | cons next rest =>
                  simp [encodeBoundedStackBits, encodeBoundedStack, encodeOneHot,
                    Fin.ext_iff]
        · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hizero
          rw [popStackBits_height_succ]
          cases xs with
          | nil =>
              split <;>
                simp [encodeBoundedStackBits, encodeBoundedStack, encodeOneHot]
          | cons symbol tail =>
              split
              next hnext =>
                change encodeOneHot
                    ((encodeBoundedStack tm k (symbol :: tail) halphabet
                      hheight).height)
                      ⟨j.val + 2, hnext⟩ =
                  encodeOneHot
                    ((encodeBoundedStack tm k tail htailAlphabet
                      htailHeight).height) j.succ
                have hequiv :
                    (⟨j.val + 2, hnext⟩ : Fin (W + 2)) =
                        (encodeBoundedStack tm k (symbol :: tail) halphabet
                          hheight).height ↔
                      j.succ =
                        (encodeBoundedStack tm k tail htailAlphabet
                          htailHeight).height := by
                  simp [encodeBoundedStack, Fin.ext_iff]
                by_cases hselected :
                    j.succ =
                      (encodeBoundedStack tm k tail htailAlphabet
                        htailHeight).height
                · have hold := hequiv.mpr hselected
                  simp [encodeOneHot, hold, hselected]
                · have hold :
                      (⟨j.val + 2, hnext⟩ : Fin (W + 2)) ≠
                        (encodeBoundedStack tm k (symbol :: tail) halphabet
                          hheight).height :=
                    fun heq => hselected (hequiv.mp heq)
                  simp [encodeOneHot, hold, hselected]
              next hnext =>
                simp only [List.tail_cons] at htailLe
                have hnotSelected :
                    j.succ ≠
                      (encodeBoundedStack tm k tail htailAlphabet
                        htailHeight).height := by
                  intro heq
                  have hval := congrArg Fin.val heq
                  simp only [Fin.val_succ, encodeBoundedStack] at hval
                  omega
                change false = encodeOneHot
                  ((encodeBoundedStack tm k tail htailAlphabet
                    htailHeight).height) j.succ
                simp [encodeOneHot, hnotSelected]
      · funext i code
        by_cases hnext : i.val + 1 < W + 1
        · rw [popStackBits_cell_of_next _ i hnext]
          change encodeOneHot
              ((encodeBoundedStack tm k xs halphabet hheight).cells
                ⟨i.val + 1, hnext⟩) code =
            encodeOneHot
              ((encodeBoundedStack tm k xs.tail htailAlphabet htailHeight).cells i)
              code
          cases xs with
          | nil => simp [encodeBoundedStack]
          | cons symbol tail =>
              by_cases hactive : i.val < tail.length
              · simp [encodeBoundedStack, hactive]
              · simp [encodeBoundedStack, hactive]
        · have hilast : i = Fin.last W := by
            apply Fin.ext
            simp only [Fin.val_last]
            omega
          subst i
          rw [popStackBits_cell_last]
          have hinactive : ¬ (Fin.last W).val < xs.tail.length := by
            simpa using Nat.not_lt_of_ge htailLe
          have hinactive' : ¬ W < xs.length - 1 := by
            simpa only [Fin.val_last, List.length_tail] using hinactive
          have hcell :
              (encodeBoundedStack tm k xs.tail htailAlphabet
                htailHeight).cells (Fin.last W) =
                encodeHeadCode (tm := tm) (k := k) none := by
            apply Fin.ext
            simp [encodeBoundedStack, hinactive', encodeHeadCode]
          change encodeHeadBits (tm := tm) (k := k) none code =
            encodeOneHot
              ((encodeBoundedStack tm k xs.tail htailAlphabet
                htailHeight).cells (Fin.last W)) code
          rw [hcell]
          rfl

/-- Popping a represented stack represents its list tail and returns the old
list head; popping an empty stack is stable. -/
theorem popStackBits_represents
    {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    {stack : StackBits tm W k} {xs : List (tm.Γ k)}
    (hrep : stack.Represents xs) :
    (popStackBits W stack).stack.Represents xs.tail ∧
      decodeHeadValue? (popStackBits W stack).head = some xs.head? := by
  rcases hrep.eq_encode with ⟨halphabet, hheight, hbits⟩
  let htailAlphabet : ∀ a, a ∈ xs.tail →
      a ∈ reachableAlphabet tm k := by
    intro a ha
    exact halphabet a (List.mem_of_mem_tail ha)
  let htailHeight : xs.tail.length ≤ W := by
    cases xs with
    | nil => simp
    | cons symbol tail =>
        simp only [List.tail_cons]
        simp only [List.length_cons] at hheight
        omega
  constructor
  · rw [hbits]
    rw [popStackBits_encodeBoundedStackBits xs halphabet hheight
      htailAlphabet htailHeight]
    exact StackBits.Represents.of_encode xs.tail htailAlphabet htailHeight
  · rw [popStackBits_head]
    exact peekStackBits_represents hrep

/-- Pushing an exactly encoded supported symbol into a nonfull bounded stack
produces the exact canonical encoding of list cons. -/
theorem pushStackBits_encodeBoundedStackBits
    {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    (symbol : SupportedSymbol tm k) (xs : List (tm.Γ k))
    (halphabet : ∀ a, a ∈ xs → a ∈ reachableAlphabet tm k)
    (hheight : xs.length ≤ W) (hroom : xs.length < W)
    (hconsAlphabet : ∀ a, a ∈ symbol.val :: xs →
      a ∈ reachableAlphabet tm k)
    (hconsHeight : (symbol.val :: xs).length ≤ W) :
    pushStackBits (encodeSymbolBits symbol) W
        (encodeBoundedStackBits
          (encodeBoundedStack tm k xs halphabet hheight)) =
      encodeBoundedStackBits
        (encodeBoundedStack tm k (symbol.val :: xs) hconsAlphabet
          hconsHeight) := by
  cases W with
  | zero => omega
  | succ W =>
      apply StackBundle.ext
      · funext i
        by_cases hizero : i = 0
        · subst i
          simp [pushStackBits, encodeBoundedStackBits, encodeBoundedStack,
            encodeOneHot, Fin.ext_iff]
        · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hizero
          rw [pushStackBits_height_succ]
          simp [encodeBoundedStackBits, encodeBoundedStack, encodeOneHot,
            Fin.ext_iff]
      · funext i code
        by_cases hizero : i = 0
        · subst i
          rw [pushStackBits_cell_zero_encodeSymbol]
          change encodeHeadBits (some symbol) code =
            encodeOneHot
              ((encodeBoundedStack tm k (symbol.val :: xs) hconsAlphabet
                hconsHeight).cells 0) code
          have hcell :
              (encodeBoundedStack tm k (symbol.val :: xs) hconsAlphabet
                hconsHeight).cells 0 = encodeHeadCode (some symbol) := by
            simp only [encodeBoundedStack]
            rw [dif_pos (by simp)]
            exact encodeAlphabetSymbol_eq_encodeHeadCode symbol
          rw [hcell]
          rfl
        · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hizero
          rw [pushStackBits_cell_succ]
          change encodeOneHot
              ((encodeBoundedStack tm k xs halphabet hheight).cells
                j.castSucc) code =
            encodeOneHot
              ((encodeBoundedStack tm k (symbol.val :: xs) hconsAlphabet
                hconsHeight).cells j.succ) code
          by_cases hactive : j.val < xs.length
          · simp [encodeBoundedStack, hactive]
          · simp [encodeBoundedStack, hactive]

/-- Pushing a supported symbol into a represented stack with capacity
represents consing that symbol onto the list. -/
theorem pushStackBits_represents
    {tm : _root_.Turing.FinTM2} {W : Nat} {k : tm.K}
    {stack : StackBits tm W k} {xs : List (tm.Γ k)}
    (hrep : stack.Represents xs) (symbol : SupportedSymbol tm k)
    (hcapacity : stack.HasCapacity) :
    (pushStackBits (encodeSymbolBits symbol) W stack).Represents
      (symbol.val :: xs) := by
  rcases hrep.eq_encode with ⟨halphabet, hheight, hbits⟩
  have hroom : xs.length < W :=
    (represents_hasCapacity_iff hrep).mp hcapacity
  let hconsAlphabet : ∀ a, a ∈ symbol.val :: xs →
      a ∈ reachableAlphabet tm k := by
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact symbol.property
    · exact halphabet a ha
  let hconsHeight : (symbol.val :: xs).length ≤ W := by
    simp only [List.length_cons]
    omega
  rw [hbits]
  rw [pushStackBits_encodeBoundedStackBits symbol xs halphabet hheight hroom
    hconsAlphabet hconsHeight]
  exact StackBits.Represents.of_encode (symbol.val :: xs) hconsAlphabet
    hconsHeight

/-! ## Complete-row projections -/

/-- Projecting one stack from a canonically encoded raw row is exactly the
one-hot projection of that row's bounded stack code. -/
theorem encodeRawCfgBits_stack
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (code : BoundedCfg tm H) (k : tm.K) :
    (encodeRawCfgBits code).stack k =
      encodeBoundedStackBits (code.stack k) := by
  apply StackBundle.ext
  · funext height
    rfl
  · funext cell symbol
    rfl

/-- If a complete row bundle evaluates and canonically decodes to a machine
configuration, each evaluated stack represents the corresponding machine
stack list. -/
theorem evalBundle_stack_represents
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (inputs : Nat → Bool)
    (wires : CfgWires tm H) (hvalid : wires.ValidIn base)
    {c : tm.Cfg} (hdecoded : evalBundle base inputs wires hvalid = some c)
    (k : tm.K) :
    StackBits.Represents ((evalCfgBits base inputs wires).stack k) (c.stk k) := by
  unfold evalBundle evalRawBundle at hdecoded
  cases hraw : decodeRawCfg? (evalCfgBits base inputs wires) with
  | none => simp [hraw] at hdecoded
  | some code =>
      simp only [hraw, Option.bind_some] at hdecoded
      unfold decodeCfg? at hdecoded
      split at hdecoded
      next hcodeValid =>
        have hc : decodeCfg tm code hcodeValid = c := Option.some.inj hdecoded
        have hbits : evalCfgBits base inputs wires = encodeRawCfgBits code :=
          (decodeRawCfg_eq_some_iff (evalCfgBits base inputs wires) code).mp hraw
        refine ⟨
          { code := code.stack k
            valid := hcodeValid.2 k
            bits_eq := ?_
            decode_eq := ?_ }⟩
        · rw [hbits, encodeRawCfgBits_stack]
        · rw [← hc]
          rfl
      next hnotValid => contradiction

end

end CLRS.Chapter34.Turing.CookLevin
