import CLRSLean.FourthEdition.Chapter_32.Section_32_2_Rabin_Karp

/-!
# Rabin–Karp with a prepared high-position power

Prepare the power once and pass it through every slide. The fixed slide formula
contains no exponentiation or window-length traversal. Power and seed hashing
are counted from their actual recursions. The scan retains the existing
shift/confirmation budget; list window movement, symbol-map evaluation and
bit-operation costs are outside this scalar charge model.
-/
namespace CLRS.Chapter32.RKExecution
variable {α : Type} [BEq α] [DecidableEq α] [LawfulBEq α] [Inhabited α]

def power (d : Nat) : Nat → Nat × Nat
  | 0 => (1,0)
  | m+1 => let prev := power d m; (prev.1*d,prev.2+1)

@[simp] theorem power_value (d m : Nat) : (power d m).1 = d^m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [power, ih, pow_succ]

@[simp] theorem power_multiplications (d m : Nat) : (power d m).2 = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [power, ih]

def hashLoop (d q : Nat) (val : α → Nat) : Nat → Text α → Nat × Nat
  | acc, [] => (acc,0)
  | acc, c::xs =>
    let rest := hashLoop d q val ((acc*d+val c)%q) xs
    (rest.1,rest.2+1)

@[simp] theorem hashLoop_value (d q : Nat) (val : α → Nat) (acc : Nat) (xs : Text α) :
    (hashLoop d q val acc xs).1 = xs.foldl (fun a c => (a*d+val c)%q) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons c xs ih => simp [hashLoop, ih]

@[simp] theorem hashLoop_characters (d q : Nat) (val : α → Nat) (acc : Nat) (xs : Text α) :
    (hashLoop d q val acc xs).2 = xs.length := by
  induction xs generalizing acc with
  | nil => rfl
  | cons c xs ih => simp [hashLoop, ih]

/-- Two multiplications, two additions, one subtraction and two remainders. -/
def slide (d q high leading incoming h : Nat) : Nat :=
  (d*h + incoming + q - (leading*high)%q)%q

/-- With the prepared power, the fixed-operation slide equals the old recurrence. -/
theorem slide_eq (d q : Nat) (val : α → Nat) (h : Nat) (w : Text α) (c : α) :
    slide d q (d^w.length) (val (w.headD default)) (val c) h = slideHash d q val h w c := rfl

structure Scan where
  positions : List Nat
  charges : Nat
  slides : Nat

def run (T P : Text α) (d q : Nat) (val : α → Nat) (high p m : Nat) :
    Nat → Text α → Nat → Text α → Scan
  | s,w,h,[] => ⟨if h == p && matchesAt T P s then [s] else [],1+(if h==p then m else 0),0⟩
  | s,w,h,c::rest =>
    let next := slide d q high (val (w.headD default)) (val c) h
    let tail := run T P d q val high p m (s+1) (w.tail++[c]) next rest
    ⟨if h==p && matchesAt T P s then s::tail.positions else tail.positions,
      (if h==p then m else 0)+1+tail.charges,tail.slides+1⟩

@[simp] theorem run_slides (T P : Text α) (d q : Nat) (val : α → Nat)
    (high p m s : Nat) (w : Text α) (h : Nat) (rest : Text α) :
    (run T P d q val high p m s w h rest).slides = rest.length := by
  induction rest generalizing s w h with
  | nil => rfl
  | cons c rest ih => simp [run, ih]

theorem run_refines (T P : Text α) (d q : Nat) (val : α → Nat)
    (p m s : Nat) (w : Text α) (h : Nat) (rest : Text α)
    (hm : 0 < m) (hw : w.length = m) :
    let r := run T P d q val (d^m) p m s w h rest
    (r.positions,r.charges) = rollingGo T P d q val p m s w h rest := by
  induction rest generalizing s w h with
  | nil => rfl
  | cons c rest ih =>
    have hw' : (w.tail++[c]).length = m := by simp [List.length_tail,hw]; omega
    have hs : slide d q (d^m) (val (w.headD default)) (val c) h = slideHash d q val h w c := by
      rw [← hw]; rfl
    have hr := ih (s+1) (w.tail++[c]) (slideHash d q val h w c) hw'
    simp only [run, hs, rollingGo]
    rw [← hr]
    split <;> rfl

structure Result where
  positions : List Nat
  powerMultiplications : Nat
  hashCharacters : Nat
  slides : Nat
  scanCharges : Nat

def execute (T P : Text α) (d q : Nat) (val : α → Nat) : Result :=
  if P.length = 0 then ⟨List.range (T.length+1),0,0,0,T.length+1⟩
  else if T.length < P.length then ⟨[],0,0,0,0⟩
  else
    let high := power d P.length
    let pattern := hashLoop d q val 0 P
    let window := T.take P.length
    let seed := hashLoop d q val 0 window
    let output := run T P d q val high.1 pattern.1 P.length 0 window seed.1 (T.drop P.length)
    ⟨output.positions,high.2,pattern.2+seed.2,output.slides,output.charges⟩

/-- Scalar preparation plus seven arithmetic primitives per slide and the
shift/confirmation budget. This is not the runtime of list copies or comparisons. -/
def chargedWork (r : Result) : Nat :=
  r.powerMultiplications + 3*r.hashCharacters + 7*r.slides + r.scanCharges

/-- Both seed hashes and the prepared power are charged once. -/
theorem execute_preparation (T P : Text α) (d q : Nat) (val : α → Nat)
    (hP : 0 < P.length) (hT : P.length ≤ T.length) :
    (execute T P d q val).powerMultiplications = P.length ∧
      (execute T P d q val).hashCharacters = 2 * P.length ∧
      (execute T P d q val).slides = T.length - P.length := by
  simp [execute, Nat.ne_of_gt hP, Nat.not_lt.mpr hT, List.length_take, Nat.min_eq_left hT,
    Nat.two_mul]

theorem execute_refines (T P : Text α) (d q : Nat) (val : α → Nat)
    (hP : 0 < P.length) (hT : P.length ≤ T.length) :
    (execute T P d q val).positions = (rabinKarpRolling T P d q val).1 ∧
      P.length + (execute T P d q val).scanCharges = (rabinKarpRolling T P d q val).2 := by
  have hw : (T.take P.length).length = P.length := by simp [Nat.min_eq_left hT]
  have hr := run_refines T P d q val (hash d q val P) P.length 0 (T.take P.length)
    (hash d q val (T.take P.length)) (T.drop P.length) hP hw
  have hpos := congrArg Prod.fst hr
  have hcost := congrArg Prod.snd hr
  simp only at hpos hcost
  simp only [execute, Nat.ne_of_gt hP, Nat.not_lt.mpr hT, ↓reduceIte,
    power_value, hashLoop_value, rabinKarpRolling]
  change _ = _ ∧ _ = _
  simp only [hash] at hpos hcost
  exact ⟨hpos, congrArg (P.length + ·) hcost⟩

/-- Actual cached-power execution returns every and only matching shift. -/
theorem execute_correct (T P : Text α) (d q : Nat) (val : α → Nat) (hq : 0 < q) :
    (execute T P d q val).positions = naiveMatcher T P := by
  by_cases hempty : P.length = 0
  · have hp : P = [] := by cases P <;> simp_all
    subst P
    simp [execute, naiveMatcher]
  · by_cases hlong : T.length < P.length
    · simp [execute, hempty, hlong, naiveMatcher_pattern_too_long T P hlong]
    · have he := (execute_refines T P d q val (by omega) (by omega)).1
      exact he.trans (rabinKarpRollingMatches_correct T P d q val hq)

/-- Exact connection to the established shift/confirmation charge, with newly
counted preparation and constant arithmetic per slide. -/
theorem execute_chargedWork (T P : Text α) (d q : Nat) (val : α → Nat)
    (hP : 0 < P.length) (hT : P.length ≤ T.length) :
    chargedWork (execute T P d q val) =
      6 * P.length + 7 * (T.length-P.length) + (rabinKarpRolling T P d q val).2 := by
  obtain ⟨hpow,hhash,hslides⟩ := execute_preparation T P d q val hP hT
  have hcost := (execute_refines T P d q val hP hT).2
  simp only [chargedWork, hpow, hhash, hslides]
  omega

end CLRS.Chapter32.RKExecution
