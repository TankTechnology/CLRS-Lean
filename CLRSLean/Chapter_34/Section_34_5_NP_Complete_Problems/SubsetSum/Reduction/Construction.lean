import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.DigitPacking
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Reduction.VariableBounds

/-!
# The CLRS 3-CNF-SAT to SUBSET-SUM construction

There are two indexed items per variable and three unit slack items per clause.
Variable columns target one; clause columns target four.  Three unit slack
copies are equivalent to the textbook's weight-one and weight-two pair, while
making the finite-item accounting more uniform.
-/

namespace CLRS.Chapter34.SubsetSumReduction

/-- Literal represented by choosing one of a variable's two items. -/
def itemLiteral (index : Nat) (truth : Bool) : Literal :=
  if truth then .pos index else .neg index

/-- The two choice items for every in-range variable. -/
def variableItems (variableCount : Nat) : Finset SubsetSumItem :=
  (Finset.range variableCount).image (fun index => .choice index false) ∪
    (Finset.range variableCount).image (fun index => .choice index true)

/-- Three unit slack copies for every clause. -/
def slackItems (clauseCount : Nat) : Finset SubsetSumItem :=
  ((Finset.range clauseCount).product (Finset.range 3)).image
    (fun pair => .slack pair.1 pair.2)

/-- All candidate items generated from a CNF formula. -/
def reductionItems (formula : CNF) : Finset SubsetSumItem :=
  variableItems (cnfVarCount formula) ∪ slackItems formula.length

@[simp] theorem variable_mem_variableItems_iff
    (variableCount index : Nat) (truth : Bool) :
    .choice index truth ∈ variableItems variableCount ↔ index < variableCount := by
  cases truth <;> simp [variableItems]

@[simp] theorem slack_mem_slackItems_iff
    (clauseCount clause slot : Nat) :
    .slack clause slot ∈ slackItems clauseCount ↔
      clause < clauseCount ∧ slot < 3 := by
  simp [slackItems]

@[simp] theorem choice_not_mem_slackItems
    (clauseCount index : Nat) (truth : Bool) :
    .choice index truth ∉ slackItems clauseCount := by
  simp [slackItems]

@[simp] theorem slack_not_mem_variableItems
    (variableCount clause slot : Nat) :
    .slack clause slot ∉ variableItems variableCount := by
  simp [variableItems]

theorem mem_reductionItems_iff {formula : CNF} {item : SubsetSumItem} :
    item ∈ reductionItems formula ↔
      (∃ index truth, item = .choice index truth ∧
        index < cnfVarCount formula) ∨
      (∃ clause slot, item = .slack clause slot ∧
        clause < formula.length ∧ slot < 3) := by
  cases item with
  | choice index truth =>
      simp [reductionItems]
  | slack clause slot =>
      simp [reductionItems]

/-- Number of decimal columns in the constructed instance. -/
def reductionWidth (formula : CNF) : Nat :=
  cnfVarCount formula + formula.length

/-- Width of one binary column block.  The three spare bits make the
power-of-two radix larger than every possible selected column sum. -/
def reductionBlockWidth (formula : CNF) : Nat :=
  (reductionItems formula).card + 3

/-- A carry-free power-of-two radix.  Choosing a binary radix keeps the
textbook column construction directly serializable as fixed-width bit
blocks, without requiring a general multiplication routine in the reduction
machine. -/
def reductionBase (formula : CNF) : Nat :=
  2 ^ reductionBlockWidth formula

/-- The digit contributed by one generated item to one column. -/
def itemDigit (formula : CNF) (item : SubsetSumItem) (column : Nat) : Nat :=
  match item with
  | .choice index truth =>
      if column < cnfVarCount formula then
        if column = index then 1 else 0
      else
        (formula.getD (column - cnfVarCount formula) []).count
          (itemLiteral index truth)
  | .slack clause _ =>
      if column < cnfVarCount formula then 0
      else if column - cnfVarCount formula = clause then 1 else 0

/-- Target digit: one in every variable column and four in every clause column. -/
def targetDigit (formula : CNF) (column : Nat) : Nat :=
  if column < cnfVarCount formula then 1 else 4

/-- Natural-number value assigned to a generated item. -/
def itemValue (formula : CNF) (item : SubsetSumItem) : Nat :=
  packColumns (reductionBase formula) (reductionWidth formula)
    (itemDigit formula item)

/-- The packed target natural number. -/
def reductionTarget (formula : CNF) : Nat :=
  packColumns (reductionBase formula) (reductionWidth formula)
    (targetDigit formula)

/-- The finite indexed SUBSET-SUM instance produced from a CNF formula. -/
def cnfToSubsetSum (formula : CNF) : SubsetSumInstance where
  items := reductionItems formula
  value := itemValue formula
  target := reductionTarget formula

@[simp] theorem itemDigit_variable_column
    (formula : CNF) {index column : Nat} (truth : Bool)
    (hcolumn : column < cnfVarCount formula) :
    itemDigit formula (.choice index truth) column =
      if column = index then 1 else 0 := by
  simp [itemDigit, hcolumn]

@[simp] theorem itemDigit_slack_variable_column
    (formula : CNF) {clause slot column : Nat}
    (hcolumn : column < cnfVarCount formula) :
    itemDigit formula (.slack clause slot) column = 0 := by
  simp [itemDigit, hcolumn]

@[simp] theorem itemDigit_variable_clause_column
    (formula : CNF) {index clause : Nat} (truth : Bool) :
    itemDigit formula (.choice index truth)
        (cnfVarCount formula + clause) =
      (formula.getD clause []).count (itemLiteral index truth) := by
  simp [itemDigit]

@[simp] theorem itemDigit_slack_clause_column
    (formula : CNF) {sourceClause slot clause : Nat} :
    itemDigit formula (.slack sourceClause slot)
        (cnfVarCount formula + clause) =
      if clause = sourceClause then 1 else 0 := by
  simp [itemDigit]

@[simp] theorem targetDigit_variable_column
    (formula : CNF) {column : Nat} (hcolumn : column < cnfVarCount formula) :
    targetDigit formula column = 1 := by
  simp [targetDigit, hcolumn]

@[simp] theorem targetDigit_clause_column
    (formula : CNF) (clause : Nat) :
    targetDigit formula (cnfVarCount formula + clause) = 4 := by
  simp [targetDigit]

end CLRS.Chapter34.SubsetSumReduction
