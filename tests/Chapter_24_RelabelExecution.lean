import CLRSLean.FourthEdition.Chapter_24.Section_24_5_Relabel_To_Front.Execution
import CLRSLean.Audit.Axioms

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 1000
namespace RelabelExecutionTests
open CLRS.Chapter26 CLRS.Chapter26.RelabelExecution
open Finset

noncomputable def bottleneck : FlowNetwork (Fin 3) where
  c u v := if u = 0 ∧ v = 1 then 5 else if u = 1 ∧ v = 2 then 2 else 0
  s := 0
  t := 2
  hc_nonneg := by intro u v; split_ifs <;> norm_num
  hc_self := by intro u; fin_cases u <;> norm_num [Fin.ext_iff]
  hs_ne_t := by decide

@[simp] theorem bottleneck_c (u v : Fin 3) : bottleneck.c u v =
    if u = 0 ∧ v = 1 then 5 else if u = 1 ∧ v = 2 then 2 else 0 := rfl
@[simp] theorem bottleneck_s : bottleneck.s = 0 := rfl
@[simp] theorem bottleneck_t : bottleneck.t = 2 := rfl

noncomputable def witness : Flow (Fin 3) bottleneck where
  f u v := if (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) then 2 else
    if (u = 1 ∧ v = 0) ∨ (u = 2 ∧ v = 1) then -2 else 0
  hcapacity := by intro u v; fin_cases u <;> fin_cases v <;> norm_num [Fin.ext_iff]
  hskew_symm := by intro u v; fin_cases u <;> fin_cases v <;> norm_num [Fin.ext_iff]
  hconservation := by intro u hs ht; fin_cases u <;> norm_num [ Fin.sum_univ_succ] at * <;> norm_num only [Fin.ext_iff, Fin.coe_ofNat_eq_mod, ite_false, ite_true, false_and, true_and] at *

example : (initialCells bottleneck).2 = 9 := by simp [initialCells]
example : initializationWork bottleneck = 21 := by simp
example : (initialMachine bottleneck).excessCache 1 = 5 := by simp [initialMachine]
example : (initialMachine bottleneck).φ.f 1 0 = -5 := by
  norm_num [ initialMachine, initialPreflow, initialFunction]
example : (scanMinimum (initialPreflow bottleneck) (initialHeight bottleneck) 1 [0,1,2]).2 = 3 := by simp
example : (scanMinimum (initialPreflow bottleneck) (initialHeight bottleneck) 1 [0,1,2]).1 = 0 := by
  norm_num [ scanMinimum, Preflow.residualEdge, Preflow.residualCapacity,
    initialPreflow, initialFunction, initialHeight] <;> norm_num only [Fin.ext_iff, Fin.coe_ofNat_eq_mod, ite_false, ite_true, false_and, true_and]
  exact min_eq_right (by decide)
example : (pushedCache (initialMachine bottleneck) 1 2) 1 = 3 := by
  norm_num [ pushedCache, initialMachine, initialPreflow, initialFunction,
    Preflow.residualCapacity] <;> norm_num [Fin.ext_iff, Function.update]
example : (pushedCache (initialMachine bottleneck) 1 2) 2 = 2 := by
  norm_num [ pushedCache, initialMachine, initialPreflow, initialFunction,
    Preflow.residualCapacity] <;> norm_num [Fin.ext_iff, Function.update]
example : reverseOnto ([3,2] : List Nat) [4,5] = ([2,3,4,5], 2) := rfl

/-- This full initialized run must send exactly the bottleneck capacity, despite
initially saturating the larger source arc and having to return excess. -/
example : (initializedFlow bottleneck).value = 2 := by
  have hlo := initialized_maximum_flow bottleneck witness
  have hhi := Flow.value_le_cut_capacity (initializedFlow bottleneck) (initializedFlow bottleneck)
    ({0,1} : Finset (Fin 3)) (by simp []) (by simp [])
  have hw : witness.value = 2 := by norm_num [ witness, Flow.value, Fin.sum_univ_succ] <;> norm_num only [Fin.ext_iff, Fin.coe_ofNat_eq_mod, ite_false, ite_true, false_and, true_and]
  rw [hw] at hlo
  have hcompl : ({0,1} : Finset (Fin 3))ᶜ = {2} := by ext u; fin_cases u <;> decide
  rw [hcompl] at hhi
  norm_num at hhi
  norm_num only [Fin.ext_iff, Fin.coe_ofNat_eq_mod, ite_false, ite_true, false_and, true_and] at hhi
  linarith

example : (execute (initialMachine bottleneck) (budget (Fin 3))).terminal ≠ none := execute_terminal _
example : initializedWork bottleneck ≤ 23328 := by simpa using initialized_work_le_cubic bottleneck

noncomputable def emptyNetwork : FlowNetwork (Fin 2) where
  c _ _ := 0
  s := 0
  t := 1
  hc_nonneg := by intros; rfl
  hc_self := by intros; rfl
  hs_ne_t := by decide

example : (initializedFlow emptyNetwork).value = 0 := by
  have hhi := Flow.value_le_cut_capacity (initializedFlow emptyNetwork) (initializedFlow emptyNetwork)
    ({0} : Finset (Fin 2)) (by simp [emptyNetwork]) (by simp [emptyNetwork])
  have hlo := Flow.nonneg_of_zero_reverse_cap (initializedFlow emptyNetwork) 0 1 rfl
  have hz := (initializedFlow emptyNetwork).self_zero 0
  norm_num [ emptyNetwork] at hhi
  change (∑ v, (initializedFlow emptyNetwork).f 0 v) = 0
  rw [Fin.sum_univ_two, hz]
  change (∑ v, (initializedFlow emptyNetwork).f 0 v) ≤ 0 at hhi
  rw [Fin.sum_univ_two, hz] at hhi
  linarith

example : (scanMinimum (initialPreflow emptyNetwork) (initialHeight emptyNetwork) 0 []).1 = ⊤ := rfl

example : (execute (initialMachine emptyNetwork) 0).terminal = none := rfl

example : (execute (initialMachine emptyNetwork) 1).steps = 0 := by
  have ht : (initialMachine emptyNetwork).todo = [] := by
    simp only [initialMachine, selectInternal_value]
    apply List.filter_eq_nil_iff.mpr
    intro u _
    fin_cases u <;> simp [Internal, emptyNetwork]
  rw [execute, next]
  split
  · rfl
  · rename_i r he
    split at he
    · cases he
    · rename_i v vs hc
      have hn : ([] : List (Fin 2)) = v :: vs := ht.symm.trans hc
      cases hn

noncomputable def fractional : FlowNetwork (Fin 2) where
  c u v := if u = 0 ∧ v = 1 then 1/2 else 0
  s := 0
  t := 1
  hc_nonneg := by intro u v; split_ifs <;> norm_num
  hc_self := by intro u; fin_cases u <;> norm_num
  hs_ne_t := by decide

noncomputable def fractionalWitness : Flow (Fin 2) fractional where
  f := initialFunction fractional
  hcapacity := initialFunction_capacity fractional
  hskew_symm := initialFunction_skew fractional
  hconservation := by intro u hs ht; fin_cases u <;> simp [fractional] at *

example : (initializedFlow fractional).value = 1/2 := by
  have hlo := initialized_maximum_flow fractional fractionalWitness
  have hw : fractionalWitness.value = 1/2 := by
    norm_num [fractionalWitness, Flow.value, initialFunction, fractional, Fin.sum_univ_two]
  rw [hw] at hlo
  have hhi := Flow.value_le_cut_capacity (initializedFlow fractional) (initializedFlow fractional)
    ({0} : Finset (Fin 2)) (by simp [fractional]) (by simp [fractional])
  have hc : ({0} : Finset (Fin 2))ᶜ = {1} := by ext u; fin_cases u <;> decide
  rw [hc] at hhi
  norm_num [fractional] at hhi
  linarith

end RelabelExecutionTests

open CLRS.Chapter26.RelabelExecution
#assert_axioms initial_valid
#assert_axioms cachedPush_eq
#assert_axioms scannedRelabel_eq
#assert_axioms Trace.toRelabelToFrontRun
#assert_axioms execute_terminal
#assert_axioms initialized_maximum_flow
#assert_axioms initialized_work_le_cubic
#assert_axioms initialized_correct_and_cost
