import Mathlib

/-!
# CLRS Section 11.1 - Direct-address tables

This section models a direct-address table as a total function from natural
keys to optional values.  This is the mathematical core of the CLRS operations:
search reads the key slot, insert overwrites that slot, and delete clears it.

Main results:

- Theorem {lit}`search_insert_same`: searching the inserted key returns the new
  value.
- Theorem {lit}`search_insert_other`: inserting at one key leaves other keys
  unchanged.
- Theorem {lit}`search_delete_same`: deleting a key clears that key.

Current gaps:

- None for the functional direct-address model.  Array bounds and RAM costs are
  deferred to a future execution model.
-/

namespace CLRS
namespace Chapter11

/-! ## Direct-address table model -/

/-- A direct-address table maps each natural key to an optional value. -/
abbrev DirectAddressTable (V : Type u) := Nat → Option V

/-- The empty direct-address table. -/
def emptyDirectAddressTable : DirectAddressTable V :=
  fun _ => none

/-- Search a direct-address table by reading the corresponding slot. -/
def directSearch (T : DirectAddressTable V) (key : Nat) : Option V :=
  T key

/-- Insert overwrites the slot at `key`. -/
def directInsert (key : Nat) (value : V)
    (T : DirectAddressTable V) : DirectAddressTable V :=
  fun j => if j = key then some value else T j

/-- Delete clears the slot at `key`. -/
def directDelete (key : Nat)
    (T : DirectAddressTable V) : DirectAddressTable V :=
  fun j => if j = key then none else T j

/-! ## Operation correctness -/

/-- Searching the inserted key returns the inserted value. -/
theorem search_insert_same (key : Nat) (value : V)
    (T : DirectAddressTable V) :
    directSearch (directInsert key value T) key = some value := by
  simp [directSearch, directInsert]

/-- Inserting at one key leaves every other key unchanged. -/
theorem search_insert_other {key other : Nat} (h : other ≠ key)
    (value : V) (T : DirectAddressTable V) :
    directSearch (directInsert key value T) other = directSearch T other := by
  simp [directSearch, directInsert, h]

/-- Deleting a key makes search at that key return `none`. -/
theorem search_delete_same (key : Nat) (T : DirectAddressTable V) :
    directSearch (directDelete key T) key = none := by
  simp [directSearch, directDelete]

/-- Deleting one key leaves every other key unchanged. -/
theorem search_delete_other {key other : Nat} (h : other ≠ key)
    (T : DirectAddressTable V) :
    directSearch (directDelete key T) other = directSearch T other := by
  simp [directSearch, directDelete, h]

/-- Searching an empty direct-address table returns `none`. -/
theorem search_empty (key : Nat) :
    directSearch (emptyDirectAddressTable : DirectAddressTable V) key = none := by
  rfl

end Chapter11
end CLRS
