import Std
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

namespace List

@[simp] abbrev IsSubset {a} (xs : List a) (ys : Set a) : Prop := (∀ a ∈ xs, a ∈ ys)

@[simp] theorem empty_IsSubset {a} {xs : Set a} : List.IsSubset [] xs := by simp

@[simp] theorem cons_IsSubset {a} {x : a} {xs : List a} {ys : Set a}
  : List.IsSubset (x :: xs) ys <-> x ∈ ys ∧ List.IsSubset xs ys := by grind

@[simp] theorem append_IsSubset {a} {xs ys : List a} {zs : Set a}
  : List.IsSubset xs zs ∧ List.IsSubset ys zs <-> List.IsSubset (xs ++ ys) zs := by grind

@[simp] theorem IsSubset_subset {a} {xs : List a} {ys zs : Set a}
  : List.IsSubset xs ys -> ys ⊆ zs -> List.IsSubset xs zs := by grind

@[simp] theorem IsSubset_empty_is_nil {a} {xs : List a}
  : List.IsSubset xs ∅ -> xs = [] := by
  intro sub
  rw [List.eq_nil_iff_forall_not_mem]
  intro x
  simp only [IsSubset] at sub
  specialize sub x
  by_contra mem
  have : x ∈ ∅ := sub mem
  contradiction

@[simp] abbrev SubsetOf {a} (ys : Set a) := { xs : List a // IsSubset xs ys }

@[simp] abbrev remove {a} [DecidableEq a] (xs : List a) (x : a) := xs.filter (· != x)

@[simp] theorem remove_is_subset {a} [DecidableEq a] {xs : List a} {x : a}
  : xs.remove x ⊆ xs := by simp

@[simp] theorem cons_remove_is_supset {a} [DecidableEq a] {xs : List a} {x : a}
  : xs ⊆ x :: xs.remove x := by
  intro y ymem
  rw [List.mem_cons, List.mem_filter]
  if eq : y = x then
    left
    exact eq
  else
    right
    refine ⟨ymem, ?_⟩
    simp only [bne_iff_ne, ne_eq]
    exact eq

@[simp] theorem mem_imp_eq_or_remove {a} [DecidableEq a] {xs : List a} {x : a} {y}
  : y ∈ xs -> y = x ∨ y ∈ xs.remove x := by
  intro ymem
  by_cases eq : y = x
  case pos =>
    left
    exact eq
  case neg =>
    right
    grind

@[simp] theorem not_mem_remove {a} [DecidableEq a] {xs : List a} {x : a}
  : x ∉ xs.remove x := by simp

end List
