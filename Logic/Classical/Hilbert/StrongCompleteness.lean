import Std
import Logic.Utils.List
import Logic.Classical.Syntax
import Logic.Classical.Semantics
import Logic.Classical.Hilbert.Basic
import Logic.Classical.Hilbert.Completeness

theorem strong_soundness {Γ : Set Fml} {a : Fml} : ProvableFrom Γ a -> ValidUnder Γ a := by
  intro ⟨xs, ⟨s, p⟩⟩ V cond
  have cond : ∀ b ∈ xs, V.isTrue b := by
    intro b bmemxs
    apply s at bmemxs
    specialize cond b
    exact cond bmemxs
  have v : Valid (⋏ xs 🡒 a) := soundness p
  have x : V.isTrue (⋏ xs) := by
    rw [Valuation.isTrue_bigconj]
    exact cond
  exact v x

@[simp, grind] noncomputable def Fml.upto (n : Nat) := { a : Fml | Encodable.encode a ≤ n }

@[simp, grind .] lemma Fml.mem_upto {a : Fml} : a ∈ Fml.upto (Encodable.encode a) := by grind

@[simp, grind .] lemma Fml.mem_sUnion_upto_all {a : Fml}
  : a ∈ Set.sUnion { Fml.upto n | n : Nat } := by
  rw [Set.mem_sUnion]
  by_contra hyp
  push Not at hyp
  have i : upto (Encodable.encode a) ∈ {x | ∃ n, upto n = x} := by grind
  have : a ∉ Fml.upto (Encodable.encode a) := hyp (a |> Encodable.encode |> Fml.upto) i
  have : a ∈ Fml.upto (Encodable.encode a) := Fml.mem_upto
  contradiction

@[simp, grind] noncomputable def Tableau.extend_by_code
  (t : Tableau) : Nat -> Tableau
  | 0 =>
    match Encodable.decode (α := Fml) 0 with
    | some a => t.extend a
    | none => t
  | n + 1 =>
    let tn := t.extend_by_code n
    match Encodable.decode (α := Fml) (n + 1) with
    | some a => tn.extend a
    | none => tn

@[simp] lemma Tableau.mem_extend_by_code_abs {t : Tableau} {n : Nat} {a : Fml}
  : Encodable.encode a = n -> a ∈ (t.extend_by_code n).abs := by
  intro eq
  induction n with
  | zero =>
    simp only [extend_by_code, <- eq, Encodable.encodek, extend_is_insert, Set.mem_insert]
  | succ n =>
    simp only [extend_by_code, <- eq, Encodable.encodek, extend_is_insert, Set.mem_insert]

@[simp, grind .] lemma Tableau.extend_by_code_is_monotone {t : Tableau} {n_1 n_2 : Nat}
  : n_1 ≤ n_2 -> t.extend_by_code n_1 ⊆ t.extend_by_code n_2 := by
  intro le
  induction le with
  | refl => trivial
  | step le ih =>
    trans
    · exact ih
    · simp only [extend_by_code, · ⊆ ·, Tableau.HasSubset]
      simp only [Set.le_iff_subset]
      split
      · grind
      · grind

lemma Tableau.extend_by_code_is_consistent {t : Tableau} {n : Nat}
  : t.Consistent -> (t.extend_by_code n).Consistent := by
  induction n with
  | zero =>
    simp only [extend_by_code]
    split
    · exact extend_is_consistent
    · exact id
  | succ n ih =>
    simp only [extend_by_code]
    split
    · trans
      · exact ih
      · exact extend_is_consistent
    · exact ih

@[simp, grind] noncomputable def Tableau.maximal (t : Tableau) : Tableau :=
  Tableau.iUnion t.extend_by_code

@[simp, grind .] lemma Tableau.sub_maximal {t : Tableau} : t ⊆ t.maximal := by
  simp only [maximal, Tableau.iUnion, Tableau.sub_iff]
  constructor
  case left =>
    rw [Set.subset_def]
    intro a a_mem_t_1
    simp only [Set.mem_iUnion]
    exists 0
    dsimp
    split
    · simp only [extend]
      split
      · grind
      · grind
    · exact a_mem_t_1
  case right =>
    rw [Set.subset_def]
    intro a a_mem_t_2
    simp only [Set.mem_iUnion]
    exists 0
    dsimp
    split
    · simp only [extend]
      split
      · grind
      · grind
    · exact a_mem_t_2

@[simp, grind =] lemma Tableau.mem_maximal_1_iff {t : Tableau} {a : Fml}
  : a ∈ t.maximal.1 <-> ∃ n, a ∈ (t.extend_by_code n).1 := by
  simp only [maximal, Tableau.iUnion, Set.mem_iUnion]
  grind

@[simp, grind =] lemma Tableau.mem_maximal_2_iff {t : Tableau} {a : Fml}
  : a ∈ t.maximal.2 <-> ∃ n, a ∈ (t.extend_by_code n).2 := by
  simp only [maximal, Tableau.iUnion, Set.mem_iUnion]
  grind

@[simp, grind =] lemma Tableau.mem_maximal_iff {t : Tableau} {a : Fml}
  : a ∈ t.maximal.abs <-> ∃ n, a ∈ (t.extend_by_code n).abs := by
  simp only [maximal, Tableau.iUnion, Tableau.abs, Set.mem_union, Set.mem_iUnion]
  grind

@[simp, grind .] lemma Tableau.extend_by_code_sub_maximal {t : Tableau} {n : Nat}
  : t.extend_by_code n ⊆ t.maximal := by
  simp only [maximal, Tableau.sub_iUnion]

@[simp, grind .] lemma Tableau.mem_maximal_abs {t : Tableau}
  : ∀ a, a ∈ t.maximal.abs := by
  intro a
  rw [mem_maximal_iff]
  exists Encodable.encode a
  exact mem_extend_by_code_abs (by trivial)

@[simp] lemma Tableau.maximal_is_partially_disjoint {t : Tableau} {a : Fml}
  : t.Consistent -> ¬ (a ∈ t.maximal.1 ∧ a ∈ t.maximal.2) := by
  intro tcon
  by_contra cond
  obtain ⟨m, a_mem_m_1⟩ := mem_maximal_1_iff.mp cond.left
  obtain ⟨n, a_mem_n_2⟩ := mem_maximal_2_iff.mp cond.right
  let k := max m n
  let u := t.extend_by_code k
  have n_le_k : n ≤ k := by grind
  have : a ∈ u.1 ∧ a ∈ u.2 := by
    constructor
    case left =>
      have m_le_k : m ≤ k := by grind
      have m_sub_k := extend_by_code_is_monotone (t := t) m_le_k
      rw [sub_iff] at m_sub_k
      exact m_sub_k.left a_mem_m_1
    case right =>
      have n_le_k : n ≤ k := by grind
      have n_sub_k := extend_by_code_is_monotone (t := t) n_le_k
      rw [sub_iff] at n_sub_k
      exact n_sub_k.right a_mem_n_2
  have : ¬ (a ∈ u.1 ∧ a ∈ u.2) := by
    have d : (t.extend_by_code k).Disjoint :=
      consistent_is_disjoint (extend_by_code_is_consistent tcon)
    exact disjoint_imp_not_mem_both a d
  contradiction

@[simp] lemma Tableau.isSubset_maximal_iff {t : Tableau} {xs : List Fml} :
  List.IsSubset xs t.maximal.abs <-> ∃ n, List.IsSubset xs (t.extend_by_code n).abs := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
    simp only [List.cons_IsSubset]
    constructor
    case mpr =>
      intro r
      have ⟨n, cond⟩ := r
      have ex : ∃ n, List.IsSubset tail (t.extend_by_code n).abs := by
        exists n
        exact cond.right
      refine ⟨?_, ih.mpr ex⟩
      exact mem_maximal_abs head
    case mp =>
      intro l
      let ⟨n, ncond⟩ := ih.mp l.right
      let m := Encodable.encode head
      by_cases le : m ≤ n
      case pos =>
        exists n
        refine ⟨?_, ncond⟩
        rw [abs, Set.mem_union]
        let sub : t.extend_by_code m ⊆ t.extend_by_code n := extend_by_code_is_monotone (t := t) le
        rw [Tableau.sub_iff] at sub
        let mem : head ∈ (t.extend_by_code m).abs :=
          mem_extend_by_code_abs (t := t) (n := m) (a := head) (by trivial)
        rw [abs, Set.mem_union] at mem
        cases mem
        case inl mem =>
          left
          exact Set.mem_of_subset_of_mem sub.left mem
        case inr mem =>
          right
          exact Set.mem_of_subset_of_mem sub.right mem
      case neg =>
        rw [Nat.not_le] at le
        have le : n ≤ m := by
          exact Nat.le_iff_lt_or_eq.mpr (Or.inl le)
        exists m
        refine ⟨mem_extend_by_code_abs (by trivial), ?_⟩
        have sub := extend_by_code_is_monotone (t := t) le |> abs_subset
        exact List.IsSubset_subset ncond sub

theorem Tableau.maximal_is_consistent {t : Tableau}
  : t.Consistent -> t.maximal.Consistent := by
  intro tcon
  by_contra h
  simp only [not_forall, not_not] at h
  obtain ⟨xs, xs_sub_maximal_2, ys, ys_sub_maximal_1, p⟩ := h
  have xs_sub_maximal : List.IsSubset xs t.maximal.abs := by grind
  have ys_sub_maximal : List.IsSubset ys t.maximal.abs := by grind
  let ⟨m, mcond⟩ :=
    isSubset_maximal_iff.mp (List.append_IsSubset.mp ⟨xs_sub_maximal, ys_sub_maximal⟩)
  let u := t.extend_by_code m
  suffices uncon : ¬ u.Consistent from by
    have : u.Consistent := extend_by_code_is_consistent tcon
    contradiction
  have u_sub_maximal : u ⊆ t.maximal := extend_by_code_sub_maximal
  have ⟨xs_sub_u, ys_sub_u⟩ := List.append_IsSubset.mpr mcond
  have xs_sub_u_2 : List.IsSubset xs u.2 := by
    intro a a_mem_xs
    by_contra a_nmem_u_2
    let a_mem_u := xs_sub_u a a_mem_xs
    rw [abs, Set.mem_union] at a_mem_u
    have : a ∈ t.maximal.1 ∧ a ∈ t.maximal.2 := by
      constructor
      case left =>
        have a_mem_u_1 := Or.resolve_right a_mem_u a_nmem_u_2
        have sub : u.1 ⊆ t.maximal.1 := by
          exact u_sub_maximal.left
        apply Set.mem_of_subset_of_mem sub
        exact a_mem_u_1
      case right =>
        exact xs_sub_maximal_2 a a_mem_xs
    have : ¬ (a ∈ t.maximal.1 ∧ a ∈ t.maximal.2) := maximal_is_partially_disjoint tcon
    contradiction
  have ys_sub_u_1 : List.IsSubset ys u.1 := by
    intro a a_mem_ys
    by_contra a_nmem_u_1
    let a_mem_u := ys_sub_u a a_mem_ys
    rw [abs, Set.mem_union] at a_mem_u
    have : a ∈ t.maximal.1 ∧ a ∈ t.maximal.2 := by
      constructor
      case right =>
        have a_mem_u_2 := Or.resolve_left a_mem_u a_nmem_u_1
        have sub : u.2 ⊆ t.maximal.2 := by
          exact u_sub_maximal.right
        apply Set.mem_of_subset_of_mem sub
        exact a_mem_u_2
      case left =>
        exact ys_sub_maximal_1 a a_mem_ys
    have : ¬ (a ∈ t.maximal.1 ∧ a ∈ t.maximal.2) := maximal_is_partially_disjoint tcon
    contradiction
  rw [Consistent]
  push Not
  exists xs
  refine ⟨xs_sub_u_2, ?_⟩
  exists ys

lemma Tableau.maximal_is_closed {t : Tableau}
  : t.maximal.Closed := by grind

theorem strong_completeness {Γ : Theory} {a : Fml}
  : ValidUnder Γ a -> ProvableFrom Γ a := by
  contrapose
  intro npa
  let t : Tableau := (Γ, {a})
  have extendable : ∃ (t': Tableau), t ⊆ t' ∧ t'.Disjoint ∧ t'.Saturated := by
    exists t.maximal
    have cont : t.Consistent := by
      intro xs sub
      have eq : t.1 = Γ := by dsimp
      rw [eq]
      by_contra pxs
      have fa : ∀ x ∈ xs, x = a := sub
      let pxsa : ProvableFrom Γ (⋎ xs 🡒 a) :=
        Provable.bigdisj_e_same fa
        |> provable_iff_provableFromEmpty.mp
        |> ProvableFrom.weakening (by simp)
      have : ProvableFrom Γ a := ProvableFrom.mp pxsa pxs
      contradiction
    have conmax := Tableau.maximal_is_consistent cont
    exact ⟨
      Tableau.sub_maximal,
      Tableau.consistent_is_disjoint conmax,
      Tableau.consistent_and_closed_is_saturated conmax Tableau.maximal_is_closed
    ⟩
  have ⟨V, vtrue, vfalse⟩ := Tableau.realizable_iff_extendable.mpr extendable
  rw [not_forall]
  exists V
  push Not
  constructor
  case right =>
    have mem : a ∈ t.2 := by
      simp only [t, Set.mem_singleton_iff]
    apply vfalse at mem
    exact mem
  case left =>
    exact vtrue
