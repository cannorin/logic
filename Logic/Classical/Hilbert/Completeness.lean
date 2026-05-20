import Std
import Logic.Utils.List
import Logic.Classical.Syntax.Concrete
import Logic.Classical.Semantics.Concrete
import Logic.Classical.Hilbert.Concrete
import Logic.Classical.Tableau

open Hilbert

theorem soundness {a : Fml} : Provable a -> Valid a := by
  intro h
  induction h.some with
  | k a b =>
    intro V hA _
    exact hA
  | s a b c =>
    intro V hABC hAB hA
    let hBC := hABC hA
    exact (hBC ∘ hAB) hA
  | conj_i a b =>
    intro V hA hB
    exact ⟨hA, hB⟩
  | conj_e1 a b =>
    intro V hAB
    exact hAB.left
  | conj_e2 a b =>
    intro V hAB
    exact hAB.right
  | disj_i1 a b =>
    intro V hA
    exact Or.inl hA
  | disj_i2 a b =>
    intro V hB
    exact Or.inr hB
  | disj_e a b c =>
    intro V hAC hBC hAB
    cases hAB with
    | inl hA => exact hAC hA
    | inr hB => exact hBC hB
  | dne a =>
    intros V hnna
    rw [V.Tarskean.neg, V.Tarskean.neg, not_not] at hnna
    exact hnna
  | mp hAB hA ihAB ihA =>
    intro V
    let ihAB := ihAB (Nonempty.intro hAB)
    let ihA := ihA (Nonempty.intro hA)
    specialize ihAB V
    specialize ihA V
    exact ihAB ihA

lemma bot_is_not_provable : ¬ Provable ⊥ := by
  apply not_imp_not.mpr soundness
  simp

@[simp] abbrev Tableau.Consistent (t : Tableau) :=
  ∀ xs, List.IsSubset xs t.2 -> ¬ ProvableFrom t.1 (⋎ xs)

lemma Tableau.consistent_is_disjoint {t : Tableau} : t.Consistent -> Tableau.Disjoint t := by
  intro con
  constructor
  case right =>
    by_contra mem
    specialize con []
    have e : List.IsSubset [] t.2 := by simp
    have : ¬ ProvableFrom t.1 ⊥ := con e
    have : ProvableFrom t.1 ⊥ := Contextual.initial mem |> Nonempty.intro
    contradiction
  case left =>
    by_contra nonempty
    rw [<- ne_eq] at nonempty
    let ⟨x, xmem⟩ := Set.nonempty_iff_ne_empty.mpr nonempty
    rw [Set.mem_inter_iff] at xmem
    specialize con [x]
    have sub : List.IsSubset [x] t.2 := by
      simp only [List.IsSubset, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
      exact xmem.right
    have : ¬ ProvableFrom t.1 (⋎ [x]) := con sub
    have : ProvableFrom t.1 (⋎ [x]) := by
      let p1 : Proof.Contextual _ _ :=
        Contextual.initial xmem.left
      let p2 : Proof.Contextual _ _ :=
        disj_i1 x ⊥ |> toContextual t.1
      exact Contextual.mp p2 p1 |> Nonempty.intro
    contradiction

@[grind] noncomputable def Tableau.extend (t : Tableau) (a : Fml) := by
  let tl := t.pushL a
  let tr := t.pushR a
  if tlcon : tl.Consistent then
    exact tl
  else
    exact tr

lemma Tableau.extend_is_consistent {t : Tableau} {a : Fml}
  : t.Consistent -> (t.extend a).Consistent := by
  intro tcon
  simp only [extend]
  split
  case isTrue tlcon => exact tlcon
  case isFalse tlncon =>
    let tl := t.pushL a
    let tr := t.pushR a
    by_contra trncon
    simp only [Tableau.Consistent, not_forall, not_not] at tlncon trncon
    have ⟨xs, xs_sub_tl2, pxs⟩ := tlncon
    have ⟨ys, ys_sub_tr2, pys⟩ := trncon
    wlog a_in_xsr : a ∈ ys
    case inr =>
      have xsrsubt : List.IsSubset ys t.2 := by
        intro x x_in_xsr
        specialize ys_sub_tr2 x
        let x_in_tr2 := ys_sub_tr2 x_in_xsr
        simp only [Set.mem_union, Set.mem_singleton_iff] at x_in_tr2
        cases x_in_tr2 with
        | inr e =>
          rw [<- e] at a_in_xsr
          contradiction
        | inl x_in_t2 => exact x_in_t2
      have : ¬ t.Consistent := by
        rw [not_forall]
        exists ys
        push Not
        constructor
        case left => exact xsrsubt
        case right => trivial
      contradiction
    apply Nonempty.map Contextual.deduction_right at pxs
    let zs := List.remove ys a
    let ws := xs ++ zs
    have p : ProvableFrom tr.1 (⋎ ws) := by
      let h1 : Proof _ := disj_e a (⋎ ws) (⋎ ws) |> imp_exchange
      let h2 : Proof _ := i (⋎ ws)
      let p : Proof.Contextual _ _ := mp h1 h2 |> toContextual tr.1
      let paws : Proof.Contextual tr.1 (a 🡒 ⋎ ws) := by
        have sub : xs ⊆ ws := by
          apply List.subset_append_left
        exact Contextual.syll
          pxs.some
          (bigdisj_i_many sub |> toContextual tr.1)
      let pwsa : Proof.Contextual tr.1 (a ⋎ (⋎ ws)) := by
        have sub : ys ⊆ a :: ws := by
          intro y ymem
          simp only [List.mem_cons, ws, zs]
          suffices cond : y = a ∨ y ∈ ys.remove a from by grind
          exact List.mem_imp_eq_or_remove ymem
        exact Contextual.mp
          (bigdisj_i_many sub |> toContextual tr.1)
          pys.some
      exact Contextual.mp (Contextual.mp p paws) pwsa |> Nonempty.intro
    have sub : List.IsSubset ws t.2 := by
      intro w
      rw [List.mem_append]
      intro mem
      cases mem with
      | inl memxs =>
        apply xs_sub_tl2 at memxs
        trivial
      | inr memzs =>
        have memys : w ∈ ys := by
          apply List.remove_is_subset
          exact memzs
        have ne : w ≠ a := by
          simp [zs] at memzs
          exact memzs.right
        apply ys_sub_tr2 at memys
        simp only [Set.mem_union, Set.mem_singleton_iff] at memys
        cases memys with
        | inl mem => exact mem
        | inr e => contradiction
    have : ¬ t.Consistent := by
      rw [not_forall]
      exists ws
      push Not
      exact ⟨sub, p⟩
    contradiction

@[simp, grind .] lemma Tableau.sub_extend {t : Tableau} {a : Fml}
  : t ⊆ (t.extend a) := by grind

@[simp, grind =] lemma Tableau.extend_is_insert {t : Tableau} {a : Fml}
  : Tableau.abs (t.extend a) = insert a (Tableau.abs t) := by
  rw [<- Set.singleton_union, extend]
  split
  case isTrue =>
    rw [Set.singleton_union]
    exact Tableau.pushL_is_insert
  case isFalse =>
    rw [Set.singleton_union]
    exact Tableau.pushR_is_insert

@[simp, grind] noncomputable def Tableau.extend_list (t : Tableau) (xs : List Fml)
  : Tableau := t |> xs.foldr (fun (x : Fml) (t' : Tableau)  => ↑(t'.extend x))

@[simp, grind .] lemma Tableau.sub_extend_list {t : Tableau} {xs : List Fml}
  : t ⊆ (t.extend_list xs) := by
  induction xs with
  | nil =>
    rw [extend_list, List.foldr_nil]
    trivial
  | cons head tail ih =>
    rw [extend_list, List.foldr_cons, <- extend_list]
    trans
    · exact ih
    · exact Tableau.sub_extend

@[simp, grind =] lemma Tableau.extend_list_is_append {t : Tableau} {xs : List Fml}
  : Tableau.abs (t.extend_list xs) = Tableau.abs t ∪ ↑xs.toFinset := by
  induction xs with
  | nil =>
    simp [extend_list]
  | cons head tail ih =>
    simp [extend_list] at ih
    simp [extend_list, List.foldr_cons]
    grind

@[simp] lemma Tableau.extend_list_is_consistent {t : Tableau} (xs : List Fml)
  : t.Consistent -> (t.extend_list xs).Consistent := by
  intro tcon
  induction xs with
  | nil => exact tcon
  | cons head tail ih =>
    rw [extend_list, List.foldr_cons, <- extend_list]
    exact Tableau.extend_is_consistent ih

theorem Tableau.consistent_and_closed_is_saturated {t : Tableau}
  : t.Consistent -> t.Closed -> t.Saturated := by
  intro con closed
  rw [Tableau.Closed, Theory.Closed] at closed
  have mem_sub {a b} : (a ∈ t.1 ∨ a ∈ t.2) -> b.isSubfmlOf a -> b ∈ t.1 ∨ b ∈ t.2 := by
    intro amem b_sub_a
    rw [<- Set.mem_union, <- Tableau.abs] at amem
    apply closed at amem
    specialize amem b
    have bmem : b ∈ a.sub := b_sub_a Fml.mem_sub_self
    exact amem bmem
  constructor
  case conjL =>
    intro a b ab_mem_1
    have a_mem := mem_sub (Or.inl ab_mem_1) Fml.sub_conjL
    have b_mem := mem_sub (Or.inl ab_mem_1) Fml.sub_conjR
    suffices g : a ∉ t.2 ∧ b ∉ t.2 from by
      exact ⟨Or.resolve_right a_mem g.left, Or.resolve_right b_mem g.right⟩
    constructor
    case left =>
      by_contra a_mem_2
      have : ¬ t.Consistent := by
        rw [not_forall]
        exists [a]
        push Not
        refine ⟨by grind, ?_⟩
        exists ⟨[a ⋏ b], by grind⟩
        have h1 : Proof (⋏ [a ⋏ b] 🡒 a ⋏ b) := bigconj_e_singleton (a ⋏ b)
        have h2 : Proof (a ⋏ b 🡒 a) := conj_e1 a b
        have h3 : Proof (a 🡒 ⋎ [a]) := bigdisj_i_singleton a
        exact syll (syll h1 h2) h3
      contradiction
    case right =>
      by_contra b_mem_2
      have : ¬ t.Consistent := by
        rw [not_forall]
        exists [b]
        push Not
        refine ⟨by grind, ?_⟩
        exists ⟨[a ⋏ b], by grind⟩
        have h1 : Proof (⋏ [a ⋏ b] 🡒 a ⋏ b) := bigconj_e_singleton (a ⋏ b)
        have h2 : Proof (a ⋏ b 🡒 b) := conj_e2 a b
        have h3 : Proof (b 🡒 ⋎ [b]) := bigdisj_i_singleton b
        exact syll (syll h1 h2) h3
      contradiction
  case conjR =>
    intro a b ab_mem_2
    have a_mem := mem_sub (Or.inr ab_mem_2) Fml.sub_conjL
    have b_mem := mem_sub (Or.inr ab_mem_2) Fml.sub_conjR
    wlog a_nmem_2 : a ∉ t.2
    case inr => exact Or.inl (not_not.mp a_nmem_2)
    right
    have a_mem_1 := Or.resolve_right a_mem a_nmem_2
    by_contra b_nmem_2
    have b_mem_1 := Or.resolve_right b_mem b_nmem_2
    have : ¬ t.Consistent := by
      rw [not_forall]
      exists [a ⋏ b]
      push Not
      refine ⟨by grind, ?_⟩
      exists ⟨[a, b], by grind⟩
      have h1 : Proof (⋏ [a, b] 🡒 a ⋏ b) := bigconj_e_conj a b
      have h2 : Proof (a ⋏ b 🡒 ⋎ [a ⋏ b]) := bigdisj_i_singleton (a ⋏ b)
      exact syll h1 h2
    contradiction
  case disjL =>
    intro a b ab_mem_1
    have a_mem := mem_sub (Or.inl ab_mem_1) Fml.sub_disjL
    have b_mem := mem_sub (Or.inl ab_mem_1) Fml.sub_disjR
    wlog a_nmem_1 : a ∉ t.1
    case inr => exact Or.inl (not_not.mp a_nmem_1)
    right
    have a_mem_2 := Or.resolve_left a_mem a_nmem_1
    by_contra b_nmem_1
    have b_mem_2 := Or.resolve_left b_mem b_nmem_1
    have : ¬ t.Consistent := by
      rw [not_forall]
      exists [a, b]
      push Not
      refine ⟨by grind, ?_⟩
      exists ⟨[a ⋎ b], by grind⟩
      have h1 : Proof (⋏ [a ⋎ b] 🡒 (a ⋎ b)) := bigconj_e_singleton (a ⋎ b)
      have h2 : Proof (a ⋎ b 🡒 ⋎ [a, b]) := bigdisj_i_disj a b
      exact syll h1 h2
    contradiction
  case disjR =>
    intro a b ab_mem_2
    have a_mem := mem_sub (Or.inr ab_mem_2) Fml.sub_disjL
    have b_mem := mem_sub (Or.inr ab_mem_2) Fml.sub_disjR
    suffices g : a ∉ t.1 ∧ b ∉ t.1 from by
      exact ⟨Or.resolve_left a_mem g.left, Or.resolve_left b_mem g.right⟩
    constructor
    case left =>
      by_contra a_mem_1
      have : ¬ t.Consistent := by
        rw [not_forall]
        exists [a ⋎ b]
        push Not
        refine ⟨by grind, ?_⟩
        exists ⟨[a], by grind⟩
        have h1 : Proof (⋏ [a] 🡒 a) := bigconj_e_singleton a
        have h2 : Proof (a 🡒 a ⋎ b) := disj_i1 a b
        have h3 : Proof (a ⋎ b 🡒 ⋎ [a ⋎ b]) := bigdisj_i_singleton (a ⋎ b)
        exact syll (syll h1 h2) h3
      contradiction
    case right =>
      by_contra b_mem_1
      have : ¬ t.Consistent := by
        rw [not_forall]
        exists [a ⋎ b]
        push Not
        refine ⟨by grind, ?_⟩
        exists ⟨[b], by grind⟩
        have h1 : Proof (⋏ [b] 🡒 b) := bigconj_e_singleton b
        have h2 : Proof (b 🡒 a ⋎ b) := disj_i2 a b
        have h3 : Proof (a ⋎ b 🡒 ⋎ [a ⋎ b]) := bigdisj_i_singleton (a ⋎ b)
        exact syll (syll h1 h2) h3
      contradiction
  case impL =>
    intro a b ab_mem_1
    have a_mem := mem_sub (Or.inl ab_mem_1) Fml.sub_impL
    have b_mem := mem_sub (Or.inl ab_mem_1) Fml.sub_impR
    wlog a_nmem_2 : a ∉ t.2
    case inr => exact Or.inl (not_not.mp a_nmem_2)
    right
    have a_mem_1 := Or.resolve_right a_mem a_nmem_2
    by_contra b_nmem_1
    have b_mem_2 := Or.resolve_left b_mem b_nmem_1
    have : ¬ t.Consistent := by
      rw [not_forall]
      exists [b]
      push Not
      refine ⟨by grind, ?_⟩
      exists ⟨[a, a 🡒 b], by grind⟩
      have h1 : Proof (⋏ [a, a 🡒 b] 🡒 (a ⋏ (a 🡒 b))) := bigconj_e_conj a (a 🡒 b)
      have h2 : Proof ((a ⋏ (a 🡒 b)) 🡒 b) := axiomatized_mp a b
      have h3 : Proof (b 🡒 ⋎ [b]) := bigdisj_i_singleton b
      exact syll (syll h1 h2) h3
    contradiction
  case impR =>
    intro a b ab_mem_2
    have a_mem := mem_sub (Or.inr ab_mem_2) Fml.sub_impL
    have b_mem := mem_sub (Or.inr ab_mem_2) Fml.sub_impR
    by_contra hyp
    rw [not_and_or] at hyp
    cases hyp with
    | inl a_nmem_1 =>
      have a_mem_2 := Or.resolve_left a_mem a_nmem_1
      have : ¬ t.Consistent := by
        rw [not_forall]
        exists [a, a 🡒 b]
        push Not
        refine ⟨by grind, ?_⟩
        exists ⟨[], by grind⟩
        have h1 : Proof _ := lin a b
        have h2 : Proof _ := bigdisj_i_disj a (a 🡒 b)
        have h3 : Proof _ := mp h2 h1
        have h4 : Proof _ := k (⋎ [a, a 🡒 b]) ⊤
        exact mp h4 h3
      contradiction
    | inr b_nmem_2 =>
      have b_mem_1 := Or.resolve_right b_mem b_nmem_2
      have : ¬ t.Consistent := by
        rw [not_forall]
        exists [a 🡒 b]
        push Not
        refine ⟨by grind, ?_⟩
        exists ⟨[b], by grind⟩
        have h1 : Proof _ := bigconj_e_singleton b
        have h2 : Proof _ := bigdisj_i_singleton (a 🡒 b)
        exact syll (syll h1 (k b a)) h2
      contradiction

theorem completeness {a : Fml} : Valid a -> Provable a := by
  contrapose
  intro npa
  let t : Tableau := (∅, {a})
  have extendable : ∃ (t': Tableau), t ⊆ t' ∧ t'.Disjoint ∧ t'.Saturated := by
    have cont : t.Consistent := by
      intro xs sub
      have eq : t.1 = ∅ := by dsimp
      rw [eq]
      simp only [ProvableFrom, Proof.Contextual]
      have fa : ∀ x ∈ xs, x = a := sub
      let pxsa : Proof _ := bigdisj_e_same fa
      by_contra pxs
      have : Provable a := mp pxsa pxs.some.toHilbert |> Nonempty.intro
      contradiction
    let u := Tableau.extend_list t a.sub
    have subu : t ⊆ u := by
      simp only [u, Tableau.sub_extend_list]
    have conu : u.Consistent  := Tableau.extend_list_is_consistent a.sub cont
    have satu : u.Saturated := by
      suffices closedu : u.Closed from
        Tableau.consistent_and_closed_is_saturated conu closedu
      suffices eq : u.abs = ↑(a.sub.toFinset) from by
        rw [Tableau.Closed, eq]
        exact Fml.sub_toFinset_is_closed
      rw [Tableau.extend_list_is_append, Set.union_eq_right]
      intro x
      simp only [
        t, List.coe_toFinset, Set.mem_setOf,
        Tableau.abs, Set.empty_union, Set.mem_singleton_iff
      ]
      intro eq
      rw [eq]
      exact Fml.mem_sub_self
    exists u
    exact ⟨subu, Tableau.consistent_is_disjoint conu, satu⟩
  have ⟨V, vtrue, vfalse⟩ := Tableau.realizable_iff_extendable.mpr extendable
  rw [Valid, not_forall]
  exists V
  have mem : a ∈ t.2 := by
    simp only [t, Set.mem_singleton_iff]
  apply vfalse at mem
  exact mem
