import Std
import Logic.Utils.List
import Logic.Classical.Syntax.Concrete
import Logic.Classical.Semantics.Concrete

abbrev Tableau := Set Fml × Set Fml

abbrev Tableau.HasSubset (t : Tableau) (u : Tableau) := t.fst ⊆ u.fst ∧ t.snd ⊆ u.snd
instance : HasSubset Tableau := ⟨Tableau.HasSubset⟩
instance : IsTrans Tableau (· ⊆ ·) where
  trans := by
    intro a b c
    simp only [· ⊆ ·, Tableau.HasSubset]
    intro ab bc
    constructor
    case left =>
      exact Set.instTransSubset.trans ab.left bc.left
    case right =>
      exact Set.instTransSubset.trans ab.right bc.right

@[grind =] lemma Tableau.sub_iff {t : Tableau} {u : Tableau}
  : t ⊆ u <-> t.1 ⊆ u.1 ∧ t.2 ⊆ u.2 := by
  simp only [· ⊆ ·, Tableau.HasSubset]

abbrev Tableau.union (t : Tableau) (u : Tableau) := (t.fst ∪ u.fst, t.snd ∪ u.snd)
instance : Union Tableau := ⟨Tableau.union⟩

@[grind ->] lemma Tableau.union_eq_self_of_subset_left {t : Tableau} {u : Tableau}
  : t ⊆ u -> t ∪ u = u := by
  intro t_sub_u
  simp only [· ⊆ ·, Tableau.HasSubset] at t_sub_u
  simp only [Set.le_iff_subset] at t_sub_u
  have eq1 : t.1.union u.1 = u.1 := Set.union_eq_self_of_subset_left t_sub_u.left
  have eq2 : t.2.union u.2 = u.2 := Set.union_eq_self_of_subset_left t_sub_u.right
  simp only [· ∪ ·, Tableau.union]
  rw [eq1, eq2]

abbrev Tableau.iUnion {ι} (s : ι -> Tableau) : Tableau
  := (Set.iUnion (Prod.fst ∘ s), Set.iUnion (Prod.snd ∘ s))

@[simp] lemma Tableau.sub_iUnion {ι} {i : ι} {s : ι -> Tableau}
  : s i ⊆ iUnion s := by
  simp only [· ⊆ ·, Tableau.HasSubset]
  simp only [Set.le_iff_subset]
  constructor
  case left =>
    exact Set.subset_iUnion (Prod.fst ∘ s) i
  case right =>
    exact Set.subset_iUnion (Prod.snd ∘ s) i

abbrev Tableau.Disjoint (t : Tableau) :=
  (t.fst ∩ t.snd) = ∅ ∧ bot ∉ t.fst

@[simp, grind <-] lemma Tableau.disjoint_imp_not_mem_both {t : Tableau} (a : Fml)
  : t.Disjoint -> ¬(a ∈ t.1 ∧ a ∈ t.2) := by
  intro d
  have : t.1 ∩ t.2 = ∅ := d.left
  by_contra h
  have : t.1 ∩ t.2 ≠ ∅ := by
    rw [<- Set.nonempty_iff_ne_empty, Set.nonempty_def]
    exists a
  contradiction

abbrev Tableau.RealizedBy (t : Tableau) (V : Valuation) :=
  (∀ a ∈ t.fst, V.IsTrue a) ∧ (∀ b ∈ t.snd, ¬ V.IsTrue b)

abbrev Tableau.Realizable (t : Tableau) := ∃ V, t.RealizedBy V

structure Tableau.Saturated (t : Tableau) : Prop where
  conjL {a b} : (a ⋏ b) ∈ t.1 -> a ∈ t.1 ∧ b ∈ t.1
  conjR {a b} : (a ⋏ b) ∈ t.2 -> a ∈ t.2 ∨ b ∈ t.2
  disjL {a b} : (a ⋎ b) ∈ t.1 -> a ∈ t.1 ∨ b ∈ t.1
  disjR {a b} : (a ⋎ b) ∈ t.2 -> a ∈ t.2 ∧ b ∈ t.2
  impL  {a b} : (a 🡒 b) ∈ t.1 -> a ∈ t.2 ∨ b ∈ t.1
  impR  {a b} : (a 🡒 b) ∈ t.2 -> a ∈ t.1 ∧ b ∈ t.2

abbrev Tableau.abs (t : Tableau) := t.1 ∪ t.2

@[simp, grind ->] lemma Tableau.abs_subset {t : Tableau} {u : Tableau}
  : t ⊆ u -> t.abs ⊆ u.abs := by
  intro sub
  simp only [· ⊆ ·, Tableau.HasSubset] at sub
  rw [Set.le_iff_subset] at sub
  simp only [abs]
  exact Set.union_subset_union sub.left sub.right

@[simp] lemma Tableau.realizes_sub {t t' : Tableau} {V : Valuation} :
  t ⊆ t' -> t'.RealizedBy V -> t.RealizedBy V := by
  intro sub rt'
  constructor
  case left =>
    intro a amem
    have amem' : a ∈ t'.fst := Set.mem_of_subset_of_mem sub.left amem
    let rtl' := rt'.left
    specialize rtl' a
    exact rtl' amem'
  case right =>
    intro b bmem
    have bmem' : b ∈ t'.snd := Set.mem_of_subset_of_mem sub.right bmem
    let rtr' := rt'.right
    specialize rtr' b
    exact rtr' bmem'

theorem Tableau.realizable_iff_extendable {t : Tableau} :
  t.Realizable <-> ∃ (t': Tableau), t ⊆ t' ∧ t'.Disjoint ∧ t'.Saturated := by
  constructor
  case mp =>
    intro ⟨V, re⟩
    let Γ := { a : Fml | V.IsTrue a }
    let Δ := { a : Fml | ¬ V.IsTrue a }
    let t': Tableau := (Γ, Δ)
    exists t'
    have e1 : t'.1 = Γ := by rw [Prod.fst_eq_iff]
    have e2 : t'.2 = Δ := by rw [Prod.snd_eq_iff]
    have sub : t ⊆ t' := by
      constructor
      case left =>
        intro x xmem
        let rel := re.left
        specialize rel x
        rw [Set.mem_setOf]
        exact rel xmem
      case right =>
        intro x xmem
        let rer := re.right
        specialize rer x
        rw [Set.mem_setOf]
        exact rer xmem
    have Disjoint : t'.Disjoint := by
      constructor
      case left =>
        by_contra h
        rw [Set.eq_empty_iff_forall_notMem, not_forall] at h
        obtain ⟨x, cond⟩ := h
        rw [Set.not_notMem, e1, e2, Set.mem_inter_iff, Set.mem_setOf, Set.mem_setOf] at cond
        have : V.IsTrue x := cond.left
        have : ¬ V.IsTrue x := cond.right
        contradiction
      case right =>
        rw [e1, Set.mem_setOf_eq, Valuation.IsTrue.eq_def]
        dsimp
        trivial
    have saturated : t'.Saturated := by
      constructor
      case conjL =>
        intro x y
        rw [e1, Set.mem_setOf_eq, Set.mem_setOf_eq, Set.mem_setOf_eq, Valuation.IsTrue.eq_def]
        exact id
      case conjR =>
        intro x y
        rw [
          e2, Set.mem_setOf_eq, Set.mem_setOf_eq, Set.mem_setOf_eq,
          Valuation.IsTrue.eq_def, not_and_or
        ]
        exact id
      case disjL =>
        intro x y
        rw [e1, Set.mem_setOf_eq, Set.mem_setOf_eq, Set.mem_setOf_eq, Valuation.IsTrue.eq_def]
        exact id
      case disjR =>
        intro x y
        rw [
          e2, Set.mem_setOf_eq, Set.mem_setOf_eq, Set.mem_setOf_eq,
          Valuation.IsTrue.eq_def, not_or
        ]
        exact id
      case impL =>
        intro x y
        rw [
          e1, e2, Set.mem_setOf_eq, Set.mem_setOf_eq, Set.mem_setOf_eq,
          Valuation.IsTrue.eq_def, <- imp_iff_not_or
        ]
        exact id
      case impR =>
        intro x y
        rw [e1, e2, Set.mem_setOf_eq, Set.mem_setOf_eq, Set.mem_setOf_eq, Valuation.IsTrue.eq_def]
        push Not
        exact id
    exact ⟨sub, Disjoint, saturated⟩
  case mpr =>
    intro ⟨t', ⟨sub, Disjoint, saturated⟩⟩
    let V: Valuation := fun p => *p ∈ t'.fst
    exists V
    suffices hyp : t'.RealizedBy V from realizes_sub sub hyp
    suffices hyp : (∀ a, (a ∈ t'.fst -> V.IsTrue a) ∧ (a ∈ t'.snd -> ¬ V.IsTrue a)) from by
      dsimp only [Tableau.RealizedBy]
      rw [<- forall_and]
      exact hyp
    intro a
    induction a with
    | bot =>
      constructor
      case left =>
        intro _
        have : bot ∉ t'.fst := Disjoint.right
        contradiction
      case right =>
        intro _
        rw [Valuation.IsTrue]
        trivial
    | var q =>
      constructor
      case left =>
        intro _
        trivial
      case right =>
        intro amem2
        have : *q ∉ t'.fst := by
          have : *q ∉ t'.fst ∩ t'.snd := by
            rw [Disjoint.left, Set.mem_empty_iff_false]
            trivial
          by_contra amem1
          have : *q ∈ t'.fst ∩ t'.snd := by
            rw [Set.mem_inter_iff]
            exact ⟨amem1, amem2⟩
          contradiction
        trivial
    | conj b c hb hc =>
      constructor
      case left =>
        intro amem
        apply saturated.conjL at amem
        exact ⟨hb.left amem.left, hc.left amem.right⟩
      case right =>
        intro amem
        apply saturated.conjR at amem
        rw [Valuation.IsTrue, not_and_or]
        cases amem with
        | inl bmem => exact Or.inl (hb.right bmem)
        | inr cmem => exact Or.inr (hc.right cmem)
    | disj b c hb hc =>
      constructor
      case left =>
        intro amem
        apply saturated.disjL at amem
        cases amem with
        | inl bmem =>
          left
          exact hb.left bmem
        | inr cmem =>
          right
          exact hc.left cmem
      case right =>
        intro amem
        apply saturated.disjR at amem
        rw [Valuation.IsTrue, not_or]
        exact ⟨hb.right amem.left, hc.right amem.right⟩
    | imp b c hb hc =>
      constructor
      case left =>
        intro amem
        apply saturated.impL at amem
        cases amem with
        | inl bmem2 =>
          rw [Valuation.IsTrue]
          intro tb
          have ntb := hb.right bmem2
          contradiction
        | inr cmem1 =>
          rw [Valuation.IsTrue]
          intro _
          exact hc.left cmem1
      case right =>
        intro amem
        apply saturated.impR at amem
        rw [Valuation.IsTrue]
        by_contra b_imp_c
        have : ¬ V.IsTrue c := hc.right amem.right
        have : V.IsTrue c := hb.left amem.left |> b_imp_c
        contradiction

@[simp, grind] abbrev Tableau.pushL (t : Tableau) (a : Fml) : Tableau := (t.1 ∪ {a}, t.2)
@[simp, grind] abbrev Tableau.pushR (t : Tableau) (a : Fml) : Tableau := (t.1, t.2 ∪ {a})

@[simp, grind .] lemma Tableau.pushL_is_sup {t : Tableau} {a : Fml} : t ⊆ t.pushL a := by
  simp only [pushL, Set.union_singleton]
  obtain ⟨fst, snd⟩ := t
  simp only [· ⊆ ·, HasSubset]
  refine ⟨?_, (by trivial)⟩
  apply Set.subset_insert

@[simp, grind .] lemma Tableau.pushR_is_sup {t : Tableau} {a : Fml} : t ⊆ t.pushR a := by
  simp only [pushR, Set.union_singleton]
  obtain ⟨fst, snd⟩ := t
  simp only [· ⊆ ·, HasSubset]
  refine ⟨(by trivial), ?_⟩
  apply Set.subset_insert

@[simp, grind =] lemma Tableau.pushL_is_insert {t : Tableau} {a : Fml}
  : (t.pushL a).abs = insert a t.abs := by
  simp only [Set.union_singleton, abs, Set.insert_union]

@[simp, grind =] lemma Tableau.pushR_is_insert {t : Tableau} {a : Fml}
  : (t.pushR a).abs = insert a t.abs:= by
  simp only [Set.union_singleton, abs, Set.union_insert]

@[simp] abbrev Tableau.Closed {t : Tableau} := Theory.Closed t.abs
