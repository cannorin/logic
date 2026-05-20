import Mathlib.Tactic.DeriveEncodable
import Logic.Utils.List
import Logic.Classical.Syntax.Basic

@[grind] inductive Fml : Type
  | bot : Fml
  | var (n: Nat) : Fml
  | conj (a b: Fml) : Fml
  | disj (a b: Fml) : Fml
  | imp (a b: Fml) : Fml
deriving Inhabited, Repr, BEq, DecidableEq, Encodable

@[simp, grind] def Fml.sub : Fml -> List Fml
  | bot => [ bot ]
  | var n => [ var n ]
  | imp a b => (imp a b) :: (Fml.sub a ++ Fml.sub b)
  | conj a b => (conj a b) :: (Fml.sub a ++ Fml.sub b)
  | disj a b => (disj a b) :: (Fml.sub a ++ Fml.sub b)

instance : Language Fml where
  var := Fml.var
  bot := Fml.bot
  conj := Fml.conj
  disj := Fml.disj
  imp := Fml.imp
  sub := Fml.sub

@[simp] lemma Fml.mem_sub_self {a} : a ∈ Fml.sub a := by
  induction a with
  | bot => simp
  | var n => simp
  | imp b c =>
    simp only [sub, List.mem_cons, List.mem_append]
    left
    trivial
  | conj a b =>
    simp only [sub, List.mem_cons, List.mem_append]
    left
    trivial
  | disj a b =>
    simp only [sub, List.mem_cons, List.mem_append]
    left
    trivial
@[simp, grind! .] lemma Fml.sub_impL {a b} : Fml.sub a ⊆ Fml.sub (a 🡒 b) := by simp
@[simp, grind! .] lemma Fml.sub_impR {a b} : Fml.sub b ⊆ Fml.sub (a 🡒 b) := by simp
@[simp, grind! .] lemma Fml.sub_conjL {a b} : Fml.sub a ⊆ Fml.sub (a ⋏ b) := by simp
@[simp, grind! .] lemma Fml.sub_conjR {a b} : Fml.sub b ⊆ Fml.sub (a ⋏ b) := by simp
@[simp, grind! .] lemma Fml.sub_disjL {a b} : Fml.sub a ⊆ Fml.sub (a ⋎ b) := by simp
@[simp, grind! .] lemma Fml.sub_disjR {a b} : Fml.sub b ⊆ Fml.sub (a ⋎ b) := by simp

@[simp, grind ->] lemma Fml.sub_imp_sub {a b c}
  : Fml.sub (a 🡒 b) ⊆ Fml.sub c -> Fml.sub a ⊆ Fml.sub c ∧ Fml.sub b ⊆ Fml.sub c := by simp

@[simp, grind ->] lemma Fml.sub_conj_sub {a b c}
  : Fml.sub (a ⋏ b) ⊆ Fml.sub c -> Fml.sub a ⊆ Fml.sub c ∧ Fml.sub b ⊆ Fml.sub c := by simp

@[simp, grind ->] lemma Fml.sub_disj_sub {a b c}
  : Fml.sub (a ⋎ b) ⊆ Fml.sub c -> Fml.sub a ⊆ Fml.sub c ∧ Fml.sub b ⊆ Fml.sub c := by simp

@[simp, grind ->] lemma Fml.sub_lift {a b} : a ∈ Fml.sub b -> Fml.sub a ⊆ Fml.sub b := by
  induction b with
  | bot =>
    intro mem
    rw [Fml.sub, List.mem_cons, List.mem_nil_iff, or_false] at mem
    rw [mem, Fml.sub]
    apply List.Subset.refl
  | var n =>
    intro mem
    rw [Fml.sub, List.mem_cons, List.mem_nil_iff, or_false] at mem
    rw [mem, Fml.sub]
    apply List.Subset.refl
  | conj c d ihc ihd =>
    intro mem
    rw [Fml.sub, List.mem_cons, List.mem_append] at mem
    cases mem with
    | inl eq =>
      rw [eq]
      apply List.Subset.refl
    | inr cond =>
      cases cond with
      | inl memc =>
        let ac := ihc memc
        exact List.Subset.trans ac sub_conjL
      | inr memd =>
        let ad := ihd memd
        exact List.Subset.trans ad sub_conjR
  | disj c d ihc ihd =>
    intro mem
    rw [Fml.sub, List.mem_cons, List.mem_append] at mem
    cases mem with
    | inl eq =>
      rw [eq]
      apply List.Subset.refl
    | inr cond =>
      cases cond with
      | inl memc =>
        let ac := ihc memc
        exact List.Subset.trans ac sub_disjL
      | inr memd =>
        let ad := ihd memd
        exact List.Subset.trans ad sub_disjR
  | imp c d ihc ihd =>
    intro mem
    rw [Fml.sub, List.mem_cons, List.mem_append] at mem
    cases mem with
    | inl eq =>
      rw [eq]
      apply List.Subset.refl
    | inr cond =>
      cases cond with
      | inl memc =>
        let ac := ihc memc
        exact List.Subset.trans ac sub_impL
      | inr memd =>
        let ad := ihd memd
        exact List.Subset.trans ad sub_impR

@[simp, grind .] lemma Fml.sub_toFinset_is_closed {a}
  : Theory.Closed (L := Fml) ((Fml.sub a).toFinset) := by
  simp only [Theory.Closed, List.IsSubset, List.coe_toFinset, Set.mem_setOf_eq]
  intro b bmem
  exact Fml.sub_lift bmem

@[simp, grind] def Fml.isSubfmlOf (a : Fml) (b : Fml) := a.sub ⊆ b.sub
