import Mathlib.Tactic.DeriveEncodable
import Logic.Utils.List

abbrev Var := Nat

@[grind] inductive Fml : Type
  | bot : Fml
  | var (n: Var) : Fml
  | conj (a b: Fml) : Fml
  | disj (a b: Fml) : Fml
  | imp (a b: Fml) : Fml
deriving Inhabited, Repr, BEq, DecidableEq, Encodable

@[simp, grind] abbrev Fml.neg (a : Fml) : Fml := imp a bot
@[simp, grind] abbrev Fml.top : Fml := neg bot
@[simp, grind] abbrev Fml.equiv (a b : Fml) : Fml := conj (imp a b) (imp b a)
@[simp, grind] abbrev Fml.bigconj (xs : List Fml) : Fml := xs.foldr conj top
@[simp, grind] abbrev Fml.bigdisj (xs : List Fml) : Fml := xs.foldr disj bot

notation "⊤" => Fml.top
notation "⊥" => Fml.bot
prefix:58 "*" => Fml.var
prefix:57 "⋏" => Fml.bigconj
prefix:56 "⋎" => Fml.bigdisj
prefix:55 "∼" => Fml.neg
infixr:54 " ⋎ " => Fml.disj
infixr:53 " ⋏ " => Fml.conj
infixr:52 " 🡘 " => Fml.equiv
infixr:51 " 🡒 " => Fml.imp

@[simp, grind =] lemma Fml.bigconj_empty_is_top : bigconj [] = top := by simp
@[simp, grind =] lemma Fml.bigdisj_empty_is_bot : bigdisj [] = bot := by simp

open Fml

@[simp, grind] def Fml.sub : Fml -> List Fml
  | bot => [ bot ]
  | var n => [ var n ]
  | a 🡒 b => (a 🡒 b) :: (Fml.sub a ++ Fml.sub b)
  | a ⋏ b => (a ⋏ b) :: (Fml.sub a ++ Fml.sub b)
  | a ⋎ b => (a ⋎ b) :: (Fml.sub a ++ Fml.sub b)

@[simp] lemma Fml.mem_sub_self {a} : a ∈ Fml.sub a := by
  induction a with
  | bot => simp
  | var n => simp
  | imp b c => simp
  | conj a b => simp
  | disj a b => simp
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

@[simp, grind] abbrev Theory := Set Fml

@[simp] abbrev Theory.Closed (Γ : Theory) := ∀ a ∈ Γ, List.IsSubset (Fml.sub a) Γ

@[simp, grind .] lemma Theory.union_of_closed_is_closed {Γ Δ : Theory}
  : Γ.Closed -> Δ.Closed -> (Γ ∪ Δ).Closed := by grind

@[simp, grind .] lemma Theory.sUnion_of_closed_is_closed {Γ : Set Theory}
  : (∀ Γ' ∈ Γ, Theory.Closed Γ') -> Theory.Closed (Set.sUnion Γ) := by grind

@[simp, grind .] lemma Fml.sub_toFinset_is_closed {a}
  : Theory.Closed ((Fml.sub a).toFinset) := by
  simp only [Theory.Closed, List.IsSubset, List.coe_toFinset, Set.mem_setOf_eq]
  intro b bmem
  exact Fml.sub_lift bmem

@[simp, grind] def Fml.isSubfmlOf (a : Fml) (b : Fml) := a.sub ⊆ b.sub
