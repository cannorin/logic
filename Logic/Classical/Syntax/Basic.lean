import Mathlib.Tactic.DeriveEncodable
import Logic.Utils.List

class Language (L : Type u) where
  var : Nat -> L
  bot : L
  conj : L -> L -> L
  disj : L -> L -> L
  imp : L -> L -> L
  sub : L -> List L

abbrev var {L} [Language L] (n : Nat) : L :=
  Language.var n
abbrev bot {L} [Language L] : L :=
  Language.bot
abbrev conj {L} [Language L] (a b : L) : L :=
  Language.conj a b
abbrev disj {L} [Language L] (a b : L) : L :=
  Language.disj a b
abbrev imp {L} [Language L] (a b : L) : L :=
  Language.imp a b

abbrev neg {L} [Language L] (a : L) : L := imp a bot
abbrev top {L} [Language L] : L := neg bot
abbrev equiv {L} [Language L] (a b : L) : L := conj (imp a b) (imp b a)

abbrev bigconj {L} [Language L] (xs : List L) : L := xs.foldr conj top
abbrev bigdisj {L} [Language L] (xs : List L) : L := xs.foldr disj bot

@[simp, grind =] theorem bigconj_empty_is_top {L} [Language L]
  : bigconj [] = top (L := L) := by simp

@[simp, grind =] theorem bigdisj_empty_is_bot {L} [Language L]
  : bigdisj [] = bot (L := L) := by simp

notation "⊤" => top
notation "⊥" => bot
prefix:58 "*" => var
prefix:57 "⋏" => bigconj
prefix:56 "⋎" => bigdisj
prefix:55 "∼" => neg
infixr:54 " ⋎ " => disj
infixr:53 " ⋏ " => conj
infixr:52 " 🡘 " => equiv
infixr:51 " 🡒 " => imp

@[simp, grind] abbrev Theory (L) [Language L] := Set L

@[simp] abbrev Theory.Closed {L} [Language L] (Γ : Theory L) :=
  ∀ a ∈ Γ, List.IsSubset (Language.sub a) Γ

@[simp, grind .] lemma Theory.union_of_closed_is_closed {L} [Language L] {Γ Δ : Theory L}
  : Γ.Closed -> Δ.Closed -> (Γ ∪ Δ).Closed := by grind

@[simp, grind .] lemma Theory.sUnion_of_closed_is_closed {L} [Language L] {Γ : Set (Theory L)}
  : (∀ Γ' ∈ Γ, Theory.Closed Γ') -> Theory.Closed (Set.sUnion Γ) := by grind
