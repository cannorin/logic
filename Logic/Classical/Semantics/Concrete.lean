import Logic.Classical.Syntax.Concrete
import Logic.Classical.Semantics.Basic

@[simp] abbrev Valuation := Nat -> Prop

@[simp, grind] def Valuation.IsTrue (V : Valuation) : Fml -> Prop
  | .bot => False
  | .var p => V p
  | .imp a b => IsTrue V a -> IsTrue V b
  | .conj a b => IsTrue V a ∧ IsTrue V b
  | .disj a b => IsTrue V a ∨ IsTrue V b

def Valuation.Tarskean (V : Valuation) : Model.Tarskean (Valuation.IsTrue V) := by
  constructor
  case bot => simp
  case conj => simp
  case disj => simp
  case imp => simp

@[simp] def Valid (a : Fml) := ∀ (V : Valuation), V.IsTrue a

@[simp] def ValidUnder (Γ : Set Fml) (a : Fml) :=
  ∀ (V : Valuation), (∀ b ∈ Γ, V.IsTrue b) -> V.IsTrue a
