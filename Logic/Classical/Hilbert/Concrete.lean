import Logic.Classical.Syntax.Concrete
import Logic.Classical.Hilbert.Basic

inductive Proof : Fml -> Type
  | k (a b: Fml) : Proof (a 🡒 b 🡒 a)
  | s (a b c: Fml) : Proof ((a 🡒 b 🡒 c) 🡒 (a 🡒 b) 🡒 (a 🡒 c))
  | conj_i (a b: Fml) : Proof (a 🡒 b 🡒 a ⋏ b)
  | conj_e1 (a b: Fml) : Proof (a ⋏ b 🡒 a)
  | conj_e2 (a b: Fml) : Proof (a ⋏ b 🡒 b)
  | disj_i1 (a b: Fml) : Proof (a 🡒 a ⋎ b)
  | disj_i2 (a b: Fml) : Proof (b 🡒 a ⋎ b)
  | disj_e (a b c: Fml) : Proof ((a 🡒 c) 🡒 (b 🡒 c) 🡒 (a ⋎ b 🡒 c))
  | dne (a: Fml) : Proof (∼ ∼ a 🡒 a)
  | mp {a b}: Proof (a 🡒 b) -> Proof a -> Proof b

instance : Hilbert Fml Proof where
  k := Proof.k
  s := Proof.s
  conj_i := Proof.conj_i
  conj_e1 := Proof.conj_e1
  conj_e2 := Proof.conj_e2
  disj_i1 := Proof.disj_i1
  disj_i2 := Proof.disj_i2
  disj_e := Proof.disj_e
  mp := Proof.mp

instance : Hilbert.Intuitionistic Fml Proof where
  exp := by
    intro a
    let h1 := Proof.k ⊥ (a 🡒 ⊥)
    let h2 := Proof.dne a
    exact Hilbert.syll h1 h2

instance : Hilbert.Classical Fml Proof where
  dne := Proof.dne

abbrev Proof.Contextual (Γ : Set Fml) (a : Fml) := Hilbert.Contextual Proof Γ a

abbrev Provable (a : Fml) := Nonempty (Proof a)

abbrev ProvableFrom (Γ : Set Fml) (a : Fml) := Nonempty (Proof.Contextual Γ a)
