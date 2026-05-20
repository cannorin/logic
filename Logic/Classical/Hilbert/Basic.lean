import Logic.Classical.Syntax.Basic

class Hilbert (L : Type) [Language L] (S : L -> Type) where
  k (a b) : S (a 🡒 b 🡒 a)
  s (a b c) : S ((a 🡒 b 🡒 c) 🡒 (a 🡒 b) 🡒 (a 🡒 c))
  conj_i (a b) : S (a 🡒 b 🡒 a ⋏ b)
  conj_e1 (a b) : S (a ⋏ b 🡒 a)
  conj_e2 (a b) : S (a ⋏ b 🡒 b)
  disj_i1 (a b) : S (a 🡒 a ⋎ b)
  disj_i2 (a b) : S (b 🡒 a ⋎ b)
  disj_e (a b c) : S ((a 🡒 c) 🡒 (b 🡒 c) 🡒 (a ⋎ b 🡒 c))
  mp {a b} : S (a 🡒 b) -> S a -> S b

class Hilbert.Intuitionistic (L : Type) [Language L] (S : L -> Type) extends Hilbert L S where
  exp (a) : S (⊥ 🡒 a)

class Hilbert.Classical (L : Type) [Language L] (S : L -> Type)
  extends Hilbert.Intuitionistic L S where
  dne (a) : S (∼ ∼ a 🡒 a)

@[grind] def Hilbert.i {L S} [Language L] [Hilbert L S]
  (a : L) : S (a 🡒 a) := by
  let h1 : S _ := k a (a 🡒 a)
  let h2 : S _ := s a (a 🡒 a) a
  let h3 : S _ := mp h2 h1
  let h4 : S _ := k a a
  exact mp h3 h4

@[grind] def Hilbert.verum {L S} [Language L] [Hilbert L S]
  : S (top (L := L)) := i (bot (L := L))

@[grind] def Hilbert.syll {L S} [Language L] [Hilbert L S]
  {a b c : L} : S (a 🡒 b) -> S (b 🡒 c) -> S (a 🡒 c) := by
  intro hab hbc
  let hbc := mp (k (b 🡒 c) a) hbc
  let habac := mp (s a b c) hbc
  exact mp habac hab

@[grind] def Hilbert.top_imp {L S} [Language L] [Hilbert L S]
  {a : L} : S (⊤ 🡒 a) -> S a := by
  intro hta
  exact mp hta verum

@[grind] def Hilbert.top_imp_rev {L S} [Language L] [Hilbert L S]
  {a : L} : S a -> S (⊤ 🡒 a) := by
  intro ha
  exact mp (k a ⊤) ha

@[grind] def Hilbert.imp_exchange {L S} [Language L] [Hilbert L S]
  {a b c : L} : S (a 🡒 b 🡒 c) -> S (b 🡒 a 🡒 c) := by
  intro habc
  let h1 := mp (s a b c) habc
  exact syll (k b a) h1

@[grind] def Hilbert.imp_contract {L S} [Language L] [Hilbert L S]
  {a b : L} : S (a 🡒 a 🡒 b) -> S (a 🡒 b) := by
  intro haab
  let h1 := mp (s a a b) haab
  exact mp h1 (i a)

@[grind] def Hilbert.curry {L S} [Language L] [Hilbert L S]
  {a b c : L} : S (a ⋏ b 🡒 c) -> S (a 🡒 b 🡒 c) := by
  intro h
  let h1 := mp (k (a ⋏ b 🡒 c) b) h
  let h2 := mp (s b (a ⋏ b) c) h1
  let h3 : S _ := s a (b 🡒 a ⋏ b) (b 🡒 c)
  let h4 := mp (k ((b 🡒 a ⋏ b) 🡒 (b 🡒 c)) a) h2
  exact mp (mp h3 h4) (conj_i a b)

@[grind] def Hilbert.uncurry {L S} [Language L] [Hilbert L S]
  {a b c : L} : S (a 🡒 b 🡒 c) -> S (a ⋏ b 🡒 c) := by
  intro h
  let h1 : S _ := s (a ⋏ b) a (b 🡒 c)
  let h2 := mp (k (a 🡒 (b 🡒 c)) (a ⋏ b)) h
  let h3 := mp (mp h1 h2) (conj_e1 a b)
  let h4 : S _ := s (a ⋏ b) b c
  exact mp (mp h4 h3) (conj_e2 a b)

@[grind] def Hilbert.conj_i_alt {L S} [Language L] [Hilbert L S]
  {a b c : L} : S (a 🡒 b) -> S (a 🡒 c) -> S (a 🡒 b ⋏ c) := by
  intro hab hac
  let h1 : S _ := conj_i b c
  let h2 := syll hab h1
  let h3 := syll hac (imp_exchange h2)
  exact imp_contract h3

@[grind] def Hilbert.axiomatized_mp {L S} [Language L] [Hilbert L S]
  (a b : L) : S (a ⋏ (a 🡒 b) 🡒 b) := by
  exact uncurry (imp_exchange (i (a 🡒 b)))

@[grind] def Hilbert.bigconj_e {L S} [DecidableEq L] [Language L] [Hilbert L S]
  {xs : List L} {x : L} : x ∈ xs -> S (⋏ xs 🡒 x) := by
  intro xmem
  induction xs with
  | nil => contradiction
  | cons head tail ih =>
    rw [List.mem_cons] at xmem
    if eq : x = head then
      rw [eq]
      exact conj_e1 head (⋏ tail)
    else
      apply Or.resolve_left (na := eq) at xmem
      let htail : S _ := conj_e2 head (⋏ tail)
      exact syll htail (ih xmem)

@[grind] def Hilbert.bigconj_e_singleton {L S} [Language L] [Hilbert L S]
  (x : L) : S (⋏ [x] 🡒 x) := by
  rw [bigconj, List.foldr_cons, List.foldr_nil]
  exact conj_e1 x ⊤

@[grind] def Hilbert.bigconj_e_conj {L S} [Language L] [Hilbert L S]
  (x y : L) : S (⋏ [x, y] 🡒 x ⋏ y) := by
  rw [bigconj, List.foldr_cons, List.foldr_cons, List.foldr_nil]
  apply uncurry
  apply imp_exchange
  apply uncurry
  apply imp_exchange
  apply top_imp_rev
  apply imp_exchange
  exact conj_i x y

@[grind] def Hilbert.bigconj_e_many {L S} [DecidableEq L] [Language L] [Hilbert L S]
  {xs ys : List L} : ys ⊆ xs -> S (⋏ xs 🡒 ⋏ ys) := by
  intro sub
  induction ys with
  | nil =>
    exact mp (k top (⋏ xs)) verum
  | cons head tail ih =>
    rw [List.cons_subset] at sub
    have subt : tail ⊆ xs := by
      intro y mem
      exact sub.right mem
    let ih := ih subt
    let hhead : S _ := bigconj_e sub.left
    exact conj_i_alt hhead ih

@[grind] def Hilbert.bigdisj_i {L S} [DecidableEq L] [Language L] [Hilbert L S]
  {xs : List L} {x : L} : x ∈ xs -> S (x 🡒 ⋎ xs) := by
  intro xmem
  induction xs with
  | nil => contradiction
  | cons head tail ih =>
    rw [List.mem_cons] at xmem
    if eq : x = head then
      rw [eq]
      exact disj_i1 head (⋎ tail)
    else
      apply Or.resolve_left (na := eq) at xmem
      let htail : S _ := disj_i2 head (⋎ tail)
      exact syll (ih xmem) htail

@[grind] def Hilbert.bigdisj_i_singleton {L S} [Language L] [Hilbert L S]
  (x : L) : S (x 🡒 ⋎ [x]) := by
  rw [bigdisj, List.foldr_cons, List.foldr_nil]
  exact disj_i1 x bot

@[grind] def Hilbert.bigdisj_i_disj {L S} [Language L] [Hilbert L S]
  (x y : L) : S (x ⋎ y 🡒 ⋎ [x, y]) := by
  rw [bigdisj, List.foldr_cons, List.foldr_cons, List.foldr_nil]
  have h3 : S _ := disj_e x y (x ⋎ y ⋎ ⊥)
  have h4 : S _ := mp h3 (disj_i1 x (y ⋎ ⊥))
  have h5 : S (y 🡒 x ⋎ (y ⋎ ⊥)) := by
    have h6 : S _ := disj_i1 y ⊥
    have h7 : S _ := disj_i2 x (y ⋎ ⊥)
    exact syll h6 h7
  exact mp h4 h5

@[grind] def Hilbert.bigdisj_i_many {L S} [DecidableEq L] [Language L] [Hilbert.Intuitionistic L S]
  {xs ys : List L} : ys ⊆ xs -> S (⋎ ys 🡒 ⋎ xs) := by
  intro sub
  induction ys with
  | nil =>
    rw [bigdisj, List.foldr_nil]
    exact Intuitionistic.exp (⋎ xs)
  | cons head tail ih =>
    rw [List.cons_subset] at sub
    have subt : tail ⊆ xs := by
      intro y mem
      exact sub.right mem
    let ih := ih subt
    let hhead : S _ := bigdisj_i sub.left
    let h : S _ := disj_e head (⋎ tail) (⋎ xs)
    exact mp (mp h hhead) ih

@[grind] def Hilbert.bigdisj_e_same {L S} [Language L] [Hilbert.Intuitionistic L S]
  {a : L} {xs : List L} : (∀ x ∈ xs, x = a) -> S (⋎ xs 🡒 a) := by
  intro forall_eq_a
  induction xs with
  | nil =>
    rw [bigdisj_empty_is_bot]
    exact Intuitionistic.exp a
  | cons head tail ih =>
    have eq : head = a := by
      specialize forall_eq_a head
      apply forall_eq_a
      rw [List.mem_cons]
      exact Or.inl (refl head)
    rw [eq]
    have forall_eq_a : ∀ y ∈ tail, y = a := by grind
    let ih := ih forall_eq_a
    exact mp (mp (disj_e a (⋎ tail) a) (i a)) ih

@[grind] def Hilbert.bigconj_to_bigdisj {L S} [DecidableEq L] [Language L] [Hilbert L S]
  {a : L} {xs ys : List L} : a ∈ xs -> a ∈ ys -> S (⋏ xs 🡒 ⋎ ys) := by
  intro memxs memys
  let lhs : S _ := bigconj_e memxs
  let rhs : S _ := bigdisj_i memys
  exact syll lhs rhs

@[simp] abbrev Hilbert.Contextual {L} (S) [Language L] [Hilbert L S]
  (Γ : Set L) (a : L) := Σ xs : List.SubsetOf Γ, S (⋏ xs 🡒 a)

@[simp] abbrev Hilbert.Contextual.toHilbert {L S} [Language L] [Hilbert L S]
  {a : L} : Contextual S ∅ a -> S a := by
  intro ⟨xs, ha⟩
  have eq : xs.val = [] := List.IsSubset_empty_is_nil xs.property
  rw [eq, bigconj_empty_is_top] at ha
  exact mp ha Hilbert.verum

@[grind] def Hilbert.Contextual.deduction_left {L S} [Language L] [Hilbert L S]
  {Γ : Set L} {a b : L} : Contextual S Γ (a 🡒 b) -> Contextual S (Γ ∪ {a}) b := by
  intro ⟨⟨xs, sub⟩, h⟩
  let xs' := a :: xs
  let sub' : xs'.IsSubset (Γ ∪ {a}) := by grind
  let h' : S (⋏ xs' 🡒 b) :=
    h |> Hilbert.imp_exchange |> Hilbert.uncurry
  exists ⟨xs', sub'⟩

@[grind] def Hilbert.Contextual.deduction_right {L S} [DecidableEq L] [Language L] [Hilbert L S]
  {Γ : Set L} {a b : L} : Contextual S (Γ ∪ {a}) b -> Contextual S Γ (a 🡒 b) := by
  intro ⟨⟨xs, sub⟩, h⟩
  let xs' := List.remove xs a
  let sub' : xs'.IsSubset Γ := by grind
  exists ⟨xs', sub'⟩
  have reord : xs ⊆ a :: xs' := by grind
  let h1 : S _ := Hilbert.bigconj_e_many reord
  let h2 := Hilbert.syll h1 h
  exact h2 |> Hilbert.curry |> Hilbert.imp_exchange

@[grind] def Hilbert.Contextual.initial {L S} [Language L] [Hilbert L S]
  {Γ : Set L} {a : L} : a ∈ Γ -> Contextual S Γ a := by
  intro amem
  exists ⟨[a], (by grind)⟩
  exact Hilbert.conj_e1 a ⊤

@[grind] def Hilbert.Contextual.weakening {L S} [Language L] [Hilbert L S]
  {Γ Δ : Set L} {a : L} : Γ ⊆ Δ -> Contextual S Γ a -> Contextual S Δ a := by
  intro Γ_sub_Δ ⟨⟨xs, xs_sub_Γ⟩, h⟩
  exists ⟨xs, (by grind)⟩

@[grind] def Hilbert.Contextual.mp {L S} [DecidableEq L] [Language L] [Hilbert L S]
  {Γ : Set L} {a b : L} : Contextual S Γ (a 🡒 b) -> Contextual S Γ a -> Contextual S Γ b := by
  intro ⟨⟨xs, xs_sub_Γ⟩, hab⟩ ⟨⟨ys, ys_sub_Γ⟩, ha⟩
  let zs := xs ++ ys
  exists ⟨zs, (by grind)⟩
  have h1 : S (⋏ zs 🡒 ⋏ xs) := Hilbert.bigconj_e_many (by grind)
  have h2 : S (⋏ zs 🡒 ⋏ ys) := Hilbert.bigconj_e_many (by grind)
  have hab' := Hilbert.syll h1 hab
  have ha' := Hilbert.syll h2 ha
  have habb' := Hilbert.conj_i_alt ha' hab'
  exact Hilbert.syll habb' (Hilbert.axiomatized_mp a b)

@[grind] def Hilbert.Contextual.syll {L S} [DecidableEq L] [Language L] [Hilbert L S]
  {Γ : Set L} {a b c : L}
  : Contextual S Γ (a 🡒 b) -> Contextual S Γ (b 🡒 c) -> Contextual S Γ (a 🡒 c) := by
  intro cab cbc
  apply deduction_right
  have cab' : Contextual S (Γ ∪ {a}) b := deduction_left cab
  have sub : Γ ⊆ Γ ∪ {a} := by simp
  let cabc := weakening sub cbc
  exact mp cabc cab'

@[simp] abbrev Hilbert.toContextual {L S} [Language L] [Hilbert L S]
  {a : L} (Γ : Set L) : S a -> Contextual S Γ a := by
  intro ha
  exists ⟨[], (by simp)⟩
  exact mp (k a (⊥ 🡒 ⊥)) ha

@[grind] def Hilbert.em {L S} [DecidableEq L] [Language L] [Hilbert.Classical L S]
  (a : L) : S (a ⋎ ∼ a) := by
  let A := a ⋎ ∼ a
  let cnA : Contextual S {∼ A} (∼ A) := Contextual.initial (by simp)
  let cna : Contextual S {∼ A} (∼ a) :=
    Contextual.syll
      (disj_i1 a (∼ a) |> toContextual {∼ A})
      cnA
  let ca : Contextual S {∼ A} A :=
    Contextual.mp
      (disj_i2 a (∼ a) |> toContextual {∼ A})
      cna
  let cb : Contextual S {∼ A} ⊥ :=
    Contextual.mp cnA ca
  let cnnA : S (∼ ∼ A) := by
    apply Contextual.toHilbert
    rw [neg]
    apply Contextual.deduction_right
    exact cb |> Contextual.weakening (by simp)
  exact mp (Classical.dne A) cnnA

@[grind] def Hilbert.lin {L S} [DecidableEq L] [Language L] [Hilbert.Classical L S]
  (a b : L) : S (a ⋎ (a 🡒 b)) := by
  let h1 : S (a 🡒 a ⋎ (a 🡒 b)) := disj_i1 a (a 🡒 b)
  let c2 : Contextual S (∅ ∪ {a 🡒 ⊥} ∪ {a}) ⊥ :=
    axiomatized_mp a ⊥
    |> curry |> imp_exchange
    |> toContextual ∅
    |> Contextual.deduction_left
    |> Contextual.deduction_left
  let c3 : Contextual S (∅ ∪ {a 🡒 ⊥}) (a 🡒 b) :=
    Contextual.syll
      (Contextual.deduction_right c2)
      (Intuitionistic.exp b |> toContextual (∅ ∪ {a 🡒 ⊥}))
  let c4 : Contextual S (∅ ∪ {a 🡒 ⊥}) (a ⋎ (a 🡒 b)) :=
    Contextual.mp
      (disj_i2 a (a 🡒 b) |> toContextual (∅ ∪ {a 🡒 ⊥}))
      c3
  let h5 : S ((a 🡒 ⊥) 🡒 a ⋎ (a 🡒 b)) :=
    c4
    |> Contextual.deduction_right
    |> Contextual.toHilbert
  let h6 : S _ := disj_e a (a 🡒 ⊥) (a ⋎ (a 🡒 b))
  let h7 : S _ := mp (mp h6 h1) h5
  exact mp h7 (em a)
