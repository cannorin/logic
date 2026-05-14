import Logic.Classical.Syntax

inductive Provable : Fml -> Prop
  | k (a b: Fml) : Provable (a 🡒 b 🡒 a)
  | s (a b c: Fml) : Provable ((a 🡒 b 🡒 c) 🡒 (a 🡒 b) 🡒 (a 🡒 c))
  | conj_i (a b: Fml) : Provable (a 🡒 b 🡒 a ⋏ b)
  | conj_e1 (a b: Fml) : Provable (a ⋏ b 🡒 a)
  | conj_e2 (a b: Fml) : Provable (a ⋏ b 🡒 b)
  | disj_i1 (a b: Fml) : Provable (a 🡒 a ⋎ b)
  | disj_i2 (a b: Fml) : Provable (b 🡒 a ⋎ b)
  | disj_e (a b c: Fml) : Provable ((a 🡒 c) 🡒 (b 🡒 c) 🡒 (a ⋎ b 🡒 c))
  | dne (a: Fml) : Provable (∼ ∼ a 🡒 a)
  | mp {a b}: Provable (a 🡒 b) -> Provable a -> Provable b

@[grind .] lemma Provable.i (a : Fml) : Provable (a 🡒 a) := by
  let h1 := k a (a 🡒 a)
  let h2 := s a (a 🡒 a) a
  let h3 := mp h2 h1
  let h4 := k a a
  exact mp h3 h4

@[grind .] lemma Provable.verum : Provable ⊤ := i ⊥

@[grind ->] lemma Provable.syll {a b c : Fml}
  : Provable (a 🡒 b) -> Provable (b 🡒 c) -> Provable (a 🡒 c) := by
  intro hab hbc
  let habc := mp (k (b 🡒 c) a) hbc
  let habac := mp (s a b c) habc
  exact mp habac hab

@[grind .] lemma Provable.exp (a : Fml) : Provable (⊥ 🡒 a) := by
  let h1 := k ⊥ (a 🡒 ⊥)
  let h2 := dne a
  exact syll h1 h2

@[grind .] lemma Provable.top_imp {a : Fml} : Provable (⊤ 🡒 a) <-> Provable a := by
  constructor
  case mp =>
    intro h
    exact mp h verum
  case mpr =>
    intro h
    exact mp (k a ⊤) h

@[grind .] lemma Provable.imp_flip {a b c : Fml}
  : Provable (a 🡒 b 🡒 c) -> Provable (b 🡒 a 🡒 c) := by
  intro habc
  let h1 := mp (s a b c) habc
  let h2 := k b a
  exact syll h2 h1

@[grind ->] lemma Provable.imp_contract {a b : Fml} : Provable (a 🡒 a 🡒 b) -> Provable (a 🡒 b) := by
  intro haab
  let h1 := mp (s a a b) haab
  exact mp h1 (i a)

@[grind =] lemma Provable.imp_curry {a b c : Fml}
  : Provable (a 🡒 b 🡒 c) <-> Provable (a ⋏ b 🡒 c) := by
  constructor
  case mpr =>
    intro h
    let h1 := mp (k (a ⋏ b 🡒 c) b) h
    let h2 := mp (s b (a ⋏ b) c) h1
    let h3 := s a (b 🡒 a ⋏ b) (b 🡒 c)
    let h4 := mp (k ((b 🡒 a ⋏ b) 🡒 (b 🡒 c)) a) h2
    exact mp (mp h3 h4) (conj_i a b)
  case mp =>
    intro h
    let h1 := s (a ⋏ b) a (b 🡒 c)
    let h2 := mp (k (a 🡒 (b 🡒 c)) (a ⋏ b)) h
    let h3 := mp (mp h1 h2) (conj_e1 a b)
    let h4 := s (a ⋏ b) b c
    exact mp (mp h4 h3) (conj_e2 a b)

@[grind ->] lemma Provable.conj_i_alt {a b c : Fml}
  : Provable (a 🡒 b) -> Provable (a 🡒 c) -> Provable (a 🡒 b ⋏ c) := by
  intro hab hac
  let h1 := conj_i b c
  let h2 := syll hab h1
  let h3 := syll hac (imp_flip h2)
  exact imp_contract h3

@[grind .] lemma Provable.axiomatized_mp (a b : Fml) : Provable (a ⋏ (a 🡒 b) 🡒 b) := by
  let h1 := imp_flip (i (a 🡒 b))
  exact imp_curry.mp h1

@[grind .] lemma Provable.bigconj_e {xs : List Fml} {x : Fml} : x ∈ xs -> Provable (⋏ xs 🡒 x) := by
  intro xmem
  induction xs with
  | nil => contradiction
  | cons head tail ih =>
    rw [List.mem_cons] at xmem
    cases xmem with
    | inl e =>
      rw [e]
      exact conj_e1 head (⋏ tail)
    | inr xmem =>
      let ptail := conj_e2 head (⋏ tail)
      exact syll ptail (ih xmem)

@[grind .] lemma Provable.bigconj_e_singleton (x : Fml) : Provable (⋏ [x] 🡒 x) := by
  have mem : x ∈ [x] := by simp
  exact bigconj_e mem

@[grind .] lemma Provable.bigconj_e_conj (x y : Fml) : Provable (⋏ [x, y] 🡒 x ⋏ y) := by
    rw [Fml.bigconj, List.foldr_cons, List.foldr_cons, List.foldr_nil]
    rw [<- Provable.imp_curry]
    apply Provable.imp_flip
    rw [<- Provable.imp_curry]
    apply Provable.imp_flip
    rw [Provable.top_imp]
    apply Provable.imp_flip
    rw [Provable.imp_curry]
    exact Provable.i (x ⋏ y)

@[grind ->] lemma Provable.bigconj_e_many {xs ys : List Fml}
  : ys ⊆ xs -> Provable (⋏ xs 🡒 ⋏ ys) := by
  intro sub
  induction ys with
  | nil =>
    exact mp (k ⊤ (⋏ xs)) verum
  | cons head tail ih =>
    rw [List.cons_subset] at sub
    have subt : tail ⊆ xs := by
      intro y mem
      exact sub.right mem
    let ih := ih subt
    let phead := bigconj_e sub.left
    exact conj_i_alt phead ih

@[grind ->] lemma Provable.bigdisj_i {xs : List Fml} {x : Fml} : x ∈ xs -> Provable (x 🡒 ⋎ xs) := by
  intro xmem
  induction xs with
  | nil => contradiction
  | cons head tail ih =>
    rw [List.mem_cons] at xmem
    cases xmem with
    | inl e =>
      rw [e]
      exact disj_i1 head (⋎ tail)
    | inr xmem =>
      let ptail := disj_i2 head (⋎ tail)
      exact syll (ih xmem) ptail

@[grind .] lemma Provable.bigdisj_i_singleton (x : Fml) : Provable (x 🡒 ⋎ [x]) := by
  have mem : x ∈ [x] := by simp
  exact bigdisj_i mem

@[grind .] lemma Provable.bigdisj_i_disj (x y : Fml) : Provable (x ⋎ y 🡒 ⋎ [x, y]) := by
  rw [Fml.bigdisj, List.foldr_cons, List.foldr_cons, List.foldr_nil]
  have h3 := Provable.disj_e x y (x ⋎ y ⋎ ⊥)
  have h4 := Provable.mp h3 (Provable.disj_i1 x (y ⋎ ⊥))
  have h5 : Provable (y 🡒 x ⋎ (y ⋎ ⊥)) := by
    have h6 := Provable.disj_i1 y ⊥
    have h7 := Provable.disj_i2 x (y ⋎ ⊥)
    exact Provable.syll h6 h7
  exact Provable.mp h4 h5

@[grind ->] lemma Provable.bigdisj_i_many {xs ys : List Fml}
  : ys ⊆ xs -> Provable (⋎ ys 🡒 ⋎ xs) := by
  intro sub
  induction ys with
  | nil =>
    rw [Fml.bigdisj, List.foldr_nil]
    exact exp (⋎ xs)
  | cons head tail ih =>
    rw [List.cons_subset] at sub
    have subt : tail ⊆ xs := by
      intro y mem
      exact sub.right mem
    let ih := ih subt
    let phead := bigdisj_i sub.left
    let h := disj_e head (⋎ tail) (⋎ xs)
    exact mp (mp h phead) ih

@[grind .] lemma Provable.bigdisj_e_same {a : Fml} {xs : List Fml}
  : (∀ x ∈ xs, x = a) -> Provable (⋎ xs 🡒 a) := by
  intro forall_eq_a
  induction xs with
  | nil =>
    rw [Fml.bigdisj_empty_is_bot]
    exact Provable.exp a
  | cons x xs ih =>
    have eq : x = a := by
      specialize forall_eq_a x
      apply forall_eq_a
      rw [List.mem_cons]
      exact Or.inl (refl x)
    rw [eq]
    have forall_eq_a : ∀ y ∈ xs, y = a := by
      intro y ymem
      have ymem : y ∈ x :: xs := by
        rw [List.mem_cons]
        exact Or.inr ymem
      specialize forall_eq_a y
      exact forall_eq_a ymem
    let ih := ih forall_eq_a
    exact mp (mp (disj_e a (⋎ xs) a) (i a)) ih

@[grind ->] lemma Provable.bigconj_to_bigdisj {a : Fml} {xs ys : List Fml}
  : a ∈ xs -> a ∈ ys -> Provable (⋏ xs 🡒 ⋎ ys) := by
  intro memx memy
  let lhs := bigconj_e memx
  let rhs := bigdisj_i memy
  exact syll lhs rhs

@[simp] abbrev ProvableFrom (Γ : Theory) (a : Fml) : Prop
  := ∃ xs, List.IsSubset xs Γ ∧ Provable (⋏ xs 🡒 a)

theorem deduction {Γ : Theory} {a b : Fml}
  : ProvableFrom Γ (a 🡒 b) <-> ProvableFrom (Γ ∪ {a}) b := by
  constructor
  case mpr =>
    intro ⟨xs, ⟨sub, p⟩⟩
    let nota (x: Fml) := x ≠ a
    let ys := List.remove xs a
    exists ys
    constructor
    case right =>
      have ys_reord : xs ⊆ a :: ys := by grind
      let h1 := Provable.bigconj_e_many ys_reord
      let h2 := Provable.syll h1 p
      exact Provable.imp_flip (Provable.imp_curry.mpr h2)
    case left =>
      intro y ymem
      specialize sub y
      have ys_sub_xs : ys ⊆ xs := by grind
      let ymem' := sub (ys_sub_xs ymem)
      rw [Set.mem_union] at ymem'
      cases ymem' with
      | inl h => exact h
      | inr e =>
        have a_notin_ys : a ∉ ys := by grind
        rw [Set.mem_singleton_iff] at e
        have : y ∉ ys := by
          rw [e]
          exact a_notin_ys
        contradiction
  case mp =>
    intro ⟨xs, ⟨sub, p⟩⟩
    exists a :: xs
    constructor
    case right =>
      exact p |> Provable.imp_flip |> Provable.imp_curry.mp
    case left =>
      intro x xmem
      rw [List.mem_cons] at xmem
      rw [Set.mem_union]
      cases xmem with
      | inl e =>
        right
        rw [Set.mem_singleton_iff]
        exact e
      | inr xmem' =>
        left
        specialize sub x
        exact sub xmem'

@[grind =] lemma provable_iff_provableFromEmpty {a : Fml} : Provable a <-> ProvableFrom ∅ a := by
  constructor
  case mp =>
    intro l
    exists []
    refine ⟨by trivial, ?_⟩
    exact Provable.mp (Provable.k a (⊥ 🡒 ⊥)) l
  case mpr =>
    intro ⟨xs, ⟨hPL, hPR⟩⟩
    have p : Provable ((⊥ 🡒 ⊥) 🡒 a) := by
      have e : xs = [] := by
        by_contra ne
        specialize hPL (xs.head ne)
        have : xs.head ne ∈ xs := List.head_mem ne
        contradiction
      rw [e] at hPR
      exact hPR
    exact Provable.mp p (Provable.i ⊥)

@[grind .] lemma ProvableFrom.initial {Γ : Theory} {a : Fml} : a ∈ Γ -> ProvableFrom Γ a := by
  intro amem
  exists [a]
  constructor
  case left =>
    intro b bmem
    rw [List.mem_singleton] at bmem
    rw [bmem]
    exact amem
  case right =>
    exact Provable.conj_e1 a ⊤

lemma ProvableFrom.weakening {Γ Δ : Theory} {a : Fml}
  : Γ ⊆ Δ -> ProvableFrom Γ a -> ProvableFrom Δ a := by
  intro sub_Γ ⟨xs, ⟨sub_xs, p⟩⟩
  have sub_xs : List.IsSubset xs Δ := by
    intro x mem
    exact Set.mem_of_subset_of_mem sub_Γ (sub_xs x mem)
  exists xs

lemma ProvableFrom.mp {Γ : Theory} {a b : Fml}
  : ProvableFrom Γ (a 🡒 b) -> ProvableFrom Γ a ->  ProvableFrom Γ b := by
  intro ⟨xsab, ⟨sub_xsab, pab⟩⟩ ⟨xsa, ⟨sub_xsa, pa⟩⟩
  let xsb := xsa ++ xsab
  have sub_xsb : List.IsSubset xsb Γ := by
    intro x xmem
    rw [List.mem_append] at xmem
    cases xmem with
    | inl hl =>
      specialize sub_xsa x
      exact sub_xsa hl
    | inr hr =>
      specialize sub_xsab x
      exact sub_xsab hr
  exists xsb
  refine ⟨sub_xsb, ?_⟩
  have sub_xsa_xsb : xsa ⊆ xsb := List.subset_append_left xsa xsab
  have sub_xsab_xsb : xsab ⊆ xsb := List.subset_append_right xsa xsab
  let ha  := Provable.syll (Provable.bigconj_e_many sub_xsa_xsb) pa
  let hab := Provable.syll (Provable.bigconj_e_many sub_xsab_xsb) pab
  let habb := Provable.conj_i_alt ha hab
  exact Provable.syll habb (Provable.axiomatized_mp a b)

lemma ProvableFrom.syll {Γ : Theory} {a b c : Fml}
: ProvableFrom Γ (a 🡒 b) -> ProvableFrom Γ (b 🡒 c) -> ProvableFrom Γ (a 🡒 c) := by
  intro pab pbc
  rw [deduction]
  rw [deduction] at pab
  have sub : Γ ⊆ Γ ∪ {a} := by simp
  let pabc := weakening sub pbc
  exact mp pabc pab

lemma Provable.to_ProvableFrom {a} (Γ : Theory) (p : Provable a) : ProvableFrom Γ a := by
  rw [provable_iff_provableFromEmpty] at p
  have sub : ∅ ⊆ Γ := by simp only [Set.empty_subset]
  exact ProvableFrom.weakening sub p

@[grind .] lemma Provable.em (a : Fml) : Provable (a ⋎ ∼ a) := by
  let A := a ⋎ ∼ a
  let pnA : ProvableFrom {∼ A} (∼ A) := ProvableFrom.initial (by simp)
  let pna : ProvableFrom {∼ A} (∼ a) :=
    ProvableFrom.syll
      (to_ProvableFrom {∼ A} (disj_i1 a (∼ a)))
      pnA
  let pa : ProvableFrom {∼ A} A :=
    ProvableFrom.mp
      (to_ProvableFrom {∼ A} (disj_i2 a (∼ a)))
      pna
  let pb : ProvableFrom {∼ A} ⊥ := ProvableFrom.mp pnA pa
  let pnnA : Provable (∼ ∼ A) :=
    provable_iff_provableFromEmpty.mpr <|
      deduction.mpr (ProvableFrom.weakening (by simp) pb)
  exact mp (dne A) pnnA

@[grind .] lemma Provable.lin (a b : Fml) : Provable (a ⋎ (a 🡒 b)) := by
  let p1 : Provable (a 🡒 a ⋎ (a 🡒 b)) := disj_i1 a (a 🡒 b)
  let p2 : ProvableFrom (∅ ∪ {a 🡒 ⊥} ∪ {a}) ⊥ :=
    axiomatized_mp a ⊥
    |> imp_curry.mpr |> imp_flip
    |> to_ProvableFrom ∅
    |> deduction.mp |> deduction.mp
  let p3 : ProvableFrom (∅ ∪ {a 🡒 ⊥}) (a 🡒 b) :=
    ProvableFrom.syll (deduction.mpr p2) (exp b |> to_ProvableFrom (∅ ∪ {a 🡒 ⊥}))
  let p4 : ProvableFrom (∅ ∪ {a 🡒 ⊥}) (a ⋎ (a 🡒 b)) :=
    ProvableFrom.mp (disj_i2 a (a 🡒 b) |> to_ProvableFrom (∅ ∪ {a 🡒 ⊥})) p3
  let p5 : Provable ((a 🡒 ⊥) 🡒 a ⋎ (a 🡒 b)) :=
    p4 |> deduction.mpr |> provable_iff_provableFromEmpty.mpr
  let p6 :=
    disj_e a (a 🡒 ⊥) (a ⋎ (a 🡒 b))
  let p7 := mp (mp p6 p1) p5
  exact mp p7 (em a)
