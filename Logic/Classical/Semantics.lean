import Logic.Classical.Syntax

@[simp] abbrev Valuation := Var -> Prop

@[simp, grind] def Valuation.isTrue (V : Valuation) : Fml -> Prop
  | ⊥ => False
  | *p => V p
  | a 🡒 b => isTrue V a -> isTrue V b
  | a ⋏ b => isTrue V a ∧ isTrue V b
  | a ⋎ b => isTrue V a ∨ isTrue V b

@[grind =] lemma Valuation.isTrue_neg {V a} : isTrue V (∼ a) <-> Not (isTrue V a) := by simp

@[grind .] lemma Valuation.isTrue_top {V} : isTrue V ⊤ := by simp

@[grind =] lemma Valuation.isTrue_equiv {V a b}
  : isTrue V (a 🡘 b) <-> Iff (isTrue V a) (isTrue V b) := by grind

@[grind =] lemma Valuation.isTrue_bigconj {V xs} : isTrue V (⋏ xs) <-> ∀ x ∈ xs, isTrue V x := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
    constructor
    case mp =>
      intro h x
      simp only [List.mem_cons]
      intro xmem
      cases xmem with
      | inl xmemL =>
        rw [xmemL]
        exact h.left
      | inr xmemR =>
        let hR := h.right
        apply ih.mp at hR
        specialize hR x
        exact hR xmemR
    case mpr =>
      intro h
      constructor
      case left =>
        specialize h head
        exact h List.mem_cons_self
      case right =>
        rw [ih]
        intro x xmem
        specialize h x
        have xmem : x ∈ head :: tail := by
          rw [List.mem_cons]
          exact Or.inr xmem
        exact h xmem

@[grind =] lemma Valuation.isTrue_bigdisj {V xs} : isTrue V (⋎ xs) <-> ∃ x ∈ xs, isTrue V x := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
    constructor
    case mp =>
      intro h
      rw [Fml.bigdisj, List.foldr_cons] at h
      cases h with
      | inl th =>
        exists head
        exact ⟨by simp, th⟩
      | inr tb =>
        rw [ih] at tb
        obtain ⟨x, ⟨xmem, tx⟩⟩ := tb
        exists x
        refine ⟨?_, tx⟩
        rw [List.mem_cons]
        right
        exact xmem
    case mpr =>
      intro ⟨x, ⟨xmem, tx⟩⟩
      rw [Fml.bigdisj, List.foldr_cons]
      rw [List.mem_cons] at xmem
      cases xmem with
      | inl e =>
        rw [<- e]
        exact Or.inl tx
      | inr xmem =>
        right
        rw [ih]
        exists x

@[simp] abbrev Valid (a : Fml) : Prop
  := ∀ {V : Valuation}, V.isTrue a

@[simp] abbrev ValidUnder (Γ : Set Fml) (a : Fml) : Prop
  := ∀ {V : Valuation}, (∀ b ∈ Γ, V.isTrue b) -> V.isTrue a

@[simp] lemma Valid.iff_validUnderEmpty {a : Fml} : Valid a <-> ValidUnder ∅ a := by simp
