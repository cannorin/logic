import Logic.Classical.Syntax.Basic

abbrev Model (L : Type u) [Language L] := L -> Prop

structure Model.Tarskean {L : Type u} [Language L] (m : Model L) where
  bot : ¬ m bot
  conj {a b} : m (conj a b) <-> m a ∧ m b
  disj {a b} : m (disj a b) <-> m a ∨ m b
  imp {a b} : m (imp a b) <-> (m a -> m b)

@[simp] lemma Model.Tarskean.top
  {L} [Language L] {m : Model L} {t : Tarskean m}
  : m top := by
  simp only [t.imp, t.bot]
  trivial

@[simp, grind =>] lemma Model.Tarskean.neg
  {L} [Language L] {m : Model L} {t : Tarskean m} (a : L)
  : m (∼ a) <-> ¬ m a := by
  simp only [t.imp, t.bot]

@[simp, grind =>] lemma Model.Tarskean.equiv
  {L} [Language L] {m : Model L} {t : Tarskean m} (a b : L)
  : m (a 🡘 b) <-> (m a <-> m b) := by
  simp only [t.conj, t.imp]
  grind

@[simp, grind =>] lemma Model.Tarskean.bigconj
  {L} [Language L] {m : Model L} {t : Tarskean m} {xs : List L}
  : (m (bigconj xs) <-> ∀ x ∈ xs, m x) := by
  induction xs with
  | nil =>
    simp only [List.foldr_nil, List.not_mem_nil, false_implies, implies_true, iff_true]
    exact t.top
  | cons head tail ih =>
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]
    rw [t.conj]
    simp only [and_congr_right_iff]
    intro vh
    exact ih

@[simp, grind =>] lemma Model.Tarskean.bigdisj
  {L} [Language L] {m : Model L} {t : Tarskean m} {xs : List L}
  : (m (bigdisj xs) <-> ∃ x ∈ xs, m x) := by
  induction xs with
  | nil =>
    simp only [List.foldr_nil, List.not_mem_nil, false_and, exists_false, t.bot]
  | cons head tail ih =>
    simp only [List.foldr_cons, List.mem_cons, exists_eq_or_imp]
    rw [t.disj]
    exact or_congr_right ih
