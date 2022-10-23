import algebra.ofe.basic

universes u v

instance {α : Type u} {β : Type v} [ofe α] [ofe β] : ofe (α ⊕ β) := {
  eq_at := λ n x y, sum.elim
    (λ a, sum.elim (λ b, a =[n] b) (λ _, false) y)
    (λ a, sum.elim (λ _, false) (λ b, a =[n] b) y) x,
  eq_at_reflexive := begin
    intros n x,
    cases x;
    simp only [sum.elim_inl, sum.elim_inr],
  end,
  eq_at_symmetric := begin
    intros n x y h,
    cases x; cases y;
    simp only [sum.elim_inl, sum.elim_inr] at h ⊢;
    try { exact h, };
    exact eq_at_symmetric n h,
  end,
  eq_at_transitive := begin
    intros n x y z hxy hyz,
    cases x; cases y; cases z;
    simp only [sum.elim_inl, sum.elim_inr] at hxy hyz ⊢;
    try { cases hyz, };
    try { cases hxy, };
    transitivity y;
    assumption,
  end,
  eq_at_mono' := begin
    intros m n hmn x y h,
    cases x; cases y;
    simp only [sum.elim_inl, sum.elim_inr] at h ⊢;
    try { exact h, };
    exact eq_at_mono hmn h,
  end,
  eq_at_limit' := begin
    intros x y h,
    cases x; cases y;
    simp only [sum.elim_inl, sum.elim_inr] at h ⊢;
    try { exact (h 0), };
    rw eq_at_limit;
    exact h,
  end,
}

/-- TODO: Make nicer versions of this lemma. -/
@[simp] lemma sum.eq_at {α : Type u} {β : Type v} [ofe α] [ofe β] (n : ℕ) (x y : α ⊕ β) :
  x =[n] y ↔ sum.elim
    (λ a, sum.elim (λ b, a =[n] b) (λ _, false) y)
    (λ a, sum.elim (λ _, false) (λ b, a =[n] b) y) x := iff.rfl
