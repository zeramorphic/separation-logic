import algebra.ofe.basic

universe u

/-!
# Next
The type-level "later" construction.
-/

/-- The type-level "later". -/
@[ext] structure next (α : Type u) : Type u :=
(val : α)

instance (α : Type u) [ofe α] : ofe (next α) := {
  eq_at := λ n x y, @nat.rec (λ _, Prop) true (λ n _, x.val =[n] y.val) n,
  eq_at_reflexive := begin
    intros n x,
    cases n,
    trivial,
    simp only,
  end,
  eq_at_symmetric := begin
    intros n x y h,
    cases n,
    trivial,
    simp only at h ⊢,
    rw eq_at_symm_iff,
    exact h,
  end,
  eq_at_transitive := begin
    intros n x y z hxy hyz,
    cases n,
    trivial,
    simp only at hxy hyz ⊢,
    transitivity y.val,
    exact hxy,
    exact hyz,
  end,
  eq_at_mono' := begin
    intros m n hmn x y h,
    cases m,
    { trivial, },
    cases n,
    { simpa only [le_zero_iff, nat.succ_ne_zero] using hmn, },
    simp only at h ⊢,
    exact eq_at_mono (nat.succ_le_succ_iff.mp hmn) h,
  end,
  eq_at_limit' := begin
    intros x y h,
    ext,
    rw eq_at_limit,
    intro n,
    exact h (n + 1),
  end,
}

lemma next.eq_at_def {α : Type u} [ofe α] (x y : next α) (n : ℕ) :
  x =[n] y ↔ @nat.rec (λ _, Prop) true (λ n _, x.val =[n] y.val) n := iff.rfl

@[simp] lemma next.eq_at_iff {α : Type u} [ofe α] {x y : next α} {n : ℕ} :
  x =[n + 1] y ↔ x.val =[n] y.val := ⟨id, id⟩

def next.map {α β : Type u} [ofe α] [ofe β] : (α →ₙₑ β) →ₖ (next α →ₙₑ next β) :=
⟨λ f, ⟨λ a, next.mk (f a.val), begin
  intros n x y h,
  cases n,
  { trivial, },
  refine nonexpansive f _,
  rw ← next.eq_at_iff,
  exact h,
end⟩, begin
  intros n f g h a,
  cases n,
  { trivial, },
  { exact h n (nat.lt_succ_self n) a.val, },
end⟩

@[simp] lemma next.map_id {α : Type u} [ofe α] :
  next.map (nonexpansive_fun.id α) = nonexpansive_fun.id (next α) :=
by ext; refl

@[simp] lemma next.map_comp {α β γ : Type u} [ofe α] [ofe β] [ofe γ]
  (f : β →ₙₑ γ) (g : α →ₙₑ β) : next.map (f.comp g) = (next.map f).comp (next.map g) :=
by ext; refl

def next_functor : ofe_functor := {
  obj := next,
  ofe_obj := λ α [ofe α], by exactI next.ofe α,
  map := λ α β [ofe α] [ofe β], by exactI next.map,
  map_id := λ α [ofe α], by exactI next.map_id,
  map_comp := λ α β γ [ofe α] [ofe β] [ofe γ], by exactI next.map_comp,
}

lemma next_locally_contractive : locally_contractive_functor next_functor :=
begin
  introsI α β _ _ _ _,
  exact next.map.is_contractive',
end
