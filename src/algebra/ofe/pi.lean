import algebra.ofe.prod

universes u v

instance pi.ofe {α : Type u} {β : α → Type v} [ofe α] [Π (a : α), ofe (β a)] :
  ofe (Π (a : α), β a) := {
  eq_at := λ n x y, ∀ a, x a =[n] y a,
  eq_at_reflexive := begin
    intros n x a,
    refl,
  end,
  eq_at_symmetric := begin
    intros n x y h a,
    rw eq_at_symm_iff,
    exact h a,
  end,
  eq_at_transitive := begin
    intros n x y z hxy hyz a,
    transitivity y a,
    exact hxy a,
    exact hyz a,
  end,
  eq_at_mono' := begin
    intros m n hmn x y h a,
    refine eq_at_mono hmn _,
    exact h a,
  end,
  eq_at_limit' := begin
    intros x y h,
    ext a,
    rw eq_at_limit,
    intro n,
    exact h n a,
  end,
}

@[simp] lemma pi.eq_at {α : Type u} {β : α → Type v} [ofe α] [Π (a : α), ofe (β a)]
  (n : ℕ) (x y : Π (a : α), β a) :
  x =[n] y ↔ ∀ a, x a =[n] y a := iff.rfl

def pi.ofe_bifunctor : ofe_bifunctor := {
  obj := λ α β [ofe α] [ofe β], by exactI α →ₙₑ β,
  map := λ α β γ δ [ofe α] [ofe β] [ofe γ] [ofe δ] f g,
    by exactI ⟨λ h, g.comp (h.comp f), begin
      intros n g h hgh,
      refine nonexpansive_fun.comp_left_eq_at _,
      refine nonexpansive_fun.comp_right_eq_at _,
      exact hgh,
    end⟩,
  map_id := by intros; ext; refl,
  map_comp := by intros; refl,
}

lemma pi.ofe_bifunctor_locally_nonexpansive : locally_nonexpansive_bifunctor pi.ofe_bifunctor :=
begin
  introsI α β γ δ _ _ _ _ _ _ n f₁ f₂ h g a,
  refine nonexpansive_fun.congr_fun_comp _ h.2 _,
  exact nonexpansive_fun.comp_left_eq_at h.1,
end
