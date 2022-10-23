import algebra.ofe.basic

universes u v w

instance {α : Type u} {β : Type v} [ofe α] [ofe β] : ofe (α × β) := {
  eq_at := λ n x y, x.1 =[n] y.1 ∧ x.2 =[n] y.2,
  eq_at_reflexive := begin
    intros n x,
    split;
    refl,
  end,
  eq_at_symmetric := begin
    intros n x y h,
    exact ⟨eq_at_symmetric n h.1, eq_at_symmetric n h.2⟩,
  end,
  eq_at_transitive := begin
    intros n x y z hxy hyz,
    exact ⟨eq_at_trans _ hxy.1 hyz.1, eq_at_trans _ hxy.2 hyz.2⟩,
  end,
  eq_at_mono' := begin
    intros m n hmn x y h,
    exact ⟨eq_at_mono hmn h.1, eq_at_mono hmn h.2⟩,
  end,
  eq_at_limit' := begin
    intros x y h,
    ext1;
    rw eq_at_limit;
    intro n,
    exact (h n).1,
    exact (h n).2,
  end,
}

@[simp] lemma prod.eq_at {α : Type u} {β : Type v} [ofe α] [ofe β] (n : ℕ) (x y : α × β) :
  x =[n] y ↔ x.1 =[n] y.1 ∧ x.2 =[n] y.2 := iff.rfl

lemma is_nonexpansive.uncurry_apply_eq_at {α : Type u} {β : Type v} {γ : Type w}
  [ofe α] [ofe β] [ofe γ] {f : α → β → γ}
  (h : is_nonexpansive (function.uncurry f)) {a b : α} {c d : β} {n : ℕ}
  (hab : a =[n] b) (hcd : c =[n] d) : f a c =[n] f b d :=
h (⟨hab, hcd⟩ : (a, c) =[n] (b, d))

/-!
# Locally nonexpansive bifunctors
We can now define bifunctors in terms of functors and the product OFE.
-/

def locally_nonexpansive_bifunctor (F : ofe_bifunctor) : Prop :=
∀ (α β γ δ : Type u) [ofe α] [ofe β] [ofe γ] [ofe δ],
begin
  resetI,
  letI := F.ofe_obj α β,
  letI := F.ofe_obj γ δ,
  exact is_nonexpansive (λ f, F.map f.1 f.2 :
    (γ →ₙₑ α) × (β →ₙₑ δ) → (F.obj α β →ₙₑ F.obj γ δ)),
end

def locally_contractive_bifunctor (F : ofe_bifunctor) : Prop :=
∀ (α β γ δ : Type u) [ofe α] [ofe β] [ofe γ] [ofe δ],
begin
  resetI,
  letI := F.ofe_obj α β,
  letI := F.ofe_obj γ δ,
  exact is_contractive (λ f, F.map f.1 f.2 :
    (γ →ₙₑ α) × (β →ₙₑ δ) → (F.obj α β →ₙₑ F.obj γ δ)),
end
