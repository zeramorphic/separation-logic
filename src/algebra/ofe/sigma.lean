import algebra.ofe.basic

universes u v

/-- Applies `γ` to two `Σ` types. If their first components match, applies `γ` as expected,
otherwise, returns `false`. The cast is alright here, because we're inside `Prop`. -/
def map_or_false {α : Type u} {β : α → Type v} (γ : Π (x : α), β x → β x → Prop)
  (x y : Σ (x : α), β x) : Prop :=
@dite _ (x.fst = y.fst) (classical.dec _)
  (λ h, γ x.fst x.snd (cast (congr_arg β h.symm) y.snd))
  (λ _, false)

@[simp] lemma map_or_false_self {α : Type u} {β : α → Type v} (γ : Π (x : α), β x → β x → Prop)
  (x : Σ (x : α), β x) : map_or_false γ x x = γ x.fst x.snd x.snd :=
begin
  unfold map_or_false,
  rw dif_pos rfl,
  refl,
end

@[simp] lemma map_or_false_mk {α : Type u} {β : α → Type v} (γ : Π (x : α), β x → β x → Prop)
  (x : α) (y z : β x) : map_or_false γ ⟨x, y⟩ ⟨x, z⟩ = γ x y z :=
begin
  unfold map_or_false,
  rw dif_pos rfl,
  refl,
end

lemma map_or_false_implies {α : Type u} {β : α → Type v} {γ : Π (x : α), β x → β x → Prop}
  {x₁ x₂ : α} {y₁ : β x₁} {y₂ : β x₂} : map_or_false γ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ → x₁ = x₂ :=
begin
  unfold map_or_false,
  split_ifs,
  { cases h,
    exact λ _, rfl, },
  { intro h,
    cases h, },
end

instance {α : Type u} {β : α → Type v} [ofe α] [Π (a : α), ofe (β a)] :
  ofe (Σ (a : α), β a) := {
  eq_at := λ n x y, map_or_false (λ a b c, b =[n] c) x y,
  eq_at_reflexive := begin
    intros n x,
    rw map_or_false_self,
  end,
  eq_at_symmetric := begin
    rintros n ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h,
    cases map_or_false_implies h,
    rw map_or_false_mk at h ⊢,
    rw eq_at_symm_iff,
    exact h,
  end,
  eq_at_transitive := begin
    rintros n ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨z₁, z₂⟩ hxy hyz,
    cases map_or_false_implies hxy,
    cases map_or_false_implies hyz,
    rw map_or_false_mk at hxy hyz ⊢,
    transitivity y₂,
    exact hxy,
    exact hyz,
  end,
  eq_at_mono' := begin
    rintros m n hmn ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h,
    cases map_or_false_implies h,
    rw map_or_false_mk at h ⊢,
    exact eq_at_mono hmn h,
  end,
  eq_at_limit' := begin
    rintros ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h,
    cases map_or_false_implies (h 0),
    simp only [eq_self_iff_true, heq_iff_eq, true_and],
    rw eq_at_limit,
    intro n,
    have := h n,
    rw map_or_false_mk at this,
    exact this,
  end,
}

/-- TODO: Make nicer versions of this lemma. -/
@[simp] lemma sigma.eq_at {α : Type u} {β : α → Type v} [ofe α] [Π (a : α), ofe (β a)]
  (n : ℕ) (x y : Σ (a : α), β a) :
  x =[n] y ↔ map_or_false (λ a b c, b =[n] c) x y := iff.rfl
