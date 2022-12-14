import algebra.camera.basic

universe u

set_option old_structure_cmd true

/-!
# Uniform predicates
-/

@[ext] structure monotone_nonexpansive (α : Type u) [camera α] extends nonexpansive_fun α sprop :=
(mono : ∀ n a b, a ≼[n] b → to_fun a ⊆[n] to_fun b)

instance monotone_nonexpansive.fun_like (α : Type u) [camera α] :
  fun_like (monotone_nonexpansive α) α (λ _, sprop) := {
  coe := monotone_nonexpansive.to_fun,
  coe_injective' := by intros f g h; ext1; exact h,
}

instance monotone_nonexpansive.nonexpansive_fun_class (α : Type u) [camera α] :
  nonexpansive_fun_class (monotone_nonexpansive α) α sprop := {
  is_nonexpansive := monotone_nonexpansive.is_nonexpansive'
}

instance monotone_nonexpansive.setoid (α : Type u) [camera α] :
  setoid (monotone_nonexpansive α) := {
  r := λ x y, ∀ m a, ✓[m] a → (x a m ↔ y a m),
  iseqv := begin
    refine ⟨_, _, _⟩,
    { intros x n a h,
      refl, },
    { intros x y h m a h',
      rw h m a,
      exact h', },
    { intros x y z h₁ h₂ m a h',
      rw h₁ m a,
      rw h₂ m a,
      exact h',
      exact h', },
  end,
}

def upred (α : Type u) [camera α] : Type* := quotient (monotone_nonexpansive.setoid α)

def monotone_nonexpansive.eq_at {α : Type u} [camera α] (n : ℕ)
  (x y : monotone_nonexpansive α) : Prop :=
∀ m a, m ≤ n → ✓[m] a → (x a m ↔ y a m)

lemma monotone_nonexpansive.eq_at_respects_rel {α : Type u} [camera α] (n : ℕ)
  (a₁ a₂ b₁ b₂ : monotone_nonexpansive α) : a₁ ≈ b₁ →
    a₂ ≈ b₂ → monotone_nonexpansive.eq_at n a₁ a₂ = monotone_nonexpansive.eq_at n b₁ b₂ :=
begin
  intros h₁ h₂,
  ext1,
  split,
  { intros h m a hmn ha,
    rw ← h₁ m a ha,
    rw ← h₂ m a ha,
    exact h m a hmn ha, },
  { intros h m a hmn ha,
    rw h₁ m a ha,
    rw h₂ m a ha,
    exact h m a hmn ha, },
end

private def upred.eq_at {α : Type u} [camera α] (n : ℕ) : upred α → upred α → Prop :=
quotient.lift₂ (monotone_nonexpansive.eq_at n) (monotone_nonexpansive.eq_at_respects_rel n)

private lemma upred.eq_at_reflexive {α : Type u} [camera α] (n : ℕ)
  (x : upred α) : upred.eq_at n x x :=
begin
  refine quotient.induction_on x _, clear x, intro x,
  intros m a hmn h,
  refl,
end

private lemma upred.eq_at_symmetric {α : Type u} [camera α] (n : ℕ) (x y : upred α) :
  upred.eq_at n x y → upred.eq_at n y x :=
begin
  refine quotient.induction_on₂ x y _, clear x y, intros x y,
  intros h m a hmn ha,
  exact (h m a hmn ha).symm,
end

private lemma upred.eq_at_transitive {α : Type u} [camera α] (n : ℕ) (x y z : upred α) :
  upred.eq_at n x y → upred.eq_at n y z → upred.eq_at n x z :=
begin
  refine quotient.induction_on₃ x y z _, clear x y z, intros x y z,
  intros hxy hyz m a hmn h,
  rw hxy m a hmn h,
  rw hyz m a hmn h,
end

private lemma upred.eq_at_antitone {α : Type u} [camera α] :
  antitone (upred.eq_at : ℕ → upred α → upred α → Prop) :=
begin
  intros m n hmn x y,
  refine quotient.induction_on₂ x y _, clear x y, intros x y,
  intros h k a hk ha,
  exact h k a (hk.trans hmn) ha,
end

private lemma upred.eq_at_limit {α : Type u} [camera α] (x y : upred α) :
  (∀ n, upred.eq_at n x y) → x = y :=
begin
  refine quotient.induction_on x _, clear x, intro x,
  refine quotient.induction_on y _, clear y, intro y,
  intro h,
  refine quotient.sound _,
  intros m a ha,
  exact h m m a le_rfl ha,
end

private def monotone_nonexpansive.lim {α : Type u} [unital_camera α]
  (c : chain (monotone_nonexpansive α) monotone_nonexpansive.eq_at) : monotone_nonexpansive α :=
begin
  refine ⟨λ a, ⟨λ n, ∀ m ≤ n, ✓[m] a → c m a m, _⟩, _, _⟩,
  { intros m n hmn h k hk hak,
    exact h k (hk.trans hmn) hak, },
  { intros n x y h m hmn,
    split,
    { intros ha k hk hy,
      refine (c k).mono k x y _ _ le_rfl (ha k hk _),
      { refine ⟨1, _⟩,
        rw [mul_comm, one_mul],
        exact eq_at_mono (hk.trans hmn) h, },
      { have : camera.validn x =[n] camera.validn y := nonexpansive camera.validn h,
        rw this k (hk.trans hmn),
        exact hy, }, },
    { intros ha k hk hy,
      refine (c k).mono k y x _ _ le_rfl (ha k hk _),
      { refine ⟨1, _⟩,
        rw [mul_comm, one_mul],
        exact eq_at_mono (hk.trans hmn) (eq_at_symmetric n h), },
      { have : camera.validn x =[n] camera.validn y := nonexpansive camera.validn h,
        rw ← this k (hk.trans hmn),
        exact hy, }, }, },
  { intros n a b hab m hmn h k hkm hb,
    refine (c k).mono n _ _ hab k (hkm.trans hmn) _,
    refine h k hkm _,
    obtain ⟨c, hc⟩ := hab,
    have : camera.validn (a * c) =[n] camera.validn b := nonexpansive camera.validn hc,
    rw ← this k (hkm.trans hmn) at hb,
    exact camera.validn_mul a c k hb, },
end

private lemma monotone_nonexpansive.complete {α : Type u} [unital_camera α] (n : ℕ)
  (c : chain (monotone_nonexpansive α) monotone_nonexpansive.eq_at) :
  monotone_nonexpansive.eq_at n (monotone_nonexpansive.lim c) (c n) :=
begin
  intros m a hmn ha,
  split,
  { intro h,
    have := h m le_rfl ha,
    exact (c.prop m n hmn m a le_rfl ha).mp this, },
  { intros h k hk hak,
    refine (c.prop k n (hk.trans hmn) k a le_rfl hak).mpr _,
    exact (c n a).mono hk h, },
end

private noncomputable def upred.chain_out {α : Type u} [unital_camera α] (c : chain (upred α) upred.eq_at) :
  chain (monotone_nonexpansive α) monotone_nonexpansive.eq_at := {
  c := λ n, (c n).out,
  prop := begin
    intros m n hmn k a hk ha,
    have := c.prop m n hmn,
    rw ← quotient.out_eq (c.c m) at this,
    rw ← quotient.out_eq (c.c n) at this,
    exact this k a hk ha,
  end,
}

private noncomputable def upred.lim {α : Type u} [unital_camera α]
  (c : chain (upred α) upred.eq_at) : upred α :=
⟦monotone_nonexpansive.lim (upred.chain_out c)⟧

private lemma upred.complete {α : Type u} [unital_camera α] (n : ℕ) (c : chain (upred α) upred.eq_at) :
  upred.eq_at n (upred.lim c) (c n) :=
begin
  rw ← quotient.out_eq (c n),
  intros m a hmn ha,
  exact monotone_nonexpansive.complete n (upred.chain_out c) m a hmn ha,
end

instance upred_ofe (α : Type u) [camera α] : ofe (upred α) := {
  eq_at := upred.eq_at,
  eq_at_reflexive := upred.eq_at_reflexive,
  eq_at_symmetric := upred.eq_at_symmetric,
  eq_at_transitive := upred.eq_at_transitive,
  eq_at_mono' := upred.eq_at_antitone,
  eq_at_limit' := upred.eq_at_limit,
}

noncomputable instance upred_cofe (α : Type u) [unital_camera α] : cofe (upred α) := {
  lim := upred.lim,
  complete := upred.complete,
}

def upred.map_fun {α β : Type u} [unital_camera α] [unital_camera β] (f : α →ₖₕ β) :
  upred β → upred α :=
quotient.lift (λ g : monotone_nonexpansive β, ⟦{
  monotone_nonexpansive .
  to_fun := λ a, ⟨λ n, g (f a) n, λ m n hmn, (g (f a)).mono hmn⟩,
  is_nonexpansive' := begin
    intros n x y h m hmn,
    dsimp only [sprop.coe_fn_mk],
    have : f x =[n] f y := nonexpansive f h,
    split,
    exact g.mono n (f x) (f y) (incln_of_eq_at this) m hmn,
    exact g.mono n (f y) (f x) (incln_of_eq_at (eq_at_symmetric n this)) m hmn,
  end,
  mono := begin
    intros n x y h m hmn hm,
    have : f x ≼[n] f y := camera_hom.map_incln h,
    exact g.mono n (f x) (f y) this m hmn hm,
  end,
}⟧) begin
  intros x y h,
  refine quotient.sound _,
  intros n a hn,
  exact h n (f a) (f.map_valid' n a hn),
end

/-- `upred` is a locally nonexpansive functor from `unital_camera` to `cofe`. -/
def upred.map {α β : Type u} [unital_camera α] [unital_camera β] :
  (α →ₖₕ β) →ₙₑ (upred β →ₙₑ upred α) := {
  to_fun := λ f, ⟨upred.map_fun f, begin
    intros n p q,
    refine quotient.induction_on₂ p q _, clear p q, intros p q,
    intros h m a hmn hm,
    exact h m (f a) hmn (f.map_valid' m a hm),
  end⟩,
  is_nonexpansive' := begin
    intros n f g h p,
    refine quotient.induction_on p _, clear p, intro p,
    intros m a hmn hm,
    have : p (f a) =[n] p (g a) := nonexpansive p (h a),
    exact this _ hmn,
  end,
}
