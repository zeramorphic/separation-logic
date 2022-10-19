import camera

universe u

def next_ofe {α : Type u} (o : ofe α) : ofe α := {
  eq_at := λ n x y, @nat.rec (λ _, Prop) true (λ n _, x =[o, n] y) n,
  eq_at_equiv := begin
    intro n,
    cases n,
    { refine ⟨_, _, _⟩,
      { intro, trivial, },
      { intros x y h, trivial, },
      { intros x y z h₁ h₂, trivial, }, },
    refine ⟨_, _, _⟩,
    { intro x,
      exact eq_at_refl o _ _, },
    { intros x y h,
      simp_rw eq_at_symm,
      exact h, },
    { intros x y z h₁ h₂,
      exact eq_at_trans _ _ _ _ _ h₁ h₂, },
  end,
  eq_at_mono := begin
    intros m n hmn x y h,
    cases n,
    { simp only [nat.nat_zero_eq_zero, le_zero_iff] at hmn,
      rw hmn,
      trivial, },
    { cases m,
      { trivial, },
      exact o.eq_at_mono (nat.succ_le_succ_iff.mp hmn) x y h, },
  end,
  eq_at_limit := begin
    intros x y,
    split,
    { rintros rfl (n | n),
      { trivial, },
      simp only, },
    intro h,
    rw o.eq_at_limit x y,
    intro n,
    exact h (n + 1),
  end,
}

def next : Ofe ⥤ Ofe := {
  obj := λ α, ⟨α, next_ofe α.str⟩,
  map := λ α β f, ⟨f, begin
    intros n x y h,
    cases n,
    { trivial, },
    { exact f.prop n x y h, },
  end⟩,
}

lemma next_eq_at_iff {α : Ofe} (x y : α) (n : ℕ) :
  x =[(next.obj α).str, n] y ↔ @nat.rec (λ _, Prop) true (λ n _, x =[α.str, n] y) n := iff.rfl

@[simp] lemma next_map_apply {α β : Ofe} (f : α ⟶ β) (a : α) : next.map f a = f a := rfl

lemma next_locally_contractive : locally_contractive_functor next :=
begin
  intros α β n f g h a,
  cases n,
  { trivial, },
  { exact h n (lt_add_one n) a, },
end

structure monotone_nonexpansive (α : UCamera.{u}) :=
(to_fun : (α : Ofe.{u}) ⟶ SProp.{u})
(prop : ∀ n a b, @incln α α.str.to_camera n a b → SProp.incln (to_fun a) (to_fun b) n)

instance monotone_nonexpansive.setoid (α : UCamera) : setoid (monotone_nonexpansive α) := {
  r := λ x y, ∀ m a, (α.str.valid a).p m → ((x.to_fun a).p m ↔ (y.to_fun a).p m),
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

def UPredT (α : UCamera) : Type* := quotient (monotone_nonexpansive.setoid α)

def monotone_nonexpansive.eq_at {α : UCamera} (n : ℕ) (x y : monotone_nonexpansive α) : Prop :=
∀ m a, m ≤ n → (α.str.valid a).p m → ((x.to_fun a).p m ↔ (y.to_fun a).p m)

lemma monotone_nonexpansive.eq_at_respects_rel {α : UCamera} (n : ℕ)
  (a₁ a₂ b₁ b₂ : monotone_nonexpansive α) : a₁ ≈ b₁ → a₂ ≈ b₂ → a₁.eq_at n a₂ = b₁.eq_at n b₂ :=
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

def UPredT.eq_at {α : UCamera} (n : ℕ) : UPredT α → UPredT α → Prop :=
quotient.lift₂ (monotone_nonexpansive.eq_at n) (monotone_nonexpansive.eq_at_respects_rel n)

lemma UPredT.eq_at_reflexive {α : UCamera} (n : ℕ) (x : UPredT α) : UPredT.eq_at n x x :=
begin
  refine quotient.induction_on x _, clear x, intro x,
  intros m a hmn h,
  refl,
end

lemma UPredT.eq_at_symmetric {α : UCamera} (n : ℕ) (x y : UPredT α) :
  UPredT.eq_at n x y → UPredT.eq_at n y x :=
begin
  refine quotient.induction_on₂ x y _, clear x y, intros x y,
  intros h m a hmn ha,
  exact (h m a hmn ha).symm,
end

lemma UPredT.eq_at_transitive {α : UCamera} (n : ℕ) (x y z : UPredT α) :
  UPredT.eq_at n x y → UPredT.eq_at n y z → UPredT.eq_at n x z :=
begin
  refine quotient.induction_on₃ x y z _, clear x y z, intros x y z,
  intros hxy hyz m a hmn h,
  rw hxy m a hmn h,
  rw hyz m a hmn h,
end

lemma UPredT.eq_at_antitone (α : UCamera) :
  antitone (UPredT.eq_at : ℕ → UPredT α → UPredT α → Prop) :=
begin
  intros m n hmn x y,
  refine quotient.induction_on₂ x y _, clear x y, intros x y,
  intros h k a hk ha,
  exact h k a (hk.trans hmn) ha,
end

lemma UPredT.eq_at_limit {α : UCamera} (x y : UPredT α) : x = y ↔ ∀ n, x.eq_at n y :=
begin
  refine quotient.induction_on x _, clear x, intro x,
  split,
  { rintros rfl n,
    exact UPredT.eq_at_reflexive _ _, },
  refine quotient.induction_on y _, clear y, intro y,
  intro h,
  refine quotient.sound _,
  intros m a ha,
  exact h m m a le_rfl ha,
end

def monotone_nonexpansive.lim {α : UCamera.{u}}
  (c : chain (monotone_nonexpansive α) monotone_nonexpansive.eq_at) : monotone_nonexpansive α :=
begin
  refine ⟨⟨λ a, ⟨λ n, ∀ m ≤ n, (α.str.valid a).p m → ((c m).to_fun a).p m, _⟩, _⟩, _⟩,
  haveI := α.str,
  { intros m n hmn h k hk hak,
    exact h k (hk.trans hmn) hak, },
  { intros n x y h m hmn,
    split,
    { intros ha k hk hy,
      refine (c k).prop k x y _ _ le_rfl (ha k hk _),
      { refine ⟨α.str.unit, _⟩,
        rw [mul_comm, is_camera_unit.unit_mul],
        exact α.str.eq_at_mono (hk.trans hmn) x y h, },
      { have := camera.valid.prop k _ _ _ k le_rfl,
        refine this.mpr hy,
        exact α.str.eq_at_mono (hk.trans hmn) x y h, }, },
    { intros ha k hk hy,
      refine (c k).prop k y x _ _ le_rfl (ha k hk _),
      { refine ⟨α.str.unit, _⟩,
        rw [mul_comm, is_camera_unit.unit_mul],
        exact α.str.eq_at_mono (hk.trans hmn) y x ((α.str.eq_at_equiv n).2.1 h), },
      { have := camera.valid.prop k _ _ _ k le_rfl,
        refine this.mpr hy,
        exact α.str.eq_at_mono (hk.trans hmn) y x ((α.str.eq_at_equiv n).2.1 h), }, }, },
  { intros n a b hab m hmn h k hkm hb,
    refine (c k).prop n _ _ hab k (hkm.trans hmn) _,
    refine h k hkm _,
    obtain ⟨c, hc⟩ := hab,
    have := camera.valid.prop k,
    have := (this b (α.str.mul a c) _ k le_rfl).mp hb,
    { exact α.str.valid_mul _ _ _ _ le_rfl this, },
    refine (α.str.eq_at_equiv k).2.1 _,
    exact α.str.eq_at_mono (hkm.trans hmn) _ _ hc, },
end

lemma monotone_nonexpansive.complete {α : UCamera} (n : ℕ)
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
    exact ((c n).to_fun a).prop hk h, },
end

noncomputable def UPredT.chain_out {α : UCamera} (c : chain (UPredT α) UPredT.eq_at) :
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

noncomputable def UPredT.lim {α : UCamera} (c : chain (UPredT α) UPredT.eq_at) : UPredT α :=
⟦monotone_nonexpansive.lim (UPredT.chain_out c)⟧

lemma UPredT.complete {α : UCamera} (n : ℕ) (c : chain (UPredT α) UPredT.eq_at) :
  UPredT.eq_at n (UPredT.lim c) (c n) :=
begin
  rw ← quotient.out_eq (c n),
  intros m a hmn ha,
  exact monotone_nonexpansive.complete n (UPredT.chain_out c) m a hmn ha,
end

noncomputable def UPred (α : UCamera) : Cofe := {
  α := UPredT α,
  str := {
    eq_at := UPredT.eq_at,
    eq_at_equiv := λ n, ⟨UPredT.eq_at_reflexive n, UPredT.eq_at_symmetric n, UPredT.eq_at_transitive n⟩,
    eq_at_mono := UPredT.eq_at_antitone α,
    eq_at_limit := UPredT.eq_at_limit,
    lim := UPredT.lim,
    complete := UPredT.complete,
  },
}
