import algebra.camera.option

universe u

lemma prod.mk_is_nonexpansive (α β : Type u) [ofe α] [ofe β] :
  is_nonexpansive (function.uncurry prod.mk : α × β → α × β) :=
is_nonexpansive_id

private lemma prod.camera.mul_is_nonexpansive {α β : Type u} [camera α] [camera β] :
  is_nonexpansive (function.uncurry ((*) : α × β → α × β → α × β)) :=
begin
  rintros n ⟨⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ ⟨⟨c₁, c₂⟩, ⟨d₁, d₂⟩⟩ ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩,
  simp only [function.uncurry_apply_pair, prod.mk_mul_mk, prod.eq_at] at *,
  split,
  exact camera.mul_eq_at h₁ h₃,
  exact camera.mul_eq_at h₂ h₄,
end

@[simp] lemma prod_mk_seq_some {α β : Type u} (a : option α) (b : option β) (c : α × β) :
  prod.mk <$> a <*> b = some c ↔ a = some c.1 ∧ b = some c.2 :=
begin
  cases a,
  tauto,
  cases b,
  tauto,
  simp only [option.map_eq_map, option.map_some', option.seq_some],
  exact prod.ext_iff,
end

@[simp] lemma prod_mk_seq_none {α β : Type u} (a : option α) (b : option β) :
  prod.mk <$> a <*> b = none ↔ a = none ∨ b = none :=
by cases a; cases b; tauto

@[simp] lemma prod_mk_seq_none_left {α β : Type u} (b : option β) :
  prod.mk <$> (none : option α) <*> b = none := rfl

@[simp] lemma prod_mk_seq_none_right {α β : Type u} (a : option α) :
  prod.mk <$> a <*> (none : option β) = none := by cases a; refl

private lemma prod.camera.core_mul_self {α β : Type u} [camera α] [camera β]
  (a : α × β) {ca : α × β} : prod.mk <$> core a.1 <*> core a.2 = some ca →
    ca * a = a :=
begin
  obtain ⟨a, b⟩ := a,
  obtain ⟨ca, cb⟩ := ca,
  intro hc,
  rw prod_mk_seq_some at hc,
  ext1,
  exact camera.core_mul_self a hc.1,
  exact camera.core_mul_self b hc.2,
end

private lemma prod.camera.core_core {α β : Type u} [camera α] [camera β]
  (a : α × β) {ca : α × β} : prod.mk <$> core a.1 <*> core a.2 = some ca →
    prod.mk <$> core ca.1 <*> core ca.2 = some ca :=
begin
  obtain ⟨a, b⟩ := a,
  obtain ⟨ca, cb⟩ := ca,
  intro hc,
  rw prod_mk_seq_some at hc ⊢,
  exact ⟨camera.core_core a hc.1, camera.core_core b hc.2⟩,
end

private lemma prod.camera.core_mono_some {α β : Type u} [camera α] [camera β]
  (a b : α × β) {ca : α × β} : prod.mk <$> core a.1 <*> core a.2 = some ca → a ≼ b →
    ∃ cb : α × β, prod.mk <$> core b.1 <*> core b.2 = some cb :=
begin
  obtain ⟨a₁, a₂⟩ := a,
  obtain ⟨b₁, b₂⟩ := b,
  obtain ⟨c₁, c₂⟩ := ca,
  rintros hc ⟨⟨d₁, d₂⟩, hd⟩,
  simp only [prod.mk_mul_mk, prod.mk.inj_iff] at hd,
  rw prod_mk_seq_some at hc,
  obtain ⟨e₁, he₁⟩ := camera.core_mono_some a₁ b₁ hc.1 ⟨d₁, hd.1⟩,
  obtain ⟨e₂, he₂⟩ := camera.core_mono_some a₂ b₂ hc.2 ⟨d₂, hd.2⟩,
  refine ⟨⟨e₁, e₂⟩, _⟩,
  rw prod_mk_seq_some,
  exact ⟨he₁, he₂⟩,
end

private lemma prod.camera.core_mono {α β : Type u} [camera α] [camera β]
  (a b : α × β) {ca : α × β} : prod.mk <$> core a.1 <*> core a.2 = some ca →
    a ≼ b → prod.mk <$> core a.1 <*> core a.2 ≼ prod.mk <$> core b.1 <*> core b.2 :=
begin
  obtain ⟨a₁, a₂⟩ := a,
  obtain ⟨b₁, b₂⟩ := b,
  obtain ⟨c₁, c₂⟩ := ca,
  rintros hc ⟨⟨d₁, d₂⟩, hd⟩,
  rw prod_mk_seq_some at hc,
  simp only [prod.mk_mul_mk, prod.mk.inj_iff] at hd,
  obtain ⟨e₁, he₁⟩ := camera.core_mono a₁ b₁ hc.1 ⟨d₁, hd.1⟩,
  obtain ⟨e₂, he₂⟩ := camera.core_mono a₂ b₂ hc.2 ⟨d₂, hd.2⟩,
  rw [← he₁, ← he₂],
  cases core a₁ with ca₁; cases core a₂ with ca₂,
  { rw prod_mk_seq_none_left, exact none_incl _, },
  { rw prod_mk_seq_none_left, exact none_incl _, },
  { rw prod_mk_seq_none_right, exact none_incl _, },
  simp only [option.map_some, option.seq_some],
  cases e₁; cases e₂,
  { rw [mul_none, mul_none, option.map_some, option.seq_some],
    exact ⟨none, rfl⟩, },
  { rw [mul_none, some_mul_some, option.map_some, option.seq_some],
    refine ⟨some (ca₁, e₂), _⟩,
    rw [some_mul_some, option.some_inj],
    ext1, swap, refl,
    rw mul_none at he₁,
    change ca₁ * ca₁ = ca₁,
    rw [← option.some_inj, ← some_mul_some, he₁, camera.core_mul_core], },
  { rw [mul_none, some_mul_some, option.map_some, option.seq_some],
    refine ⟨some (e₁, ca₂), _⟩,
    rw [some_mul_some, option.some_inj],
    ext1, refl,
    rw mul_none at he₂,
    change ca₂ * ca₂ = ca₂,
    rw [← option.some_inj, ← some_mul_some, he₂, camera.core_mul_core], },
  { rw [some_mul_some, some_mul_some, option.map_some, option.seq_some],
    refine ⟨some (e₁, e₂), rfl⟩, },
end

private lemma prod.camera.validn_mul {α β : Type u} [camera α] [camera β] (a b : α × β) :
  camera.validn (a * b).1 ⊓ camera.validn (a * b).2 ≤ camera.validn a.1 ⊓ camera.validn a.2 :=
begin
  rintros n ⟨ha, hb⟩,
  exact ⟨camera.validn_mul _ _ n ha, camera.validn_mul _ _ n hb⟩,
end

private lemma prod.camera.extend_mul_eq {α β : Type u} [camera α] [camera β] (n : ℕ)
  (a b₁ b₂ : α × β) (ha : ✓[n] a.1 ∧ ✓[n] a.2) (hb : a =[n] b₁ * b₂) :
  a = ((extend ha.1 hb.1).1, (extend ha.2 hb.2).1) * ((extend ha.1 hb.1).2, (extend ha.2 hb.2).2) :=
begin
  ext1,
  exact camera.extend_mul_eq ha.1 hb.1,
  exact camera.extend_mul_eq ha.2 hb.2,
end

private lemma prod.camera.extend_eq_at_left {α β : Type u} [camera α] [camera β] (n : ℕ)
  (a b₁ b₂ : α × β) (ha : ✓[n] a.1 ∧ ✓[n] a.2) (hb : a =[n] b₁ * b₂) :
  ((extend ha.1 hb.1).1, (extend ha.2 hb.2).1) =[n] b₁ :=
begin
  split,
  exact camera.extend_eq_at_left ha.1 hb.1,
  exact camera.extend_eq_at_left ha.2 hb.2,
end

private lemma prod.camera.extend_eq_at_right {α β : Type u} [camera α] [camera β] (n : ℕ)
  (a b₁ b₂ : α × β) (ha : ✓[n] a.1 ∧ ✓[n] a.2) (hb : a =[n] b₁ * b₂) :
  ((extend ha.1 hb.1).2, (extend ha.2 hb.2).2) =[n] b₂ :=
begin
  split,
  exact camera.extend_eq_at_right ha.1 hb.1,
  exact camera.extend_eq_at_right ha.2 hb.2,
end

instance prod.camera {α β : Type u} [camera α] [camera β] : camera (α × β) := {
  validn := ⟨λ a, camera.validn a.1 ⊓ camera.validn a.2, begin
    rintros n ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨hx, hy⟩,
    refine sprop.inf_eq_at _ _,
    exact nonexpansive camera.validn hx,
    exact nonexpansive camera.validn hy,
  end⟩,
  core := ⟨λ a, prod.mk <$> (core a.1) <*> (core a.2), begin
    rintros n ⟨a, b⟩ ⟨c, d⟩ ⟨hac, hbd⟩,
    refine option.seq_eq_at_seq _ _ _,
    exact prod.mk_is_nonexpansive α β,
    exact nonexpansive core hac,
    exact nonexpansive core hbd,
  end⟩,
  extend := λ n a b₁ b₂ h₁ h₂,
    (((extend h₁.1 h₂.1).1, (extend h₁.2 h₂.2).1), ((extend h₁.1 h₂.1).2, (extend h₁.2 h₂.2).2)),
  mul_is_nonexpansive := prod.camera.mul_is_nonexpansive,
  core_mul_self := prod.camera.core_mul_self,
  core_core := prod.camera.core_core,
  core_mono_some := prod.camera.core_mono_some,
  core_mono := prod.camera.core_mono,
  validn_mul := prod.camera.validn_mul,
  extend_mul_eq := prod.camera.extend_mul_eq,
  extend_eq_at_left := prod.camera.extend_eq_at_left,
  extend_eq_at_right := prod.camera.extend_eq_at_right,
  ..prod.ofe,
  ..prod.comm_semigroup,
}

lemma prod.can_update {α β : Type u} [camera α] [camera β] {a : α} {b : β} {A : set α} {B : set β} :
  a ↝ A → b ↝ B → (a, b) ↝ A ×ˢ B :=
begin
  rintros haA hbB n ⟨⟨c, d⟩, ⟨hc, hd⟩⟩,
  obtain ⟨fa, hfa⟩ := haA n ⟨c, hc⟩,
  obtain ⟨fb, hfb⟩ := hbB n ⟨d, hd⟩,
  exact ⟨⟨(fa.val, fb.val), fa.prop, fb.prop⟩, hfa, hfb⟩,
end
