import camera

universe u

@[simp] lemma option.none_eq_at {α : Type u} [ofe α] {n : ℕ} {a : option α} :
  none =[n] a ↔ a = none :=
begin
  split,
  { intro h,
    cases h,
    refl, },
  { rintro rfl,
    refl, },
end

@[simp] lemma option.eq_at_none {α : Type u} [ofe α] {n : ℕ} {a : option α} :
  a =[n] none ↔ a = none :=
begin
  rw ← option.none_eq_at,
  symmetry,
end

lemma option.some_eq_at {α : Type u} [ofe α] {n : ℕ} {a : α} {b : option α} :
  some a =[n] b → b.is_some :=
begin
  intro h,
  cases b,
  cases h,
  simp only [option.is_some_some, coe_sort_tt],
end

lemma option.eq_at_some {α : Type u} [ofe α] {n : ℕ} {a : option α} {b : α} :
  a =[n] some b → a.is_some :=
begin
  intro h,
  symmetry' at h,
  exact option.some_eq_at h,
end

@[simp] lemma option.some_eq_at_some {α : Type u} [ofe α] {n : ℕ} {a b : α} :
  some a =[n] some b ↔ a =[n] b :=
begin
  split,
  intro h, cases h, assumption,
  intro h, exact option.eq_at_prop.some h,
end

lemma option.map_nonexpansive {α β : Type u} [ofe α] [ofe β] (f : α → β) (hf : is_nonexpansive f) :
  is_nonexpansive (option.map f) :=
begin
  intros n a b h,
  cases h,
  { refine option.eq_at_prop.some _,
    refine hf _, assumption, },
  { refl, },
end

lemma option.map_eq_at_map {α β γ : Type u} [ofe α] [ofe β] [ofe γ] {n : ℕ}
  {f : α → β} {a b : option α} :
  is_nonexpansive f → a =[n] b → f <$> a =[n] f <$> b:=
begin
  intros hf hac,
  cases a,
  simpa only [option.map_eq_map, option.map_none', option.none_eq_at, option.map_eq_none'] using hac,
  cases b,
  cases hac,
  simp only [option.map_eq_map, option.map_some', option.some_eq_at_some] at hac ⊢,
  exact hf hac,
end

lemma option.seq_eq_at_seq {α β γ : Type u} [ofe α] [ofe β] [ofe γ] {n : ℕ}
  {f : α → β → γ} {a b : option α} {c d : option β} :
  is_nonexpansive (function.uncurry f) →
  a =[n] b → c =[n] d → f <$> a <*> c =[n] f <$> b <*> d :=
begin
  intros hf hac hbd,
  cases a,
  { rw option.none_eq_at at hac,
    rw hac,
    refl, },
  cases b,
  { cases hac, },
  cases c,
  { rw option.none_eq_at at hbd,
    rw hbd,
    refl, },
  cases d,
  { cases hbd, },
  simp only [option.map_eq_map, option.map_some', option.seq_some, option.some_eq_at_some],
  rw option.some_eq_at_some at hac hbd,
  exact hf.uncurry_apply_eq_at hac hbd,
end

@[simp] lemma option.not_none_is_some {α : Type*} : (none : option α).is_some ↔ false :=
by finish

@[simp] lemma option.some_is_some {α : Type*} {a : α} : (some a).is_some :=
by solve_by_elim

@[simp] lemma option.not_some_seq_none_is_some {α β : Type*} {f : α → β} :
  (some f <*> none).is_some ↔ false :=
by finish

@[simp] lemma option.not_none_seq_some_is_some {α β : Type*} {a : α} :
  ((none : option (α → β)) <*> some a).is_some ↔ false :=
by finish

@[simp] lemma option.not_none_seq_none_is_some {α β : Type*} :
  ((none : option (α → β)) <*> none).is_some ↔ false :=
by finish

@[simp] lemma option.map_is_some_iff {α β : Type*} {f : α → β} {a : option α} :
  (f <$> a).is_some ↔ a.is_some :=
by cases a; refl

@[simp] lemma option.seq_is_some_iff {α β : Type*} {f : option (α → β)} {a : option α} :
  (f <*> a).is_some ↔ f.is_some ∧ a.is_some :=
begin
  cases f; cases a;
  simp only [option.not_none_is_some, option.some_is_some, option.seq_some,
    option.not_some_seq_none_is_some, option.not_none_seq_some_is_some,
    option.not_none_seq_none_is_some, and_self, false_and, and_false],
end

/-!
# Product camera
-/

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

/-!
# Sum camera
-/

inductive sum_camera (α β : Type u)
| cinl : α → sum_camera
| cinr : β → sum_camera
| invalid : sum_camera

namespace sum_camera

infixr ` ⊕ₖ `:30 := sum_camera

lemma cinl_injective {α β : Type u} : function.injective (cinl : α → sum_camera α β) :=
by intros x y h; cases h; refl

lemma cinr_injective {α β : Type u} : function.injective (cinr : β → sum_camera α β) :=
by intros x y h; cases h; refl

inductive eq_at_prop {α β : Type u} [ofe α] [ofe β] (n : ℕ) : α ⊕ₖ β → α ⊕ₖ β → Prop
| cinl : Π {a b : α}, a =[n] b → eq_at_prop (cinl a) (cinl b)
| cinr : Π {a b : β}, a =[n] b → eq_at_prop (cinr a) (cinr b)
| invalid : eq_at_prop invalid invalid

instance ofe {α β : Type u} [ofe α] [ofe β] : ofe (α ⊕ₖ β) := {
  eq_at := eq_at_prop,
  eq_at_reflexive := begin
    intros n a,
    cases a,
    { refine eq_at_prop.cinl _, refl, },
    { refine eq_at_prop.cinr _, refl, },
    { exact eq_at_prop.invalid, },
  end,
  eq_at_symmetric := begin
    intros n a b h,
    cases h,
    { refine eq_at_prop.cinl _, symmetry, assumption, },
    { refine eq_at_prop.cinr _, symmetry, assumption, },
    { exact eq_at_prop.invalid, },
  end,
  eq_at_transitive := begin
    intros n a b c hab hbc,
    cases hab with a₁ b₁ hab₁ a₂ b₂ hab₂,
    { cases c; cases hbc with hbc,
      refine eq_at_prop.cinl _, transitivity b₁; assumption, },
    { cases c; cases hbc with hbc,
      refine eq_at_prop.cinr _, transitivity b₂; assumption, },
    { cases c; cases hbc with hbc,
      exact eq_at_prop.invalid, },
  end,
  eq_at_mono' := begin
    intros m n hmn a b h,
    cases h,
    { refine eq_at_prop.cinl _, refine eq_at_mono hmn _, assumption, },
    { refine eq_at_prop.cinr _, refine eq_at_mono hmn _, assumption, },
    { exact eq_at_prop.invalid, },
  end,
  eq_at_limit' := begin
    intros a b h,
    cases h 0,
    { refine congr_arg _ _, rw eq_at_limit,
      intro n, cases h n, assumption, },
    { refine congr_arg _ _, rw eq_at_limit,
      intro n, cases h n, assumption, },
    { refl, },
  end,
}

lemma cinl_is_nonexpansive {α β : Type u} [ofe α] [ofe β] :
  is_nonexpansive (cinl : α → α ⊕ₖ β) :=
λ m a b, eq_at_prop.cinl

lemma cinr_is_nonexpansive {α β : Type u} [ofe α] [ofe β] :
  is_nonexpansive (cinr : β → α ⊕ₖ β) :=
λ m a b, eq_at_prop.cinr

@[simp] lemma cinl_eq_at_cinl {α β : Type u} [ofe α] [ofe β] {n : ℕ} {a b : α} :
  (cinl a : α ⊕ₖ β) =[n] cinl b ↔ a =[n] b :=
begin
  split,
  { rintro (h | h | h),
    assumption, },
  { exact eq_at_prop.cinl, },
end

@[simp] lemma cinr_eq_at_cinr {α β : Type u} [ofe α] [ofe β] {n : ℕ} {a b : β} :
  (cinr a : α ⊕ₖ β) =[n] cinr b ↔ a =[n] b :=
begin
  split,
  { rintro (h | h | h),
    assumption, },
  { exact eq_at_prop.cinr, },
end

lemma cinl_eq_at {α β : Type u} [ofe α] [ofe β] {n : ℕ} {a : α} {b : α ⊕ₖ β} :
  cinl a =[n] b → ∃ b', b = cinl b' :=
begin
  rintro (h | h | h),
  exact ⟨_, rfl⟩,
end

lemma cinr_eq_at {α β : Type u} [ofe α] [ofe β] {n : ℕ} {a : β} {b : α ⊕ₖ β} :
  cinr a =[n] b → ∃ b', b = cinr b' :=
begin
  rintro (h | h | h),
  exact ⟨_, rfl⟩,
end

lemma invalid_eq_at {α β : Type u} [ofe α] [ofe β] {n : ℕ} {b : α ⊕ₖ β} :
  invalid =[n] b → b = invalid :=
begin
  rintro (h | h | h),
  refl,
end

def mul {α β : Type u} [comm_semigroup α] [comm_semigroup β] : α ⊕ₖ β → α ⊕ₖ β → α ⊕ₖ β
| (cinl a) (cinl b) := cinl (a * b)
| (cinr a) (cinr b) := cinr (a * b)
| _ _ := invalid

instance comm_semigroup {α β : Type u} [comm_semigroup α] [comm_semigroup β] :
  comm_semigroup (α ⊕ₖ β) := {
  mul := mul,
  mul_assoc := begin
    intros a b c,
    cases a; cases b; cases c;
    try { refl, },
    refine congr_arg cinl _, rw mul_assoc,
    refine congr_arg cinr _, rw mul_assoc,
  end,
  mul_comm := begin
    intros a b,
    cases a; cases b;
    try { refl, },
    refine congr_arg cinl _, rw mul_comm,
    refine congr_arg cinr _, rw mul_comm,
  end,
}

lemma cinl_mul_cinl {α β : Type u} [comm_semigroup α] [comm_semigroup β] {a b : α} :
  (cinl a : α ⊕ₖ β) * cinl b = cinl (a * b) := rfl

lemma cinr_mul_cinr {α β : Type u} [comm_semigroup α] [comm_semigroup β] {a b : β} :
  (cinr a : α ⊕ₖ β) * cinr b = cinr (a * b) := rfl

lemma cinl_eq_mul {α β : Type u} [comm_semigroup α] [comm_semigroup β] {a : α} {b c : α ⊕ₖ β} :
  cinl a = b * c → ∃ b' c', b = cinl b' ∧ c = cinl c' :=
begin
  cases b; cases c,
  repeat { intro h, cases h, },
  exact ⟨b, c, rfl, rfl⟩,
end

lemma cinr_eq_mul {α β : Type u} [comm_semigroup α] [comm_semigroup β] {a : β} {b c : α ⊕ₖ β} :
  cinr a = b * c → ∃ b' c', b = cinr b' ∧ c = cinr c' :=
begin
  cases b; cases c,
  repeat { intro h, cases h, },
  exact ⟨b, c, rfl, rfl⟩,
end

def validn {α β : Type u} [camera α] [camera β] : α ⊕ₖ β → sprop
| (cinl a) := camera.validn a
| (cinr a) := camera.validn a
| invalid := ⊥

def core {α β : Type u} [camera α] [camera β] : α ⊕ₖ β → option (α ⊕ₖ β)
| (cinl a) := (camera.core a).map cinl
| (cinr a) := (camera.core a).map cinr
| invalid := some invalid

def extend {α β : Type u} [camera α] [camera β] {n : ℕ} : Π {a b₁ b₂ : α ⊕ₖ β},
  validn a n → a =[n] b₁ * b₂ → (α ⊕ₖ β) × (α ⊕ₖ β)
| (cinl a) (cinl b₁) (cinl b₂) va hab :=
  (cinl (camera.extend va (by cases hab; assumption)).1,
   cinl (camera.extend va (by cases hab; assumption)).2)
| (cinr a) (cinr b₁) (cinr b₂) va hab :=
  (cinr (camera.extend va (by cases hab; assumption)).1,
   cinr (camera.extend va (by cases hab; assumption)).2)
| (cinl a) (cinl b₁) (cinr b₂) va hab := by exfalso; cases hab
| (cinl a) (cinl b₁) invalid va hab := by exfalso; cases hab
| (cinl a) (cinr b₁) b₂ va hab := by exfalso; cases b₂; cases hab
| (cinl a) invalid b₂ va hab := by exfalso; cases hab
| (cinr a) (cinr b₁) (cinl b₂) va hab := by exfalso; cases hab
| (cinr a) (cinr b₁) invalid va hab := by exfalso; cases hab
| (cinr a) (cinl b₁) b₂ va hab := by exfalso; cases b₂; cases hab
| (cinr a) invalid b₂ va hab := by exfalso; cases hab
| invalid _ b₂ va hab := by exfalso; cases va

private lemma mul_is_nonexpansive {α β : Type u} [camera α] [camera β] :
  is_nonexpansive (function.uncurry ((*) : α ⊕ₖ β → α ⊕ₖ β → α ⊕ₖ β)) :=
begin
  rintros n ⟨a, b⟩ ⟨c, d⟩ ⟨h₁, h₂⟩,
  cases h₁,
  case invalid { refl, },
  { cases h₂,
    case cinr { refl, },
    case invalid { refl, },
    refine cinl_is_nonexpansive _,
    refine camera.mul_eq_at _ _; assumption, },
  { cases h₂,
    case cinl { refl, },
    case invalid { refl, },
    refine cinr_is_nonexpansive _,
    refine camera.mul_eq_at _ _; assumption, },
end

private lemma cinl_core_eq_some {α β : Type u} [camera α] [camera β] {a : α} {ca : α ⊕ₖ β} :
  (cinl a : α ⊕ₖ β).core = some ca → ∃ ca', ca = cinl ca' ∧ camera.core a = some ca' :=
begin
  intro h,
  cases ca,
  { refine ⟨ca, rfl, _⟩,
    simpa only [core, option.map_eq_some', exists_eq_right] using h, },
  { simpa only [core, option.map_eq_some', and_false, exists_false] using h, },
  { simpa only [core, option.map_eq_some', and_false, exists_false] using h, },
end

private lemma cinr_core_eq_some {α β : Type u} [camera α] [camera β] {a : β} {ca : α ⊕ₖ β} :
  (cinr a : α ⊕ₖ β).core = some ca → ∃ ca', ca = cinr ca' ∧ camera.core a = some ca' :=
begin
  intro h,
  cases ca,
  { simpa only [core, option.map_eq_some', and_false, exists_false] using h, },
  { refine ⟨ca, rfl, _⟩,
    simpa only [core, option.map_eq_some', exists_eq_right] using h, },
  { simpa only [core, option.map_eq_some', and_false, exists_false] using h, },
end

private lemma core_mul_self {α β : Type u} [camera α] [camera β]
  (a : α ⊕ₖ β) {ca : α ⊕ₖ β} : core a = some ca → ca * a = a :=
begin
  intro h,
  cases a,
  { obtain ⟨ca, rfl, hca⟩ := cinl_core_eq_some h,
    exact congr_arg cinl (camera.core_mul_self _ hca), },
  { obtain ⟨ca, rfl, hca⟩ := cinr_core_eq_some h,
    exact congr_arg cinr (camera.core_mul_self _ hca), },
  { rw mul_comm, refl, },
end

private lemma core_core {α β : Type u} [camera α] [camera β]
  (a : α ⊕ₖ β) {ca : α ⊕ₖ β} : core a = some ca → core ca = some ca :=
begin
  intro h,
  cases a,
  { obtain ⟨ca, rfl, hca⟩ := cinl_core_eq_some h,
    simp only [core, option.map_eq_some', exists_eq_right],
    exact camera.core_core _ hca, },
  { obtain ⟨ca, rfl, hca⟩ := cinr_core_eq_some h,
    simp only [core, option.map_eq_some', exists_eq_right],
    exact camera.core_core _ hca, },
  { cases h, exact h, },
end

private lemma core_mono_some {α β : Type u} [camera α] [camera β]
  (a b : α ⊕ₖ β) {ca : α ⊕ₖ β} : core a = some ca → a ≼ b →
    ∃ cb : α ⊕ₖ β, core b = some cb :=
begin
  rintros h ⟨c, hc⟩,
  cases a,
  { obtain ⟨ca, rfl, hca⟩ := cinl_core_eq_some h,
    cases c; cases hc,
    { obtain ⟨d, hd⟩ := camera.core_mono_some a (a * c) hca ⟨c, rfl⟩,
      refine ⟨cinl d, _⟩,
      simp only [core, option.map_eq_some', exists_eq_right],
      exact hd, },
    { exact ⟨invalid, rfl⟩, },
    { exact ⟨invalid, rfl⟩, }, },
  { obtain ⟨ca, rfl, hca⟩ := cinr_core_eq_some h,
    cases c; cases hc,
    { exact ⟨invalid, rfl⟩, },
    { obtain ⟨d, hd⟩ := camera.core_mono_some a (a * c) hca ⟨c, rfl⟩,
      refine ⟨cinr d, _⟩,
      simp only [core, option.map_eq_some', exists_eq_right],
      exact hd, },
    { exact ⟨invalid, rfl⟩, }, },
  { cases hc,
    exact ⟨invalid, rfl⟩, },
end

private lemma core_mono {α β : Type u} [camera α] [camera β]
  (a b : α ⊕ₖ β) {ca : α ⊕ₖ β} : core a = some ca → a ≼ b → core a ≼ core b :=
begin
  rintros h ⟨c, hc⟩,
  cases a,
  { obtain ⟨ca, rfl, hca⟩ := cinl_core_eq_some h,
    cases c; cases hc,
    { obtain ⟨d, hd⟩ := camera.core_mono a (a * c) hca ⟨c, rfl⟩,
      refine ⟨d.map cinl, _⟩,
      simp only [core, option.map_eq_some', exists_eq_right, ← hd],
      cases camera.core a; cases d;
      simp only [option.map_none', option.map_some', none_mul, mul_none, some_mul_some],
      refl, },
    { refine ⟨some invalid, _⟩,
      cases (cinl a).core, refl, cases val; refl, },
    { refine ⟨some invalid, _⟩,
      cases (cinl a).core, refl, cases val; refl, }, },
  { obtain ⟨ca, rfl, hca⟩ := cinr_core_eq_some h,
    cases c; cases hc,
    { refine ⟨some invalid, _⟩,
      cases (cinr a).core, refl, cases val; refl, },
    { obtain ⟨d, hd⟩ := camera.core_mono a (a * c) hca ⟨c, rfl⟩,
      refine ⟨d.map cinr, _⟩,
      simp only [core, option.map_eq_some', exists_eq_right, ← hd],
      cases camera.core a; cases d;
      simp only [option.map_none', option.map_some', none_mul, mul_none, some_mul_some],
      refl, },
    { refine ⟨some invalid, _⟩,
      cases (cinr a).core, refl, cases val; refl, }, },
  { cases hc, exact ⟨some invalid, rfl⟩, },
end

private lemma validn_mul {α β : Type u} [camera α] [camera β] (a b : α ⊕ₖ β) :
  validn (a * b) ≤ validn a :=
begin
  intros n h,
  cases a,
  { cases b,
    exact camera.validn_mul a b n h,
    cases h,
    cases h, },
  { cases b,
    cases h,
    exact camera.validn_mul a b n h,
    cases h, },
  { cases h, },
end

private lemma extend_mul_eq {α β : Type u} [camera α] [camera β] (n : ℕ)
  (a b₁ b₂ : α ⊕ₖ β) (ha : validn a n) (hb : a =[n] b₁ * b₂) :
  a = (extend ha hb).1 * (extend ha hb).2 :=
begin
  cases a,
  { obtain ⟨b, hb'⟩ := cinl_eq_at hb,
    obtain ⟨b₁, b₂, rfl, rfl⟩ := cinl_eq_mul hb'.symm,
    rw [cinl_mul_cinl, cinl_eq_at_cinl] at hb,
    exact congr_arg cinl (camera.extend_mul_eq ha hb), },
  { obtain ⟨b, hb'⟩ := cinr_eq_at hb,
    obtain ⟨b₁, b₂, rfl, rfl⟩ := cinr_eq_mul hb'.symm,
    rw [cinr_mul_cinr, cinr_eq_at_cinr] at hb,
    exact congr_arg cinr (camera.extend_mul_eq ha hb), },
  { cases ha, },
end

private lemma extend_eq_at_left {α β : Type u} [camera α] [camera β] (n : ℕ)
  (a b₁ b₂ : α ⊕ₖ β) (ha : validn a n) (hb : a =[n] b₁ * b₂) :
  (extend ha hb).1 =[n] b₁ :=
begin
  cases a,
  { obtain ⟨b, hb'⟩ := cinl_eq_at hb,
    obtain ⟨b₁, b₂, rfl, rfl⟩ := cinl_eq_mul hb'.symm,
    rw [cinl_mul_cinl, cinl_eq_at_cinl] at hb,
    exact cinl_is_nonexpansive (camera.extend_eq_at_left ha hb), },
  { obtain ⟨b, hb'⟩ := cinr_eq_at hb,
    obtain ⟨b₁, b₂, rfl, rfl⟩ := cinr_eq_mul hb'.symm,
    rw [cinr_mul_cinr, cinr_eq_at_cinr] at hb,
    exact cinr_is_nonexpansive (camera.extend_eq_at_left ha hb), },
  { cases ha, },
end

private lemma extend_eq_at_right {α β : Type u} [camera α] [camera β] (n : ℕ)
  (a b₁ b₂ : α ⊕ₖ β) (ha : validn a n) (hb : a =[n] b₁ * b₂) :
  (extend ha hb).2 =[n] b₂ :=
begin
  cases a,
  { obtain ⟨b, hb'⟩ := cinl_eq_at hb,
    obtain ⟨b₁, b₂, rfl, rfl⟩ := cinl_eq_mul hb'.symm,
    rw [cinl_mul_cinl, cinl_eq_at_cinl] at hb,
    exact cinl_is_nonexpansive (camera.extend_eq_at_right ha hb), },
  { obtain ⟨b, hb'⟩ := cinr_eq_at hb,
    obtain ⟨b₁, b₂, rfl, rfl⟩ := cinr_eq_mul hb'.symm,
    rw [cinr_mul_cinr, cinr_eq_at_cinr] at hb,
    exact cinr_is_nonexpansive (camera.extend_eq_at_right ha hb), },
  { cases ha, },
end

instance camera {α β : Type u} [camera α] [camera β] : camera (α ⊕ₖ β) := {
  validn := ⟨validn, begin
    intros n a b h,
    cases h,
    refine nonexpansive camera.validn _, assumption,
    refine nonexpansive camera.validn _, assumption,
    intros m hmn, refl,
  end⟩,
  core := ⟨core, begin
    intros n a b h,
    cases h,
    { refine option.map_nonexpansive _ cinl_is_nonexpansive _,
      refine nonexpansive camera.core _, assumption, },
    { refine option.map_nonexpansive _ cinr_is_nonexpansive _,
      refine nonexpansive camera.core _, assumption, },
    { refl, },
  end⟩,
  extend := @extend α β _ _,
  mul_is_nonexpansive := mul_is_nonexpansive,
  core_mul_self := core_mul_self,
  core_core := core_core,
  core_mono_some := core_mono_some,
  core_mono := core_mono,
  validn_mul := validn_mul,
  extend_mul_eq := extend_mul_eq,
  extend_eq_at_left := extend_eq_at_left,
  extend_eq_at_right := extend_eq_at_right,
  ..sum_camera.ofe,
  ..sum_camera.comm_semigroup,
}

end sum_camera
