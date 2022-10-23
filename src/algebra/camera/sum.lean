import algebra.camera.option

universe u

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

lemma mul_cinl_valid {α β : Type u} [camera α] [camera β] {a : α} {b : α ⊕ₖ β} {n : ℕ} :
  ✓[n] b * cinl a → ∃ b', b = cinl b' :=
begin
  intro h,
  cases b,
  exact ⟨b, rfl⟩,
  cases h,
  cases h,
end

lemma mul_cinr_valid {α β : Type u} [camera α] [camera β] {a : β} {b : α ⊕ₖ β} {n : ℕ} :
  ✓[n] b * cinr a → ∃ b', b = cinr b' :=
begin
  intro h,
  cases b,
  cases h,
  exact ⟨b, rfl⟩,
  cases h,
end

lemma can_update_cinl {α β : Type u} [camera α] [camera β] {a : α} {A : set α} :
  a ↝ A → (cinl a : α ⊕ₖ β) ↝ cinl '' A :=
begin
  rintros h n ⟨c, hc⟩,
  obtain ⟨c, rfl⟩ := mul_cinl_valid hc,
  obtain ⟨f, hf⟩ := h n ⟨c, hc⟩,
  exact ⟨⟨cinl f.val, f.prop⟩, f.val, hf, rfl⟩,
end

lemma can_update_cinr {α β : Type u} [camera α] [camera β] {b : β} {B : set β} :
  b ↝ B → (cinr b : α ⊕ₖ β) ↝ cinr '' B :=
begin
  rintros h n ⟨c, hc⟩,
  obtain ⟨c, rfl⟩ := mul_cinr_valid hc,
  obtain ⟨f, hf⟩ := h n ⟨c, hc⟩,
  exact ⟨⟨cinr f.val, f.prop⟩, f.val, hf, rfl⟩,
end

/-- If `cinl a` has no frame, we can update it to any valid `cinr b`.
TODO: Why does the Iris appendix add the additional `✓ b` assumption? -/
lemma can_update_swap {α β : Type u} [camera α] [camera β] (a : α) (b : β) :
  (∀ n, is_empty (time_frame a n)) → ✓ b → (cinl a : α ⊕ₖ β) ↝ {cinr b} :=
begin
  rintros ha hb n ⟨c, hc⟩,
  obtain ⟨c, rfl⟩ := mul_cinl_valid hc,
  cases (ha n).false ⟨c, hc⟩,
end

end sum_camera
