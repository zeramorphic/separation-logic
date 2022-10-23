import algebra.camera.basic

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
  some a =[n] b → ∃ b', b = some b' :=
begin
  intro h,
  cases b,
  cases h,
  exact ⟨b, rfl⟩,
end

lemma option.eq_at_some {α : Type u} [ofe α] {n : ℕ} {a : option α} {b : α} :
  a =[n] some b → ∃ a', a = some a' :=
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

@[simp] lemma option.some_eq_at_some_mul_some {α : Type u} [camera α]
  {n : ℕ} {a b c : α} : some a =[n] some b * some c ↔ a =[n] b * c :=
by rw [some_mul_some, option.some_eq_at_some]

@[simp] lemma option.some_eq_at_some_mul_none {α : Type u} [camera α]
  {n : ℕ} {a b : α} : some a =[n] some b * none ↔ a =[n] b :=
by rw [mul_none, option.some_eq_at_some]

@[simp] lemma option.some_eq_at_none_mul_some {α : Type u} [camera α]
  {n : ℕ} {a b : α} : some a =[n] none * some b ↔ a =[n] b :=
by rw [none_mul, option.some_eq_at_some]

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

def option.extend {α : Type u} [camera α] (n : ℕ) :
  Π {a b₁ b₂ : option α} (h₁ : ∀ a', a = some a' → ✓[n] a')
    (h₂ : a =[n] (b₁ * b₂)), option α × option α
| (some a) (some b₁) (some b₂) h₁ h₂ :=
    (some (extend (h₁ a rfl) (option.some_eq_at_some_mul_some.mp h₂)).1,
     some (extend (h₁ a rfl) (option.some_eq_at_some_mul_some.mp h₂)).2)
| (some a) (some b₁) none h₁ h₂ := (some a, none)
| (some a) none (some b₂) h₁ h₂ := (none, some a)
| _ _ _ _ _ := (none, none)

private lemma option.camera.mul_is_nonexpansive {α : Type u} [camera α] :
  is_nonexpansive (function.uncurry ((*) : option α → option α → option α)) :=
begin
  rintros n ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨h₁, h₂⟩,
  cases h₁,
  { cases h₂,
    { simp only [function.uncurry_apply_pair, some_mul_some,
        option.some_eq_at_some],
      refine camera.mul_eq_at _ _; assumption, },
    simp only [function.uncurry_apply_pair, mul_none,
      option.some_eq_at_some],
    assumption, },
  { cases h₂,
    { simp only [function.uncurry_apply_pair, none_mul,
        option.some_eq_at_some],
      assumption, },
    { refl, }, },
end

private lemma option.camera.core_mul_self {α : Type u} [camera α]
  (a : option α) {ca : option α} : some (option.elim none (λ a, core a) a) = some ca →
    ca * a = a :=
begin
  intro h,
  rw option.some_inj at h,
  rw ← h,
  cases a,
  { refl, },
  { simp only [option.elim],
    have := camera.core_mul_self a,
    revert this,
    induction core a,
    { intro h, refl, },
    { intro h,
      rw some_mul_some,
      rw h rfl, }, },
end

private lemma option.camera.core_core {α : Type u} [camera α]
  (a : option α) {ca : option α} : some (option.elim none (λ a, core a) a) = some ca →
    some (option.elim none (λ a, core a) ca) = some ca :=
begin
  intro h,
  rw option.some_inj at h ⊢,
  cases a,
  { cases h,
    refl, },
  cases ca,
  { simp only [option.elim] at h,
    simp_rw h,
    refl, },
  simp only [option.elim] at h ⊢,
  exact camera.core_core a h,
end

private lemma option.camera.core_mono_some {α : Type u} [camera α]
  (a b : option α) {ca : option α} : some (option.elim none (λ a, core a) a) = some ca → a ≼ b →
    ∃ cb : option α, some (option.elim none (λ a, core a) b) = some cb :=
begin
  intros h₁ h₂,
  simp_rw exists_eq',
end

private lemma option.camera.core_mono {α : Type u} [camera α]
  (a b : option α) {ca : option α} : some (option.elim none (λ a, core a) a) = some ca →
    a ≼ b → some (option.elim none (λ a, core a) a) ≼ some (option.elim none (λ a, core a) b) :=
begin
  intros h₁ h₁,
  cases a,
  { refine ⟨some (option.elim none (λ a, core a) b), _⟩,
    simp only [option.elim, some_mul_some, none_mul], },
  obtain ⟨c, hc⟩ := h₁,
  rw ← hc,
  cases c,
  { rw mul_none at hc,
    refine ⟨none, _⟩,
    rw [mul_none, mul_none], },
  simp only [option.elim] at h₁,
  cases ca,
  { simp only [option.elim, some_mul_some],
    rw h₁,
    refine ⟨some (core (a * c)), _⟩,
    simp only [some_mul_some, none_mul], },
  obtain ⟨d, hd⟩ := camera.core_mono a (a * c) h₁ ⟨c, rfl⟩,
  refine ⟨some d, _⟩,
  simp only [option.elim, some_mul_some],
  exact hd,
end

private lemma option.camera.extend_mul_eq {α : Type u} [camera α] (n : ℕ)
  (a b₁ b₂ : option α) (ha : ∀ b, a = some b → ✓[n] b) (hb : a =[n] b₁ * b₂) :
  a = (option.extend n ha hb).1 * (option.extend n ha hb).2 :=
begin
  cases a,
  { simp only [option.none_eq_at] at hb,
    cases b₁,
    { rw none_mul at hb,
      cases hb,
      unfold option.extend,
      refl, },
    { cases b₂; cases hb, }, },
  cases b₁,
  { rw none_mul at hb,
    obtain ⟨b₂, rfl⟩ := option.some_eq_at hb,
    unfold option.extend,
    rw none_mul, },
  cases b₂,
  { rw mul_none at hb,
    unfold option.extend,
    rw mul_none, },
  unfold option.extend,
  rw some_mul_some,
  simp only [some_mul_some, option.some_eq_at_some] at hb,
  rw ← camera.extend_mul_eq (ha a rfl) hb,
end

private lemma option.camera.extend_eq_at_left {α : Type u} [camera α] (n : ℕ)
  (a b₁ b₂ : option α) (ha : ∀ b, a = some b → ✓[n] b) (hb : a =[n] b₁ * b₂) :
  (option.extend n ha hb).1 =[n] b₁ :=
begin
  cases b₁,
  { rw none_mul at hb,
    cases b₂,
    { rw option.eq_at_none at hb,
      cases hb,
      refl, },
    obtain ⟨a, rfl⟩ := option.some_eq_at (ofe.eq_at_symmetric n hb),
    refl, },
  cases b₂,
  { rw mul_none at hb,
    obtain ⟨a, rfl⟩ := option.some_eq_at (ofe.eq_at_symmetric n hb),
    exact hb, },
  rw [some_mul_some, eq_at_symm_iff] at hb,
  obtain ⟨a, rfl⟩ := option.some_eq_at hb,
  unfold option.extend,
  rw option.some_eq_at_some,
  exact camera.extend_eq_at_left _ _,
end

private lemma option.camera.extend_eq_at_right {α : Type u} [camera α] (n : ℕ)
  (a b₁ b₂ : option α) (ha : ∀ b, a = some b → ✓[n] b) (hb : a =[n] b₁ * b₂) :
  (option.extend n ha hb).2 =[n] b₂ :=
begin
  cases b₁,
  { rw none_mul at hb,
    cases b₂,
    { rw option.eq_at_none at hb,
      cases hb,
      refl, },
    obtain ⟨a, rfl⟩ := option.some_eq_at (ofe.eq_at_symmetric n hb),
    exact hb, },
  cases b₂,
  { rw mul_none at hb,
    obtain ⟨a, rfl⟩ := option.some_eq_at (ofe.eq_at_symmetric n hb),
    refl, },
  rw [some_mul_some, eq_at_symm_iff] at hb,
  obtain ⟨a, rfl⟩ := option.some_eq_at hb,
  unfold option.extend,
  rw option.some_eq_at_some,
  exact camera.extend_eq_at_right _ _,
end

instance option.camera {α : Type u} [camera α] : camera (option α) := {
  validn := ⟨λ a, ⟨λ n, ∀ b, a = some b → ✓[n] b,
    λ m n hmn h b hb, (camera.validn b).mono hmn (h b hb)⟩,
    begin
      intros n a b h m hmn,
      simp only [option.mem_def, sprop.coe_fn_mk],
      split; rintros ha c rfl,
      { obtain ⟨d, rfl⟩ := option.eq_at_some h,
        rw option.some_eq_at_some at h,
        exact camera.validn_of_eq_at (eq_at_mono hmn h) (ha d rfl), },
      { obtain ⟨d, rfl⟩ := option.some_eq_at h,
        rw option.some_eq_at_some at h,
        exact camera.validn_of_eq_at
          (eq_at_mono hmn (eq_at_symmetric n h)) (ha d rfl), },
    end⟩,
  core := ⟨λ a, some (option.elim none (λ a, core a) a), begin
    intros n a b hab,
    cases hab,
    { simp only [option.elim, option.some_eq_at_some],
      refine nonexpansive core _,
      assumption, },
    { refl, },
  end⟩,
  extend := option.extend,
  mul_is_nonexpansive := option.camera.mul_is_nonexpansive,
  core_mul_self := option.camera.core_mul_self,
  core_core := option.camera.core_core,
  core_mono_some := option.camera.core_mono_some,
  core_mono := option.camera.core_mono,
  validn_mul := begin
    intros a b n h,
    cases a,
    { simp only [is_empty.forall_iff, implies_true_iff, nonexpansive_fun.coe_fn_mk], },
    cases b,
    { simpa only [sprop.coe_fn_mk, forall_eq', mul_none, nonexpansive_fun.coe_fn_mk] using h, },
    simp only [sprop.coe_fn_mk, forall_eq', nonexpansive_fun.coe_fn_mk, some_mul_some] at h ⊢,
    exact camera.validn_mul a b n h,
  end,
  extend_mul_eq := option.camera.extend_mul_eq,
  extend_eq_at_left := option.camera.extend_eq_at_left,
  extend_eq_at_right := option.camera.extend_eq_at_right,
  ..option.ofe,
  ..option.comm_semigroup,
}
