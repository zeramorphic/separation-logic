import algebra.camera.exclusive
import algebra.camera.option

universes u

@[ext] structure auth (α : Type u) :=
(excl : option (exclusive α))
(frag : α)

namespace auth

notation `● `:75 a:75 := auth.mk (some (exclusive.mk a)) 1
notation `◯ `:75 a:75 := auth.mk none a

instance {α : Type u} [ofe α] : ofe (auth α) := {
  eq_at := λ n a b, a.excl =[n] b.excl ∧ a.frag =[n] b.frag,
  eq_at_reflexive := by intros n a; split; refl,
  eq_at_symmetric := λ n a b h, ⟨eq_at_symmetric n h.1, eq_at_symmetric n h.2⟩,
  eq_at_transitive := begin
    rintros n a b c ⟨hab₁, hab₂⟩ ⟨hbc₁, hbc₂⟩,
    split; transitivity; assumption,
  end,
  eq_at_mono' := λ m n hmn a b h, ⟨eq_at_mono hmn h.1, eq_at_mono hmn h.2⟩,
  eq_at_limit' := begin
    intros x y h,
    ext1; rw eq_at_limit; intros n,
    exact (h n).1, exact (h n).2,
  end,
}

lemma excl_eq_at {α : Type u} [unital_camera α] {n : ℕ} {a b : α} :
  ● a =[n] ● b → a =[n] b :=
λ h, exclusive.mk_eq_at (option.eq_at_of_some_eq_at h.1)

@[simp] lemma excl_eq_at_iff {α : Type u} [unital_camera α] {n : ℕ} {a b : α} :
  ● a =[n] ● b ↔ a =[n] b :=
⟨excl_eq_at, λ h, ⟨option.some_eq_at_iff.mpr (exclusive.mk_eq_at_iff.mpr h), eq_at_refl n 1⟩⟩

lemma frag_eq_at {α : Type u} [ofe α] {n : ℕ} {a b : α} :
  ◯ a =[n] ◯ b → a =[n] b :=
λ h, h.2

@[simp] lemma frag_eq_at_iff {α : Type u} [ofe α] {n : ℕ} {a b : α} :
  ◯ a =[n] ◯ b ↔ a =[n] b :=
⟨λ h, h.2, λ h, ⟨eq_at_refl n _, h⟩⟩

instance {α : Type u} [comm_semigroup α] : comm_semigroup (auth α) := {
  mul := λ a b, ⟨a.excl * b.excl, a.frag * b.frag⟩,
  mul_assoc := by intros; ext1; simp only [mul_assoc],
  mul_comm := begin
    intros, ext1,
    change a.excl * b.excl = b.excl * a.excl, rw mul_comm,
    change a.frag * b.frag = b.frag * a.frag, rw mul_comm,
  end,
}

@[simp] lemma mul_excl {α : Type u} [comm_semigroup α] (a b : auth α) :
  (a * b).excl = a.excl * b.excl := rfl

@[simp] lemma mul_frag {α : Type u} [comm_semigroup α] (a b : auth α) :
  (a * b).frag = a.frag * b.frag := rfl

@[simp] lemma mul_mk {α : Type u} [comm_semigroup α]
  (ax bx : option (exclusive α)) (af bf : α) :
  (⟨ax, af⟩ : auth α) * ⟨bx, bf⟩ = ⟨ax * bx, af * bf⟩ := rfl

inductive validn {α : Type u} [camera α] (n : ℕ) : auth α → Prop
| none {b : α} : ✓[n] b → validn (◯ b)
| mk {a b : α} : b ≼[n] a → ✓[n] a → validn ⟨some (exclusive.mk a), b⟩

private lemma validn_nonexpansive {α : Type u} [camera α] {n : ℕ} {xa ya : option (exclusive α)}
  {xf yf : α} : (⟨xa, xf⟩ : auth α) =[n] ⟨ya, yf⟩ → validn n ⟨xa, xf⟩ → validn n ⟨ya, yf⟩ :=
begin
  intros h h',
  obtain (⟨_, h₁⟩ | ⟨z, _, ⟨c, hc⟩, h₃⟩) := h',
  { cases h.1,
    refine validn.none _,
    refine camera.validn_of_eq_at (frag_eq_at h) _,
    assumption, },
  { obtain ⟨h₁, h₂⟩ := h,
    simp only [option.exists_eq_iff_some_eq, exclusive.exists_eq_iff_mk_eq] at h₁,
    obtain ⟨_, rfl, ⟨b', rfl, h₁⟩⟩ := h₁,
    refine validn.mk ⟨c, _⟩ _,
    simp only at h₂,
    refine eq_at_trans z _ h₁,
    refine eq_at_trans (xf * c) _ hc,
    exact camera.mul_eq_at_left (eq_at_symm h₂),
    exact camera.validn_of_eq_at h₁ h₃, },
end

private lemma excl_validn {α : Type u} [camera α] {n : ℕ} {a : auth α} : validn n a → ✓[n] a.excl :=
begin
  rintro (h | h) a (h | h),
  intro h', cases h',
end

private lemma frag_validn {α : Type u} [camera α] {n : ℕ} {a : auth α} : validn n a → ✓[n] a.frag :=
begin
  rintro (h | h),
  assumption,
  exact camera.validn_incln ‹_› ‹_›,
end

def extend {α : Type u} [unital_camera α] {n : ℕ} {a b₁ b₂ : auth α}
  (h₁ : validn n a) (h₂ : a =[n] b₁ * b₂) : auth α × auth α :=
⟨⟨(camera.extend (excl_validn h₁) h₂.1).1, (camera.extend (frag_validn h₁) h₂.2).1⟩,
  ⟨(camera.extend (excl_validn h₁) h₂.1).2, (camera.extend (frag_validn h₁) h₂.2).2⟩⟩

instance {α : Type u} [unital_camera α] : camera (auth α) := {
  validn := ⟨λ a, ⟨λ n, validn n a, begin
    intros m n hmn h,
    cases h,
    exact validn.none (camera.validn_mono hmn ‹_›),
    exact validn.mk (incln_mono hmn ‹_›) (camera.validn_mono hmn ‹_›),
  end⟩, begin
    rintros n ⟨xa, xf⟩ ⟨ya, yf⟩ h m hmn,
    exact ⟨validn_nonexpansive (eq_at_mono hmn h),
      validn_nonexpansive (eq_at_mono hmn (eq_at_symm h))⟩,
  end⟩,
  core := ⟨λ a, some (◯ |a.frag|), begin
    intros n a b h,
    simp only [option.exists_eq_iff_some_eq, exists_eq_left', frag_eq_at_iff],
    exact abs_is_nonexpansive h.2,
  end⟩,
  extend := @extend _ _,
  mul_is_nonexpansive := λ n a b h, ⟨camera.mul_eq_at h.1.1 h.2.1, camera.mul_eq_at h.1.2 h.2.2⟩,
  core_mul_self := begin
    intros a ca h,
    cases h,
    ext1,
    simp only [mul_excl, none_mul],
    simp only [mul_frag, unital_camera.abs_mul_self],
  end,
  core_core := begin
    intros a ca h,
    cases h,
    simp only [nonexpansive_fun.coe_fn_mk, eq_self_iff_true, true_and, unital_camera.abs_abs],
  end,
  core_mono_some := λ a b ca hca h, by simp only [nonexpansive_fun.coe_fn_mk, exists_eq'],
  core_mono := begin
    rintros a b ca hca ⟨c, rfl⟩,
    simp only [nonexpansive_fun.coe_fn_mk, mul_frag] at hca ⊢,
    obtain ⟨d, hd⟩ := unital_camera.abs_mono a.frag (a.frag * c.frag) ⟨c.frag, rfl⟩,
    refine ⟨some (◯ d), _⟩,
    simp only [some_mul_some],
    ext1, refl,
    simp only [nonexpansive_fun.coe_fn_mk, some_mul_some, mul_frag],
    exact hd,
  end,
  validn_mul := begin
    rintros ⟨ax, af⟩ ⟨bx, bf⟩ n h,
    simp only [nonexpansive_fun.coe_fn_mk, sprop.coe_fn_mk, mul_mk] at h ⊢,
    cases ax,
    { cases bx,
      { obtain (⟨_, h⟩ | _) := h,
        exact validn.none (camera.validn_mul_left h), },
      { obtain (_ | ⟨c, _, ⟨d, hd⟩, hc⟩) := h,
        refine validn.none _,
        exact camera.validn_mul_left (camera.validn_mul_left
          (camera.validn_of_eq_at (eq_at_symm hd) hc)), }, },
    { cases bx,
      { obtain (_ | ⟨c, _, ⟨d, hd⟩, hc⟩) := h,
        refine validn.mk ⟨bf * d, _⟩ hc,
        convert hd using 1,
        rw ← mul_assoc,
        refl, },
      { cases h, }, },
  end,
  extend_mul_eq := begin
    intros n a b₁ b₂ h₁ b₂,
    ext1,
    exact camera.extend_mul_eq _ _,
    exact camera.extend_mul_eq _ _,
  end,
  extend_eq_at_left := begin
    intros n a b₁ b₂ h₁ b₂,
    split,
    exact camera.extend_eq_at_left _ _,
    exact camera.extend_eq_at_left _ _,
  end,
  extend_eq_at_right := begin
    intros n a b₁ b₂ h₁ b₂,
    split,
    exact camera.extend_eq_at_right _ _,
    exact camera.extend_eq_at_right _ _,
  end,
  ..auth.ofe,
  ..auth.comm_semigroup,
}

end auth
