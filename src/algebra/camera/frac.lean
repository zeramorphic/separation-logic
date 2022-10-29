import algebra.camera.basic

inductive frac
| mk (a : ℚ) : 0 < a → a ≤ 1 → frac
| bot : frac

namespace frac

instance : ofe frac := {
  eq_at := λ _, (=),
  eq_at_reflexive := λ _, eq_equivalence.1,
  eq_at_symmetric := λ _, eq_equivalence.2.1,
  eq_at_transitive := λ _, eq_equivalence.2.2,
  eq_at_mono' := λ n m hmn a b h, h,
  eq_at_limit' := λ a b h, h 0,
}

@[simp] lemma eq_at_iff (n : ℕ) (a b : frac) : a =[n] b ↔ a = b := iff.rfl

def mul : frac → frac → frac
| (mk a ha _) (mk b hb _) :=
  if h : a + b ≤ 1 then mk (a + b) (add_pos ha hb) h else bot
| _ _ := bot

instance : comm_semigroup frac := {
  mul := mul,
  mul_assoc := begin
    rintros (⟨a, ha₁, ha₂⟩ | _) (⟨b, hb₁, hb₂⟩ | _) (⟨c, hc₁, hc₂⟩ | _);
    try { refl },
    { simp only [mul],
      split_ifs with h₁ h₂ h₂,
      simp only [mul],
      split_ifs with h₃ h₄ h₄,
      rw add_assoc,
      rw add_assoc at h₃, cases h₄ h₃,
      rw add_assoc at h₃, cases h₃ h₄,
      refl,
      simp only [mul], rw dif_neg, linarith,
      simp only [mul], rw dif_neg, linarith,
      refl, },
    { simp only [mul], split_ifs; refl, },
  end,
  mul_comm := begin
    rintros (⟨a, ha₁, ha₂⟩ | _) (⟨b, hb₁, hb₂⟩ | _); try { refl },
    simp only [has_mul.mul, mul],
    split_ifs with h₁ h₂ h₂,
    rw add_comm,
    rw add_comm at h₁, cases h₂ h₁,
    rw add_comm at h₁, cases h₁ h₂,
    refl,
  end,
}

lemma mk_mul_mk {a b : ℚ} (ha₁ : 0 < a) (ha₂ : a ≤ 1) (hb₁ : 0 < b) (hb₂ : b ≤ 1) :
  (mk a ha₁ ha₂) * (mk b hb₁ hb₂) =
    if h : a + b ≤ 1 then mk (a + b) (add_pos ha₁ hb₁) h else bot := rfl

def core : frac → option frac
| (mk a _ _) := none
| bot := some bot

instance : camera frac := {
  validn := ⟨λ a, sprop.const (a ≠ bot),
    by intros n a b h m hmn; rw frac.eq_at_iff at h; rw h⟩,
  core := ⟨core, λ n a b h, by cases h; refl⟩,
  extend := λ n a b₁ b₂ h₁ h₂, ⟨b₁, b₂⟩,
  mul_is_nonexpansive := begin
    rintros n a b ⟨h₁, h₂⟩,
    rw eq_at_iff at h₁ h₂ ⊢,
    rw prod.ext h₁ h₂,
  end,
  core_mul_self := λ a ca h, by cases a; cases h; refl,
  core_core := λ a ca h, by cases a; cases h; refl,
  core_mono_some := λ a b ca h₁ h₂, by cases a; cases h₁; cases h₂.some_spec; exact ⟨bot, rfl⟩,
  core_mono := λ a b ca h₁ h₂, by cases a; cases h₁; cases h₂.some_spec; exact ⟨some bot, rfl⟩,
  validn_mul := λ a b n h, by cases a; trivial,
  extend_mul_eq := λ n a b₁ b₂ h₁ h₂, h₂,
  extend_eq_at_left := λ n a b₁ b₂ h₁ h₂, by refl,
  extend_eq_at_right := λ n a b₁ b₂ h₁ h₂, by refl,
  ..frac.ofe,
  ..frac.comm_semigroup,
}

end frac
