import algebra.ofe.basic

universes u v

/-!
# Complete OFEs
-/

@[ext] structure chain (α : Type u) (eq_at : ℕ → α → α → Prop) :=
(c : ℕ → α)
(prop : ∀ m n, m ≤ n → eq_at m (c m) (c n))

instance chain.fun_like (α : Type u) (eq_at : ℕ → α → α → Prop) :
  fun_like (chain α eq_at) ℕ (λ _, α) := {
  coe := chain.c,
  coe_injective' := λ p q h, by ext1; exact h,
}

class cofe (α : Type u) extends ofe α :=
(lim : chain α eq_at → α)
(complete : ∀ n c, eq_at n (lim c) (c n))

/-!
# Metric spaces of OFEs

OFEs form metric spaces. Complete OFEs directly correspond to complete metric spaces.
We prove the contraction mapping theorem, also known as Banach's fixed point theorem, for
complete OFEs.
-/

noncomputable theory
open_locale classical

def ofe_dist {α : Type u} [ofe α] (a b : α) : ℝ :=
⨅ (n : ℕ), if a =[n] b then (2 ^ n)⁻¹ else 2

lemma ofe_dist_bdd_below {α : Type u} [ofe α] (a b : α) :
  bdd_below (set.range (λ n, if a =[n] b then ((2 : ℝ) ^ n)⁻¹ else 2)) :=
begin
  refine ⟨0, _⟩,
  rintro r ⟨n, h⟩,
  rw ← h,
  dsimp only,
  split_ifs,
  { rw inv_nonneg,
    exact pow_nonneg zero_le_two _, },
  { exact zero_le_two, },
end

lemma ofe_dist_le' {α : Type u} [ofe α] (a b : α) (n : ℕ) :
  ofe_dist a b ≤ if a =[n] b then (2 ^ n)⁻¹ else 2 :=
cinfi_le (ofe_dist_bdd_below a b) _

lemma ofe_dist_le {α : Type u} [ofe α] (a b : α) (n : ℕ) (h : a =[n] b) :
  ofe_dist a b ≤ (2 ^ n)⁻¹ :=
begin
  have := ofe_dist_le' a b n,
  rw if_pos h at this,
  exact this,
end

lemma ofe_dist_le_two {α : Type u} [ofe α] (a b : α) :
  ofe_dist a b ≤ 2 :=
begin
  refine le_trans (ofe_dist_le' a b 0) _,
  split_ifs,
  { norm_num, },
  { refl, },
end

lemma le_ofe_dist' {α : Type u} [ofe α] (a b : α) (r : ℝ)
  (h : ∀ n, r ≤ if a =[n] b then (2 ^ n)⁻¹ else 2) :
  r ≤ ofe_dist a b :=
le_cinfi h

lemma le_ofe_dist {α : Type u} [ofe α] (a b : α) (r : ℝ)
  (h₁ : ∀ n, a =[ n] b → r ≤ (2 ^ n)⁻¹) (h₂ : r ≤ 2) :
  r ≤ ofe_dist a b :=
begin
  refine le_ofe_dist' a b r _,
  intro n,
  split_ifs,
  exact h₁ n h,
  exact h₂,
end

lemma ofe_dist_eq_one {α : Type u} [ofe α] {a b : α} (h : a ≠ b) :
  critical_point h = 0 → ofe_dist a b = 2 :=
begin
  intro hp,
  rw critical_point_eq_zero at hp,
  unfold ofe_dist,
  convert cinfi_const,
  { ext n,
    rw if_neg (hp n), },
  { apply_instance, },
end

lemma ofe_dist_eq_of_ne {α : Type u} [ofe α] {a b : α} (h : a ≠ b) :
  ofe_dist a b = 2 * (2 ^ critical_point h)⁻¹ :=
begin
  have := critical_point_spec h,
  refine le_antisymm _ _,
  { generalize hp : critical_point h = p,
    cases p,
    { rw ofe_dist_eq_one h hp,
      norm_num, },
    { refine le_of_le_of_eq (ofe_dist_le a b p _) _,
      { rw eq_at_iff_lt_critical_point h,
        rw hp,
        exact lt_add_one p, },
      { rw [pow_succ, mul_inv],
        simp only [mul_inv_cancel_left₀, ne.def,
          bit0_eq_zero, one_ne_zero, not_false_iff], }, }, },
  { refine le_ofe_dist a b _ _ _,
    { intros n hn,
      rw eq_at_iff_lt_critical_point h at hn,
      obtain ⟨k, hk⟩ := le_iff_exists_add.mp (nat.succ_le_of_lt hn),
      rw [hk, pow_add, pow_succ, mul_inv, mul_inv, ← mul_assoc, ← mul_assoc],
      simp only [mul_inv_cancel, ne.def, bit0_eq_zero, one_ne_zero,
        not_false_iff, one_mul, mul_le_iff_le_one_right, inv_pos, pow_pos,
        zero_lt_bit0, zero_lt_one],
      rw [inv_le, inv_one],
      refine one_le_pow_of_one_le _ _,
      exact one_le_two,
      exact pow_pos zero_lt_two _,
      exact zero_lt_one, },
    { simp only [mul_le_iff_le_one_right, zero_lt_bit0, zero_lt_one],
      rw [inv_le, inv_one],
      refine one_le_pow_of_one_le _ _,
      exact one_le_two,
      exact pow_pos zero_lt_two _,
      exact zero_lt_one, }, },
end

lemma lt_ofe_dist {α : Type u} [ofe α] (a b : α) (n : ℕ) (h : ¬a =[n] b) :
  (2 ^ n)⁻¹ < ofe_dist a b :=
begin
  rw ofe_dist_eq_of_ne (ne_of_exists_ne ⟨n, h⟩),
  obtain ⟨k, hk⟩ := le_iff_exists_add.mp (critical_point_min' (ne_of_exists_ne ⟨n, h⟩) h),
  generalize_proofs,
  rw hk,
  simp only [pow_add, mul_inv_rev, mul_lt_mul_right,
    inv_pos, pow_pos, zero_lt_bit0, zero_lt_one],
  refine lt_of_le_of_lt _ one_lt_two,
  rw [inv_le, inv_one],
  refine one_le_pow_of_one_le _ _,
  exact one_le_two,
  exact pow_pos zero_lt_two _,
  exact zero_lt_one,
end

lemma ofe_dist_nonneg {α : Type u} [ofe α] (a b : α) :
  0 ≤ ofe_dist a b :=
begin
  refine le_ofe_dist a b 0 _ zero_le_two,
  intros n h,
  rw inv_nonneg,
  exact pow_nonneg zero_le_two _,
end

lemma ofe_dist_le_of_eq_at {α : Type u} [ofe α] {a b c d : α} :
  (∀ n, a =[n] b → c =[n] d) → ofe_dist c d ≤ ofe_dist a b :=
begin
  intro h,
  refine le_ofe_dist _ _ _ _ (ofe_dist_le_two c d),
  intros n hab,
  exact ofe_dist_le c d n (h n hab),
end

lemma ofe_dist_eq_of_eq_at {α : Type u} [ofe α] {a b c d : α} :
  (∀ n, a =[n] b ↔ c =[n] d) → ofe_dist a b = ofe_dist c d :=
begin
  intro h,
  refine le_antisymm _ _,
  { exact ofe_dist_le_of_eq_at (λ n, (h n).mpr), },
  { exact ofe_dist_le_of_eq_at (λ n, (h n).mp), },
end

/-- Ordered families of equivalences induce a metric space.
This is not made an instance, because we don't want to overwrite the metric space
structure on any type. More importantly, we basically only need this structure to
prove the contraction mapping theorem, so the metric space API doesn't really need
to be visible. -/
def ofe.metric_space (α : Type u) [ofe α] : metric_space α := {
  dist := ofe_dist,
  dist_self := begin
    intro a,
    refine le_antisymm _ (ofe_dist_nonneg a a),
    have : ∀ n, ofe_dist a a ≤ (2 ^ n)⁻¹,
    { intro n,
      refine ofe_dist_le a a _ _,
      refl, },
    by_contra' h,
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h one_half_lt_one,
    rw [div_pow, one_pow, one_div] at hn,
    exact not_lt_of_le (this n) hn,
  end,
  dist_comm := begin
    intros x y,
    unfold dist ofe_dist,
    congr' 1,
    ext n,
    rw eq_at_symm_iff,
  end,
  dist_triangle := begin
    intros x y z,
    unfold dist,
    by_contra',
    rw ← lt_sub_iff_add_lt at this,
    obtain ⟨n, hn⟩ := exists_lt_of_cinfi_lt this,
    dsimp only at hn,
    split_ifs at hn with hxy,
    { by_cases hxz : x =[n] z,
      { have := ofe_dist_le x z n hxz,
        have := ofe_dist_nonneg y z,
        linarith, },
      by_cases hyz : y =[n] z,
      { exact hxz (eq_at_trans _ hxy hyz), },
      suffices : ofe_dist x z = ofe_dist y z,
      { rw [this, sub_self, inv_lt_zero] at hn,
        refine not_le_of_lt hn _,
        exact pow_nonneg zero_le_two _, },
      by_cases hz : ∃ m, x =[m] z,
      { obtain ⟨m, hxz'⟩ := hz,
        by_cases h : n ≤ m,
        { cases hxz (eq_at_mono h hxz'), },
        push_neg at h,
        have hxy' := eq_at_mono h.le hxy,
        exact ofe_dist_eq_of_eq_at (eq_at_forall_trans' hxy hxz), },
      { push_neg at hz,
        refine ofe_dist_eq_of_eq_at _,
        intro m,
        split,
        { intro h,
          cases hz m h, },
        { intro h,
          have h₁ := eq_at_mono (min_le_right m n) hxy,
          have h₂ := eq_at_mono (min_le_left m n) h,
          cases hz _ (eq_at_trans _ h₁ h₂), }, }, },
    { have := ofe_dist_le_two x z,
      have := ofe_dist_nonneg y z,
      linarith, },
  end,
  eq_of_dist_eq_zero := begin
    intros a b h,
    rw eq_at_limit,
    intro n,
    by_contra hxy,
    have := lt_ofe_dist a b n hxy,
    unfold dist at h,
    rw h at this,
    refine not_le_of_lt this _,
    rw inv_nonneg,
    exact pow_nonneg zero_le_two _,
  end,
}

local attribute [instance] ofe.metric_space

lemma dist_def (α : Type u) [ofe α] : (dist : α → α → ℝ) = ofe_dist := rfl

lemma ofe_dist_eq {α : Type u} [ofe α] {a b : α} :
  ofe_dist a b = if h : a = b then 0 else 2 * (2 ^ critical_point h)⁻¹ :=
begin
  split_ifs,
  { rw [← dist_def, dist_eq_zero],
    exact h, },
  { rw ofe_dist_eq_of_ne, },
end

def cofe.complete_space (α : Type u) [cofe α] : complete_space α :=
begin
  split,
  intros f hf,
  rw metric.cauchy_iff at hf,
  choose hf₁ s hs₁ hs₂ using hf,
  resetI,
  have hpow : ∀ n, 0 < ((2 : ℝ) ^ n)⁻¹,
  { intro n,
    rw inv_pos,
    exact pow_pos two_pos _, },
  have hf : ∀ n, (⋂ (k : fin (n + 1)), s (2 ^ k.val)⁻¹ (hpow _)) ∈ f,
  { intro n,
    rw filter.Inter_mem,
    intro k,
    exact hs₁ _ _, },
  have hs₃ : ∀ n, (⋂ (k : fin (n + 1)), s (2 ^ k.val)⁻¹ (hpow _)).nonempty,
  { intro n,
    by_contra,
    rw set.not_nonempty_iff_eq_empty at h,
    have h₁ := hf n,
    have h₂ := filter.empty_not_mem f,
    rw h at h₁,
    exact h₂ h₁, },
  choose t ht using hs₃,
  have hts : ∀ m n, m ≤ n → t n ∈ s (2 ^ m)⁻¹ (hpow _),
  { intros m n hmn,
    have := ht n,
    rw set.mem_Inter at this,
    exact this ⟨m, nat.lt_succ_of_le hmn⟩, },
  have hchain : ∀ (m n : ℕ), m ≤ n → t m =[m] t n,
  { intros m n hmn,
    have := hs₂ (2 ^ m)⁻¹ (hpow m) (t n) (hts m n hmn) (t m) (hts m m le_rfl),
    by_contra,
    refine not_le_of_lt this _,
    rw dist_comm,
    exact (lt_ofe_dist _ _ _ h).le, },
  refine ⟨cofe.lim ⟨t, hchain⟩, _⟩,
  rw le_nhds_iff,
  intros u hlu hu,
  rw metric.is_open_iff at hu,
  obtain ⟨ε, hε₁, hε₂⟩ := hu _ hlu,
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε₁ (show (1 / 2 : ℝ) < 1, by linarith),
  refine f.sets_of_superset _ hε₂,
  refine f.sets_of_superset _ _,
  { exact s (2 ^ (n + 1))⁻¹ (hpow _), },
  { exact hs₁ _ _, },
  intros x hx,
  rw metric.mem_ball,
  refine lt_of_le_of_lt _ hn,
  refine le_trans (dist_triangle x (t (n + 1)) (cofe.lim ⟨t, hchain⟩)) _,
  rw [div_pow, one_pow, one_div],
  have : ((2 : ℝ) ^ n)⁻¹ = (2 ^ (n + 1))⁻¹ + (2 ^ (n + 1))⁻¹,
  { have := add_self_div_two ((2 : ℝ) ^ (n + 1))⁻¹,
    rw div_eq_iff at this,
    rw this,
    refine inv_eq_of_mul_eq_one_left _,
    rw mul_assoc,
    rw pow_succ,
    rw inv_mul_eq_one₀,
    exact mul_ne_zero two_ne_zero (pow_ne_zero _ two_ne_zero),
    exact two_ne_zero, },
  rw this,
  refine add_le_add (hs₂ _ _ x hx (t (n + 1)) (hts (n + 1) (n + 1) le_rfl)).le _,
  rw dist_comm,
  exact ofe_dist_le _ _ _ (cofe.complete (n + 1) ⟨t, hchain⟩),
end

local attribute [instance] cofe.complete_space

def contractive_is_contracting_with {α : Type u} [ofe α] {F : Type v}
  [contractive_fun_class F α α] (f : F) : contracting_with (1 / 2) f :=
begin
  split,
  { rw [div_lt_iff, one_mul],
    exact one_lt_two,
    exact zero_lt_two, },
  rw lipschitz_with_iff_dist_le_mul,
  intros x y,
  rw [nnreal.coe_div, nnreal.coe_one, nnreal.coe_two],
  by_cases x = y,
  { rw h,
    simp only [dist_self, mul_zero], },
  rw [dist_def, ofe_dist_eq_of_ne h, ofe_dist_eq],
  split_ifs with hfxy,
  { simp only [one_div, inv_mul_cancel_left₀, ne.def, bit0_eq_zero,
      one_ne_zero, not_false_iff, inv_nonneg, pow_nonneg,
      zero_le_bit0, zero_le_one], },
  have := critical_point_contractive f hfxy,
  obtain ⟨k, hk⟩ := le_iff_exists_add.mp (nat.succ_le_of_lt this),
  rw [hk, pow_add, pow_succ, mul_inv, mul_inv, ← mul_assoc, ← mul_assoc],
  simp only [mul_inv_cancel, ne.def, bit0_eq_zero, one_ne_zero,
    not_false_iff, one_mul, one_div, inv_mul_cancel_left₀,
    mul_le_iff_le_one_right, inv_pos, pow_pos, zero_lt_bit0, zero_lt_one],
  refine inv_le_one _,
  refine one_le_pow_of_one_le one_le_two _,
end

lemma uniform_continuous_of_nonexpansive {α : Type u} [ofe α] {F : Type v}
  [nonexpansive_fun_class F α α] (f : F) : uniform_continuous f :=
begin
  rw metric.uniform_continuous_iff,
  intros ε hε,
  refine ⟨ε, hε, _⟩,
  intros a b ha,
  by_cases f a = f b,
  { rw h,
    simp only [dist_def, ofe_dist_eq, dif_pos],
    exact hε, },
  have := critical_point_nonexpansive f h,
  rw [dist_def, ofe_dist_eq] at ha ⊢,
  rw dif_neg h,
  rw dif_neg (ne_of_apply_ne f h) at ha,
  refine lt_of_le_of_lt _ ha,
  rw [mul_le_mul_left, inv_le_inv],
  refine pow_le_pow _ this,
  exact one_le_two,
  exact pow_pos zero_lt_two _,
  exact pow_pos zero_lt_two _,
  exact zero_lt_two,
end

/-- The unique fixed point of a contractive function
in a type with a complete ordered family of equivalences. -/
def contractive_fixed_point {α : Type u} [cofe α] [nonempty α] {F : Type v}
  [contractive_fun_class F α α] (f : F) : α :=
contracting_with.fixed_point f (contractive_is_contracting_with f)
