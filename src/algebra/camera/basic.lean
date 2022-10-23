import algebra.ofe.option
import algebra.ofe.prod
import algebra.ofe.sprop
import algebra.camera.resource_algebra

universe u

set_option old_structure_cmd true

class camera (α : Type u) extends ofe α, comm_semigroup α : Type u :=
(validn : α →ₙₑ sprop.{u})
(core : α →ₙₑ option α)
(extend {n : ℕ} {a b₁ b₂ : α} (ha : validn a n) (hb : eq_at n a (b₁ * b₂)) : α × α)
(mul_is_nonexpansive : is_nonexpansive (function.uncurry (*) : α × α → α))
(core_mul_self (a : α) ⦃ca : α⦄ : core a = some ca → ca * a = a)
(core_core (a : α) {ca : α} : core a = some ca → core ca = some ca)
(core_mono_some (a b : α) {ca : α} : core a = some ca → a ≼ b → ∃ cb, core b = some cb)
(core_mono (a b : α) {ca : α} : core a = some ca → a ≼ b → core a ≼ core b)
(validn_mul (a b : α) : validn (a * b) ≤ validn a)
(extend_mul_eq {n : ℕ} {a b₁ b₂ : α} (ha : validn a n) (hb : eq_at n a (b₁ * b₂)) :
  a = (extend ha hb).1 * (extend ha hb).2)
(extend_eq_at_left {n : ℕ} {a b₁ b₂ : α} (ha : validn a n) (hb : eq_at n a (b₁ * b₂)) :
  (extend ha hb).1 =[n] b₁)
(extend_eq_at_right {n : ℕ} {a b₁ b₂ : α} (ha : validn a n) (hb : eq_at n a (b₁ * b₂)) :
  (extend ha hb).2 =[n] b₂)

export camera (core extend)

lemma camera.mul_eq_at {α : Type u} [camera α] {a b c d : α} {n : ℕ} :
  a =[n] b → c =[n] d → a * c =[n] b * d :=
camera.mul_is_nonexpansive.uncurry_apply_eq_at

@[simp] lemma camera.core_mul_core {α : Type u} [camera α] {a : α} :
  core a * core a = core a :=
begin
  by_cases ∃ ca, core a = some ca,
  swap, { rw ← option.is_some_iff_exists at h, cases core a, refl,
    simpa only [option.is_some_some, coe_sort_tt, not_true] using h, },
  obtain ⟨ca, hca⟩ := h,
  have := camera.core_mul_self ca (camera.core_core a hca),
  rw [hca, some_mul_some, this],
end

def incln {α : Type u} [camera α] (n : ℕ) (a b : α) : Prop :=
∃ c, a * c =[n] b

notation `✓[`:40 n `] ` a:40 := camera.validn a n
notation a ` ≼[`:50 n `] ` b:50 := incln n a b

lemma camera.validn_mul_left {α : Type u} [camera α] {n : ℕ} {a b : α} :
  ✓[n] a * b → ✓[n] a := camera.validn_mul a b n

lemma camera.validn_mul_right {α : Type u} [camera α] {n : ℕ} {a b : α} :
  ✓[n] a * b → ✓[n] b := by rw mul_comm; exact camera.validn_mul b a n

lemma camera.validn_of_eq_at {α : Type u} [camera α] {n : ℕ} {a b : α} :
  a =[n] b → ✓[n] a → ✓[n] b :=
begin
  intros hab ha,
  have : camera.validn a =[n] camera.validn b := nonexpansive camera.validn hab,
  rwa this n le_rfl at ha,
end

/-- A way of turning every camera into a resource algebra. -/
instance camera.resource_algebra (α : Type u) [camera α] : resource_algebra α := {
  valid := {a | ∀ n, ✓[n] a},
  core := camera.core,
  core_mul_self := camera.core_mul_self,
  core_core := camera.core_core,
  core_mono_some := camera.core_mono_some,
  core_mono := camera.core_mono,
  valid_mul := λ a b h n, camera.validn_mul a b n (h n),
}

class unital_camera (α : Type u) extends camera α, comm_monoid α :=
(one_valid : ∀ n, ✓[n] (1 : α))
(core_one_eq : camera.core 1 = some (1 : α))

@[simp] lemma one_incl {α : Type u} [unital_camera α] (a : α) : 1 ≼ a :=
⟨a, one_mul a⟩

@[simp, refl] lemma incln_refl {α : Type u} [unital_camera α] (n : ℕ) (a : α) : a ≼[n] a :=
⟨1, by rw mul_one⟩

lemma incln_of_eq_at {α : Type u} [unital_camera α] {n : ℕ} {a b : α} :
  a =[n] b → a ≼[n] b :=
λ h, ⟨1, by rw mul_one; exact h⟩

lemma core_total_of_unital {α : Type u} [unital_camera α] :
  ∀ a : α, ∃ ca, camera.core a = some ca :=
λ a, camera.core_mono_some 1 a unital_camera.core_one_eq (one_incl a)

structure time_frame {α : Type u} [camera α] (a : α) (n : ℕ) :=
(val : α)
(prop : ✓[n] val * a)

def camera.can_update {α : Type u} [camera α] (a : α) (b : set α) : Prop :=
∀ n, ∀ f : time_frame a n, ∃ f' : time_frame f.val n, f'.val ∈ b

infixr ` ↝ `:30 := camera.can_update

@[ext] structure camera_hom (α β : Type u) [camera α] [camera β] :=
(to_fun : α → β)
(is_nonexpansive' : is_nonexpansive to_fun)
(map_mul' : ∀ a b, to_fun a * to_fun b = to_fun (a * b))
(map_core': ∀ a, camera.core (to_fun a) = option.map to_fun (camera.core a))
(map_valid' : ∀ n (a : α), ✓[n] a → ✓[n] to_fun a)

infixr ` →ₖₕ `:25 := camera_hom

instance camera_hom_fun_like {α β : Type u} [camera α] [camera β] :
  fun_like (α →ₖₕ β) α (λ _, β) := {
  coe := camera_hom.to_fun,
  coe_injective' := begin intros f g h, ext1, exact h, end,
}

instance camera_hom.nonexpansive_fun_class (α β : Type u) [camera α] [camera β] :
  nonexpansive_fun_class (camera_hom α β) α β := {
  is_nonexpansive := camera_hom.is_nonexpansive',
}

instance camera_hom.mul_hom_class (α β : Type u) [camera α] [camera β] :
  mul_hom_class (α →ₖₕ β) α β := {
  coe := camera_hom.to_fun,
  coe_injective' := begin intros f g h, ext1, exact h, end,
  map_mul := λ f x y, (f.map_mul' x y).symm,
}

def camera_hom.id {α : Type u} [cα : camera α] : camera_hom α α := {
  to_fun := id,
  is_nonexpansive' := is_nonexpansive_id,
  map_mul' := by obviously,
  map_core' := by obviously,
  map_valid' := by obviously,
}

def camera_hom.comp {α β γ : Type u} [camera α] [camera β] [camera γ]
  (g : β →ₖₕ γ) (f : α →ₖₕ β) : α →ₖₕ γ := {
  to_fun := g.to_fun ∘ f.to_fun,
  is_nonexpansive' := is_nonexpansive_comp g.to_fun f.to_fun
    g.is_nonexpansive' f.is_nonexpansive',
  map_mul' := by simp only [g.map_mul', f.map_mul', eq_self_iff_true, forall_2_true_iff],
  map_core' := by intro; simp only [g.map_core', f.map_core', option.map_map],
  map_valid' := λ n a h, g.map_valid' _ _ (f.map_valid' _ _ h),
}

lemma camera_hom.map_incln {α β : Type u} [camera α] [camera β] {a b : α} {n : ℕ} {f : α →ₖₕ β} :
  a ≼[n] b → f a ≼[n] f b :=
begin
  rintro ⟨c, hc⟩,
  refine ⟨f c, _⟩,
  rw ← map_mul,
  exact nonexpansive f hc,
end
