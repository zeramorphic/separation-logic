import category_theory.concrete_category.basic
import category_theory.concrete_category.bundled_hom

import ofe
import resource_algebra

open category_theory

universe u

instance (α : Ofe) [comm_semigroup α] : comm_semigroup (ofe_with_bot.obj α) :=
with_bot.comm_semigroup

class camera (α : Type u) extends ofe α, comm_semigroup α :=
(nonexpansive : nonexpansive (function.uncurry (*) : α × α → α)
  (binary_product_ofe
    { eq_at := eq_at,
      eq_at_equiv := eq_at_equiv,
      eq_at_mono := eq_at_mono,
      eq_at_limit := eq_at_limit, }
    { eq_at := eq_at,
      eq_at_equiv := eq_at_equiv,
      eq_at_mono := eq_at_mono,
      eq_at_limit := eq_at_limit, })
  { eq_at := eq_at,
    eq_at_equiv := eq_at_equiv,
    eq_at_mono := eq_at_mono,
    eq_at_limit := eq_at_limit, })
(valid : ⟨α, { eq_at := eq_at,
  eq_at_equiv := eq_at_equiv,
  eq_at_mono := eq_at_mono,
  eq_at_limit := eq_at_limit, }⟩ →ₙₑ SProp.{u})
(core : α ⟶ ofe_with_bot.obj ⟨α, {
  eq_at := eq_at,
  eq_at_equiv := eq_at_equiv,
  eq_at_mono := eq_at_mono,
  eq_at_limit := eq_at_limit, }⟩)
(core_mul_self (a : α) (ha : core a ≠ ⊥) : ((core a).unbot ha) * a = a)
(core_core (a : α) (ha : core a ≠ ⊥) : core ((core a).unbot ha) = core a)
(core_mono_ne (a b : α) : a ≼ b → core a ≠ ⊥ → core b ≠ ⊥)
(core_mono (a b : α) (ha : core a ≠ ⊥) : a ≼ b → core a ≼ core b)
(valid_mul (a b : α) : valid (a * b) ≤ valid a)
(extend (n : ℕ) (a b₁ b₂ : α) (ha : (valid a).p n) (hb : eq_at n a (b₁ * b₂)) :
  {c : α × α // a = c.1 * c.2 ∧ eq_at n c.1 b₁ ∧ eq_at n c.2 b₂})

def incln {α : Type u} [cam : camera α] (n : ℕ) (a b : α) : Prop :=
∃ c, cam.eq_at n (a * c) b

notation a ` ≼[`:50 n `] ` b:50 := incln n a b

/-- A noncanonical way of turning every camera into a resource algebra. -/
instance camera.resource_algebra (α : Type u) [camera α] : resource_algebra α := {
  resource_valid := {a | ∀ n, (camera.valid a).p n},
  core := camera.core,
  core_mul_self := camera.core_mul_self,
  core_core := camera.core_core,
  core_mono_ne := camera.core_mono_ne,
  core_mono := camera.core_mono,
  resource_valid_mul := λ a b h n, camera.valid_mul a b n n le_rfl (h n),
}

class is_camera_unit {α : Type u} [camera α] (ε : α) : Prop :=
(valid : ∀ n, (camera.valid ε).p n)
(unit_mul : ∀ a, ε * a = a)
(core_eq : camera.core ε = (ε : with_bot α))

@[simp] lemma unit_incl {α : Type u} [camera α] (ε : α) [is_camera_unit ε] (a : α) : ε ≼ a :=
⟨a, is_camera_unit.unit_mul a⟩

lemma core_total_of_exists_unit {α : Type u} [camera α] (ε : α) [is_camera_unit ε] :
  ∀ a : α, camera.core a ≠ ⊥ :=
begin
  intro a,
  refine camera.core_mono_ne ε a (unit_incl ε a) _,
  rw is_camera_unit.core_eq,
  exact with_bot.coe_ne_bot,
end

class unital_camera (α : Type u) extends camera α :=
(unit : α)
(is_unit : is_camera_unit unit)

attribute [instance] unital_camera.is_unit

structure time_frame {α : Type u} [camera α] (a : α) (n : ℕ) :=
(val : α)
(prop : (camera.valid (val * a)).p n)

def camera.can_update_preserving_frame {α : Ofe} [camera α] (a : α) (b : set α) : Prop :=
∀ n, ∀ f : time_frame a n, ∃ f' : time_frame f.val n, f'.val ∈ b

infixr ` ↝ `:25 := camera.can_update_preserving_frame

@[ext] structure camera_hom (α β : Type u) [cα : camera α] [cβ : camera β] :=
(to_fun : α → β)
(nonexpansive : nonexpansive to_fun cα.to_ofe cβ.to_ofe)
(map_mul : ∀ a b, to_fun a * to_fun b = to_fun (a * b))
(map_core : ∀ a, camera.core (to_fun a) = option.map to_fun (camera.core a))
(map_valid : ∀ n a, (camera.valid a).p n → (camera.valid (to_fun a)).p n)

def camera_hom.id {α : Type u} [cα : camera α] : camera_hom α α := {
  to_fun := id,
  nonexpansive := nonexpansive_id cα.to_ofe,
  map_mul := by obviously,
  map_core := by obviously,
  map_valid := by obviously,
}

def camera_hom.comp {α β γ : Type u} [cα : camera α] [cβ : camera β] [cγ : camera γ]
  (g : camera_hom β γ) (f : camera_hom α β) : camera_hom α γ := {
  to_fun := g.to_fun ∘ f.to_fun,
  nonexpansive := nonexpansive_comp g.to_fun f.to_fun cα.to_ofe cβ.to_ofe cγ.to_ofe
    g.nonexpansive f.nonexpansive,
  map_mul := by simp only [types_comp_apply, g.map_mul,
    f.map_mul, eq_self_iff_true, forall_2_true_iff],
  map_core := begin
    intro a,
    simp only [types_comp_apply, g.map_core, f.map_core, option.map_map],
  end,
  map_valid := λ n a h, g.map_valid _ _ (f.map_valid _ _ h),
}

instance camera_hom_fun_like {α β : Type u} [camera α] [camera β] :
  fun_like (camera_hom α β) α (λ _, β) := {
  coe := camera_hom.to_fun,
  coe_injective' := begin intros f g h, ext1, exact h, end,
}

def Camera := bundled camera

instance : has_coe_to_sort Camera Type* := bundled.has_coe_to_sort

instance : bundled_hom camera_hom :=
⟨λ α β [camera α] [camera β], by exactI @camera_hom.to_fun α β _ _,
 λ α [camera α], by exactI @camera_hom.id α _,
 λ α β γ [camera α] [camera β] [camera γ], by exactI @camera_hom.comp α β γ _ _ _,
 λ α β [camera α] [camera β], by exactI @fun_like.coe_injective (camera_hom α β) α (λ _, β) _⟩

attribute [derive [large_category, concrete_category]] Camera

instance Camera.has_forget_to_Ofe : has_forget₂ Camera Ofe := {
  forget₂ := {
    obj := λ α, ⟨α, α.str.to_ofe⟩,
    map := λ α β f, ⟨f, by exactI @camera_hom.nonexpansive α β α.str β.str f⟩,
  },
}

instance coe_Camera_Ofe : has_coe Camera Ofe :=
{ coe := (forget₂ Camera Ofe).obj, }

def UCamera := bundled unital_camera

instance : has_coe_to_sort UCamera Type* := bundled.has_coe_to_sort

instance : bundled_hom.parent_projection @unital_camera.to_camera := ⟨⟩

attribute [derive [large_category, concrete_category]] UCamera

instance has_forget_to_Camera : has_forget₂ UCamera Camera := bundled_hom.forget₂ _ _

instance coe_UCamera_Camera : has_coe UCamera Camera :=
{ coe := (forget₂ UCamera Camera).obj, }
