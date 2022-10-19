import algebra.abs
import algebra.group.defs
import order.bounded_order

universe u

def incl {M : Type u} [has_mul M] (a b : M) : Prop :=
∃ c, a * c = b

infix ` ≼ `:50 := incl

instance {M : Type u} [has_mul M] : has_mul (with_bot M) :=
⟨λ a, @with_bot.rec_bot_coe _ (λ _, with_bot M) a
    (λ b, @with_bot.rec_bot_coe _ (λ _, with_bot M) ↑b (λ a, ↑(a * b)) a)⟩

@[simp] lemma bot_mul {M : Type u} [has_mul M] (a : with_bot M) : ⊥ * a = a :=
begin
  induction a using with_bot.rec_bot_coe,
  refl,
  refl,
end

@[simp] lemma mul_bot {M : Type u} [has_mul M] (a : with_bot M) : a * ⊥ = a := rfl

lemma mul_coe {M : Type u} [has_mul M] (a b : M) :
(↑(a * b) : with_bot M) = ↑a * ↑b := rfl

instance with_bot.comm_semigroup {M : Type u} [comm_semigroup M] : comm_semigroup (with_bot M) := {
  mul := λ a, @with_bot.rec_bot_coe _ (λ _, with_bot M) a
    (λ b, @with_bot.rec_bot_coe _ (λ _, with_bot M) ↑b (λ a, ↑(a * b)) a),
  mul_assoc := begin
    intros a b c,
    induction a using with_bot.rec_bot_coe,
    { rw [bot_mul, bot_mul], },
    induction b using with_bot.rec_bot_coe,
    { rw [bot_mul, mul_bot], },
    induction c using with_bot.rec_bot_coe,
    { rw [mul_bot, mul_bot], },
    rw [← mul_coe, ← mul_coe, ← mul_coe, ← mul_coe, mul_assoc],
  end,
  mul_comm := begin
    intros a b,
    induction a using with_bot.rec_bot_coe,
    { rw [bot_mul, mul_bot], },
    induction b using with_bot.rec_bot_coe,
    { rw [bot_mul, mul_bot], },
    rw [← mul_coe, ← mul_coe, mul_comm],
  end,
}

@[simp] lemma bot_incl {M : Type u} [comm_semigroup M] (a : with_bot M) : ⊥ ≼ a :=
⟨a, bot_mul a⟩

@[simp] lemma incl_trans {M : Type u} [semigroup M] (a b c : M) :
  a ≼ b → b ≼ c → a ≼ c :=
begin
  rintro ⟨d, rfl⟩ ⟨e, rfl⟩,
  refine ⟨d * e, _⟩,
  rw mul_assoc,
end

class resource_algebra (M : Type u) extends comm_semigroup M :=
(resource_valid : set M)
(core : M → with_bot M)
(core_mul_self (a : M) (ha : core a ≠ ⊥) : ((core a).unbot ha) * a = a)
(core_core (a : M) (ha : core a ≠ ⊥) : core ((core a).unbot ha) = core a)
(core_mono_ne (a b : M) : a ≼ b → core a ≠ ⊥ → core b ≠ ⊥)
(core_mono (a b : M) (ha : core a ≠ ⊥) : a ≼ b → core a ≼ core b)
(resource_valid_mul (a b : M) : resource_valid (a * b) → resource_valid a)

export resource_algebra (resource_valid)

structure frame {M : Type u} [resource_algebra M] (a : M) :=
(val : M)
(prop : resource_valid (val * a))

def resource_algebra.can_update_preserving_frame
  {M : Type u} [resource_algebra M] (a : M) (b : set M) : Prop :=
∀ f : frame a, ∃ f' : frame f.val, f'.val ∈ b

infixr ` ↝ᵣₐ `:25 := resource_algebra.can_update_preserving_frame

lemma can_update_preserving_frame_iff {M : Type u} [resource_algebra M] (a : M) (b : set M) :
  a ↝ᵣₐ b ↔ ∀ f : M, resource_valid (f * a) → ∃ f' ∈ b, resource_valid (f' * f) :=
begin
  split,
  { intros h f hf,
    obtain ⟨f', hf'⟩ := h ⟨f, hf⟩,
    exact ⟨f'.val, hf', f'.prop⟩, },
  { intros h f,
    obtain ⟨f', hf₁, hf₂⟩ := h f.val f.prop,
    exact ⟨⟨f', hf₂⟩, hf₁⟩, },
end
