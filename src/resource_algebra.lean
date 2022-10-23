import algebra.group.defs

universe u

def incl {α : Type u} [has_mul α] (a b : α) : Prop :=
∃ c, a * c = b

infix ` ≼ `:50 := incl

instance {α : Type u} [has_mul α] : has_mul (option α) :=
⟨option.lift_or_get (*)⟩

@[simp] lemma none_mul {α : Type u} [has_mul α] (a : option α) : none * a = a :=
by cases a; refl

@[simp] lemma mul_none {α : Type u} [has_mul α] (a : option α) : a * none = a :=
by cases a; refl

@[simp] lemma some_mul_some {α : Type u} [has_mul α] (a b : α) :
some a * some b = some (a * b) := rfl

instance option.comm_semigroup {α : Type u} [comm_semigroup α] : comm_semigroup (option α) := {
  mul_assoc := begin
    intros a b c,
    cases a,
    { rw [none_mul, none_mul], },
    cases b,
    { rw [none_mul, mul_none], },
    cases c,
    { rw [mul_none, mul_none], },
    rw [some_mul_some, some_mul_some, some_mul_some, some_mul_some, mul_assoc],
  end,
  mul_comm := begin
    intros a b,
    cases a,
    { rw [none_mul, mul_none], },
    cases b,
    { rw [none_mul, mul_none], },
    rw [some_mul_some, some_mul_some, mul_comm],
  end,
  ..option.has_mul,
}

@[simp] lemma none_incl {α : Type u} [comm_semigroup α] (a : option α) : none ≼ a :=
⟨a, none_mul a⟩

@[simp, refl] lemma incl_refl {α : Type u} [monoid α] (a : α) : a ≼ a :=
⟨1, mul_one a⟩

@[simp, trans] lemma incl_trans {α : Type u} [semigroup α] (a b c : α) :
  a ≼ b → b ≼ c → a ≼ c :=
begin
  rintro ⟨d, rfl⟩ ⟨e, rfl⟩,
  refine ⟨d * e, _⟩,
  rw mul_assoc,
end

class resource_algebra (α : Type u) extends comm_semigroup α :=
(valid : set α)
(core : α → option α)
(core_mul_self (a : α) {ca : α} : core a = some ca → ca * a = a)
(core_core (a : α) {ca : α} : core a = some ca → core ca = some ca)
(core_mono_some (a b : α) {ca : α} : core a = some ca → a ≼ b → ∃ cb, core b = some cb)
(core_mono (a b : α) {ca : α} : core a = some ca → a ≼ b → core a ≼ core b)
(valid_mul (a b : α) : valid (a * b) → valid a)

prefix `✓ `:40 := resource_algebra.valid

structure frame {α : Type u} [resource_algebra α] (a : α) :=
(val : α)
(prop : ✓ val * a)

def resource_algebra.can_update
  {α : Type u} [resource_algebra α] (a : α) (b : set α) : Prop :=
∀ f : frame a, ∃ f' : frame f.val, f'.val ∈ b

infixr ` ↝ᵣₐ `:25 := resource_algebra.can_update

lemma can_update_iff {α : Type u} [resource_algebra α] (a : α) (b : set α) :
  a ↝ᵣₐ b ↔ ∀ f : α, ✓ f * a → ∃ f' ∈ b, ✓ f' * f :=
begin
  split,
  { intros h f hf,
    obtain ⟨f', hf'⟩ := h ⟨f, hf⟩,
    exact ⟨f'.val, hf', f'.prop⟩, },
  { intros h f,
    obtain ⟨f', hf₁, hf₂⟩ := h f.val f.prop,
    exact ⟨⟨f', hf₂⟩, hf₁⟩, },
end
