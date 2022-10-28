import algebra.camera.basic

universe u

inductive exclusive (α : Type u)
| mk : α → exclusive
| bot : exclusive

namespace exclusive

lemma mk_injective {α : Type u} : function.injective (mk : α → exclusive α) :=
λ a b h, by cases h; refl

inductive eq_at {α : Type u} [ofe α] (n : ℕ) : exclusive α → exclusive α → Prop
| mk (a b : α) : a =[n] b → eq_at (mk a) (mk b)
| bot : eq_at bot bot

instance {α : Type u} [ofe α] : ofe (exclusive α) := {
  eq_at := eq_at,
  eq_at_reflexive := begin
    rintros n (a | a),
    exact eq_at.mk a a (eq_at_refl n a),
    exact eq_at.bot,
  end,
  eq_at_symmetric := begin
    rintros n (a | a) (b | b) (h | h),
    refine eq_at.mk b a _,
    symmetry, assumption,
    exact eq_at.bot,
  end,
  eq_at_transitive := begin
    rintros n (a | a) (b | b) (c | c) (hab | hab) (hbc | hbc),
    refine eq_at.mk a c _,
    transitivity b; assumption,
    exact eq_at.bot,
  end,
  eq_at_mono' := begin
    rintros m n hmn (a | a) (b | b) (h | h),
    exact eq_at.mk a b (eq_at_mono hmn ‹_›),
    exact eq_at.bot,
  end,
  eq_at_limit' := begin
    rintros (a | a) (b | b) h;
    cases h 0,
    refine congr_arg mk _,
    rw eq_at_limit,
    intro n,
    cases h n,
    assumption,
    refl,
  end,
}

instance {α : Type u} : comm_semigroup (exclusive α) := {
  mul := λ a b, bot,
  mul_assoc := λ a b c, rfl,
  mul_comm := λ a b, rfl,
}

def core {α : Type u} : exclusive α → option (exclusive α)
| (mk a) := none
| bot := some bot

instance {α : Type u} [ofe α] : camera (exclusive α) := {
  validn := ⟨λ a, ⟨λ n, a ≠ bot, λ m n hmn h, h⟩, begin
    rintros n a b (h | h) m hmn,
    simp only [ne.def],
    simp only,
  end⟩,
  core := ⟨core, by rintros n a b (h | h); refl⟩,
  extend := λ n a b₁ b₂ h₁ h₂, ⟨b₁, b₂⟩,
  mul_is_nonexpansive := λ n a b h, by refl,
  core_mul_self := λ a ca h, by cases a; cases h; refl,
  core_core := λ a ca h, by cases a; cases h; refl,
  core_mono_some := λ a b ca h₁ h₂, by cases a; cases h₁; cases h₂.some_spec; exact ⟨bot, rfl⟩,
  core_mono := λ a b ca h₁ h₂, by cases a; cases h₁; cases h₂.some_spec; exact ⟨some bot, rfl⟩,
  validn_mul := λ a b n h, by cases h rfl,
  extend_mul_eq := λ n a b₁ b₂ h₁ h₂, by cases a; cases h₂; refl,
  extend_eq_at_left := λ n a b₁ b₂ h₁ h₂, by refl,
  extend_eq_at_right := λ n a b₁ b₂ h₁ h₂, by refl,
  ..exclusive.ofe,
  ..exclusive.comm_semigroup,
}

end exclusive
