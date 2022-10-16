import algebra.abs
import algebra.group.defs
import order.bounded_order

universe u

def preceq {M : Type u} [has_mul M] (a b : M) : Prop :=
∃ c, a * c = b

infix ` ≼ `:50 := preceq

class bot_comm_semigroup (M : Type u) extends has_bot M, comm_semigroup M :=
(bot_mul (a : M) : ⊥ * a = a)

@[simp] lemma bot_preceq {M : Type u} [bot_comm_semigroup M] (a : M) : ⊥ ≼ a :=
⟨a, bot_comm_semigroup.bot_mul a⟩

@[simp] lemma preceq_trans {M : Type u} [semigroup M] (a b c : M) :
  a ≼ b → b ≼ c → a ≼ c :=
begin
  rintro ⟨d, rfl⟩ ⟨e, rfl⟩,
  refine ⟨d * e, _⟩,
  rw mul_assoc,
end

class has_valid (M : Type u) :=
(carrier : set M)

def valid {M : Type u} [has_valid M] : M → Prop := has_valid.carrier

class resource_algebra (M : Type u) extends bot_comm_semigroup M, has_valid M, has_abs M :=
(core_mul_self (a : M) : valid (|a|) → |a| * a = a)
(core_core (a : M) : valid (|a|) → | |a| | = |a|)
(core_mono (a b : M) : valid (|a|) → a ≼ b → valid (|b|) ∧ |a| ≼ |b|)
(valid_mul (a b : M) : valid (a * b) → valid a)

class unital_resource_algebra (M : Type u) extends has_one M, resource_algebra M :=
(valid_one : valid (1 : M))
(one_mul (a : M) : valid a → 1 * a = a)
(one_core : |(1 : M)| = (1 : M))
