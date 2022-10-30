import algebra.ofe.pi

/-!
# Logic of bunched implications
-/

universe u

/--
Contains the logical connectives for bundled implications.
-/
class bi_struct (ℙ : Type u) :=
(entails : ℙ → ℙ → Prop)
(empty : ℙ)
(pure : Prop → ℙ)
(and : ℙ → ℙ → ℙ)
(or : ℙ → ℙ → ℙ)
(implies : ℙ → ℙ → ℙ)
(for_all (A : Type u) : (A → ℙ) → ℙ)
(there_exists (A : Type u) : (A → ℙ) → ℙ)
(sep : ℙ → ℙ → ℙ)
(wand : ℙ → ℙ → ℙ)
(persistently : ℙ → ℙ)
(later : ℙ → ℙ)

infixr ` ⊢ `:26 := bi_struct.entails
notation `⌜`:1 p:200 `⌝` := bi_struct.pure p
infixr ` ⋀ `:35 := bi_struct.and
infixr ` ⋁ `:30 := bi_struct.or
infixr ` => `:28 := bi_struct.implies
notation `∀'` binders `, ` r:(scoped f, bi_struct.for_all _ f) := r
notation `∃'` binders `, ` r:(scoped f, bi_struct.there_exists _ f) := r
infixl ` ∗ `:80 := bi_struct.sep
infixr ` -∗ `:90 := bi_struct.wand
prefix `▷ `:100 := bi_struct.later

export bi_struct (persistently)

def bi.empty {ℙ : Type u} [bi_struct ℙ] : ℙ := bi_struct.empty
def bi.true {ℙ : Type u} [bi_struct ℙ] : ℙ := ⌜true⌝
def bi.false {ℙ : Type u} [bi_struct ℙ] : ℙ := ⌜false⌝

/-- Laws for `⊢`. -/
class bi_entails (ℙ : Type u) [bi_struct ℙ] :=
(entails_preorder : is_preorder ℙ (⊢))
(propext {P Q : ℙ} : P ⊢ Q → Q ⊢ P → P = Q)

-- TODO: Is `bi_mixin_pure_ne` required given Lean's `propext`?

/-- Nonexpansivity laws. -/
class bi_nonexpansive (ℙ : Type u) [ofe ℙ] [bi_struct ℙ] :=
(and_nonexpansive : is_nonexpansive (function.uncurry ((⋀) : ℙ → ℙ → ℙ)))
(or_nonexpansive : is_nonexpansive (function.uncurry ((⋁) : ℙ → ℙ → ℙ)))
(implies_nonexpansive : is_nonexpansive (function.uncurry ((=>) : ℙ → ℙ → ℙ)))
(forall_nonexpansive (A : Type u) : is_nonexpansive (bi_struct.for_all A : (A → ℙ) → ℙ))
(exists_nonexpansive (A : Type u) : is_nonexpansive (bi_struct.there_exists A : (A → ℙ) → ℙ))
(sep_nonexpansive : is_nonexpansive (function.uncurry ((∗) : ℙ → ℙ → ℙ)))
(wand_nonexpansive : is_nonexpansive (function.uncurry ((-∗) : ℙ → ℙ → ℙ)))
(persistently_nonexpansive : is_nonexpansive (bi_struct.persistently : ℙ → ℙ))

/-- Laws for higher-order logic. -/
class bi_hol (ℙ : Type u) [bi_struct ℙ] :=
(pure_intro {p : Prop} {P : ℙ} : p → P ⊢ ⌜p⌝)
(pure_elim {p : Prop} {P : ℙ} : (p → bi.true ⊢ P) → ⌜p⌝ ⊢ P)
(and_intro {P Q R : ℙ} : P ⊢ Q → P ⊢ R → P ⊢ Q ⋀ R)
(and_elim_left {P Q : ℙ} : P ⋀ Q ⊢ P)
(and_elim_right {P Q : ℙ} : P ⋀ Q ⊢ Q)
(or_intro_left {P Q : ℙ} : P ⊢ P ⋁ Q)
(or_intro_right {P Q : ℙ} : Q ⊢ P ⋁ Q)
(or_elim {P Q R : ℙ} : P ⊢ R → Q ⊢ R → P ⋁ Q ⊢ R)
(implies_intro {P Q R : ℙ} : P ⋀ Q ⊢ R → P ⊢ Q => R)
(implies_elim {P Q R : ℙ} : P ⊢ Q => R → P ⋀ Q ⊢ R)
(forall_intro {A : Type u} {P : ℙ} {Q : A → ℙ} : (∀ a, P ⊢ Q a) → P ⊢ ∀' a, Q a)
(forall_elim {A : Type u} {Φ : A → ℙ} {a : A} : (∀' a, Φ a) ⊢ Φ a)
(exists_intro {A : Type u} {Φ : A → ℙ} {a : A} : Φ a ⊢ ∃' a, Φ a)
(exists_elim {A : Type u} {P : ℙ} {Q : A → ℙ} : (∀ a, Q a ⊢ P) → (∃' a, Q a) ⊢ P)

/-- Laws for separating conjunction. -/
class bi_connectives (ℙ : Type u) [bi_struct ℙ] :=
(sep_mono {P Q R S : ℙ} : P ⊢ Q → R ⊢ S → P ∗ R ⊢ Q ∗ S)
(empty_sep {P : ℙ} : P ⊢ bi.empty ∗ P)
(sep_empty {P : ℙ} : P ⊢ P ∗ bi.empty)
(sep_comm {P Q : ℙ} : P ∗ Q ⊢ Q ∗ P)
(sep_assoc {P Q R : ℙ} : P ∗ Q ∗ R ⊢ P ∗ (Q ∗ R))
(wand_intro {P Q R : ℙ} : P ∗ Q ⊢ R → P ⊢ Q -∗ R)
(wand_elim {P Q R : ℙ} : P ⊢ Q -∗ R → P ∗ Q ⊢ R)

class bi_persistently (ℙ : Type u) [bi_struct ℙ] :=
(persistently_mono {P Q : ℙ} : P ⊢ Q → persistently P ⊢ persistently Q)
(persistently_persistently {P : ℙ} : persistently P ⊢ persistently (persistently P))
(persistently_empty : (bi.empty : ℙ) ⊢ persistently bi.empty)
(persistently_and {P Q : ℙ} : persistently P ⋀ persistently Q ⊢ persistently (P ⋀ Q))
(persistently_exists {A : Type u} {Φ : A → ℙ} :
  persistently (∃' a, Φ a) ⊢ ∃' a, persistently (Φ a))
(persistently_sep {P Q : ℙ} : persistently (P ∗ Q) ⊢ persistently P)
(persistently_and_sep_elim {P Q : ℙ} : persistently (P ⋀ Q) ⊢ P ∗ Q)

class bi_later (ℙ : Type u) [ofe ℙ] [bi_struct ℙ] :=
(later_nonexpansive : is_nonexpansive (bi_struct.later : ℙ → ℙ))
(later_mono {P Q : ℙ} : P ⊢ Q → ▷ P ⊢ ▷ Q)
(later_intro {P : ℙ} : P ⊢ ▷ P)
(forall_later {A : Type u} {Φ : A → ℙ} : (∀' a, ▷ Φ a) ⊢ ▷ ∀' a, Φ a)
(later_exists_false {A : Type u} {Φ : A → ℙ} : (▷ ∃' a, Φ a) ⊢ ▷ bi.false ⋁ (∃' a, ▷ Φ a))
(later_sep {P Q : ℙ} : ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q)
(later_sep' {P Q : ℙ} : ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q))
(persistently_later {P : ℙ} : ▷ persistently P ⊢ persistently ▷ P)
(later_persistently {P : ℙ} : persistently ▷ P ⊢ ▷ persistently P)
(later_false_em {P : ℙ} : ▷ P ⊢ ▷ bi.false ⋁ (▷ bi.false => P))

class bi (ℙ : Type u) [ofe ℙ] [bi_struct ℙ] extends
  bi_entails ℙ, bi_nonexpansive ℙ, bi_hol ℙ, bi_connectives ℙ, bi_persistently ℙ, bi_later ℙ

namespace bi

variables {ℙ : Type u} [ofe ℙ] [bi_struct ℙ] [bi ℙ]
variables {n : ℕ} {p : Prop} {A : Type u} {P Q R S : ℙ} {Φ Ψ : A → ℙ}

/-!
# Laws for `⊢`
-/

@[refl] lemma entails_refl (P : ℙ) : P ⊢ P := bi_entails.entails_preorder.1.refl P
lemma entails_rfl {P : ℙ} : P ⊢ P := entails_refl P
/-- The cut law. -/
@[trans] lemma entails_trans : P ⊢ Q → Q ⊢ R → P ⊢ R := bi_entails.entails_preorder.2.trans P Q R
lemma propext : P ⊢ Q → Q ⊢ P → P = Q := bi_entails.propext

lemma propext_iff : P = Q ↔ (P ⊢ Q) ∧ (Q ⊢ P) :=
begin
  split,
  { rintro rfl, split; refl, },
  { intro h, exact propext h.1 h.2, },
end

/-!
# Nonexpansivity laws
-/

lemma and_eq_at : P =[n] R → Q =[n] S → (P ⋀ Q) =[n] (R ⋀ S) :=
begin
  intros h₁ h₂,
  have := bi_nonexpansive.and_nonexpansive,
  exact @this n ⟨P, Q⟩ ⟨R, S⟩ ⟨h₁, h₂⟩,
  apply_instance,
end

lemma or_eq_at : P =[n] R → Q =[n] S → (P ⋁ Q) =[n] (R ⋁ S) :=
begin
  intros h₁ h₂,
  have := bi_nonexpansive.or_nonexpansive,
  exact @this n ⟨P, Q⟩ ⟨R, S⟩ ⟨h₁, h₂⟩,
  apply_instance,
end

lemma implies_eq_at : P =[n] R → Q =[n] S → (P => Q) =[n] (R => S) :=
begin
  intros h₁ h₂,
  have := bi_nonexpansive.implies_nonexpansive,
  exact @this n ⟨P, Q⟩ ⟨R, S⟩ ⟨h₁, h₂⟩,
  apply_instance,
end

lemma forall_eq_at : (∀ a, Φ a =[n] Ψ a) → (∀' a, Φ a) =[n] (∀' a, Ψ a) :=
λ h, bi_nonexpansive.forall_nonexpansive A h

lemma exists_eq_at : (∀ a, Φ a =[n] Ψ a) → (∃' a, Φ a) =[n] (∃' a, Ψ a) :=
λ h, bi_nonexpansive.exists_nonexpansive A h

lemma sep_eq_at : P =[n] R → Q =[n] S → (P ∗ Q) =[n] (R ∗ S) :=
begin
  intros h₁ h₂,
  have := bi_nonexpansive.sep_nonexpansive,
  exact @this n ⟨P, Q⟩ ⟨R, S⟩ ⟨h₁, h₂⟩,
  apply_instance,
end

lemma wand_eq_at : P =[n] R → Q =[n] S → (P -∗ Q) =[n] (R -∗ S) :=
begin
  intros h₁ h₂,
  have := bi_nonexpansive.wand_nonexpansive,
  exact @this n ⟨P, Q⟩ ⟨R, S⟩ ⟨h₁, h₂⟩,
  apply_instance,
end

lemma persistently_eq_at : P =[n] Q → persistently P =[n] persistently Q :=
λ h, bi_nonexpansive.persistently_nonexpansive h

/-!
# Higher order logic
We show that `bi` induces a Heyting algebra.
-/

lemma pure_intro : p → P ⊢ ⌜p⌝ := bi_hol.pure_intro
lemma pure_elim : (p → true ⊢ P) → ⌜p⌝ ⊢ P := bi_hol.pure_elim
lemma entails_true : P ⊢ true := pure_intro trivial
lemma false_entails : false ⊢ P := pure_elim false.elim

/-! ## Basic logical laws -/

lemma and_intro : P ⊢ Q → P ⊢ R → P ⊢ Q ⋀ R := bi_hol.and_intro
lemma and_elim_left : P ⋀ Q ⊢ P := bi_hol.and_elim_left
lemma and_elim_right : P ⋀ Q ⊢ Q := bi_hol.and_elim_right

lemma or_intro_left : P ⊢ P ⋁ Q := bi_hol.or_intro_left
lemma or_intro_right : Q ⊢ P ⋁ Q := bi_hol.or_intro_right
lemma or_elim : P ⊢ R → Q ⊢ R → P ⋁ Q ⊢ R := bi_hol.or_elim

lemma implies_intro : P ⋀ Q ⊢ R → P ⊢ Q => R := bi_hol.implies_intro
lemma implies_elim : P ⊢ Q => R → P ⋀ Q ⊢ R := bi_hol.implies_elim
lemma implies_iff : P ⊢ Q => R ↔ P ⋀ Q ⊢ R := ⟨implies_elim, implies_intro⟩

lemma forall_intro : (∀ a, P ⊢ Φ a) → P ⊢ ∀' a, Φ a := bi_hol.forall_intro
lemma forall_elim (Φ : A → ℙ) (a : A) : (∀' a, Φ a) ⊢ Φ a := bi_hol.forall_elim

lemma exists_intro (Φ : A → ℙ) (a : A) : Φ a ⊢ ∃' a, Φ a := bi_hol.exists_intro
lemma exists_elim : (∀ a, Φ a ⊢ P) → (∃' a, Φ a) ⊢ P := bi_hol.exists_elim

/-!
## Heyting algebra

We show `ℙ` forms a Heyting algebra and a complete lattice.
We can deduce many logical laws from these typeclasses.
-/

instance : lattice ℙ := {
  sup := (⋁),
  inf := (⋀),
  le := (⊢),
  le_refl := entails_refl,
  le_trans := λ _ _ _, entails_trans,
  le_antisymm := λ _ _, propext,
  le_sup_left := λ _ _, or_intro_left,
  le_sup_right := λ _ _, or_intro_right,
  sup_le := λ _ _ _, or_elim,
  inf_le_left := λ _ _, and_elim_left,
  inf_le_right := λ _ _, and_elim_right,
  le_inf := λ _ _ _, and_intro,
}

instance : heyting_algebra ℙ := {
  top := true,
  himp := (=>),
  le_top := λ _, entails_true,
  le_himp_iff := λ _ _ _, implies_iff,
  bot := false,
  compl := λ P, P => false,
  bot_le := λ _, false_entails,
  himp_bot := λ _, rfl,
  ..bi.lattice
}

instance : complete_lattice ℙ := {
  Sup := λ S, ∃' P : S, P,
  le_Sup := λ S P hP, exists_intro (λ p : S, (p : ℙ)) (⟨P, hP⟩ : S),
  Sup_le := λ S P h, exists_elim (λ Q, h Q Q.prop),
  Inf := λ S, ∀' P : S, P,
  Inf_le := λ S P hP, forall_elim (λ p : S, (p : ℙ)) (⟨P, hP⟩ : S),
  le_Inf := λ S P h, forall_intro (λ Q, h Q Q.prop),
  ..bi.heyting_algebra
}

instance : distrib_lattice ℙ := generalized_heyting_algebra.to_distrib_lattice

lemma and_or_distrib_left : (P ⋀ (Q ⋁ R)) = (P ⋀ Q ⋁ P ⋀ R) := inf_sup_left
lemma and_or_distrib_right : ((P ⋁ Q) ⋀ R) = (P ⋀ R ⋁ Q ⋀ R) := inf_sup_right
lemma or_and_distrib_left : (P ⋁ (Q ⋀ R)) = ((P ⋁ Q) ⋀ (P ⋁ R)) := sup_inf_left
lemma or_and_distrib_right : ((P ⋀ Q) ⋁ R) = ((P ⋁ R) ⋀ (Q ⋁ R)) := sup_inf_right

/-!
## Bunched implication connectives

We prove facts about separating conjunction and magic wand.
-/

lemma sep_mono : P ⊢ Q → R ⊢ S → P ∗ R ⊢ Q ∗ S := bi_connectives.sep_mono
lemma empty_sep : P ⊢ empty ∗ P := bi_connectives.empty_sep
lemma sep_empty : P ⊢ P ∗ empty := bi_connectives.sep_empty
lemma sep_comm : P ∗ Q = Q ∗ P := propext bi_connectives.sep_comm bi_connectives.sep_comm
lemma sep_assoc : P ∗ Q ∗ R = P ∗ (Q ∗ R) :=
begin
  refine propext bi_connectives.sep_assoc _,
  rw sep_comm,
  refine entails_trans bi_connectives.sep_assoc _,
  rw sep_comm,
  refine entails_trans bi_connectives.sep_assoc _,
  rw sep_comm,
end
lemma entails_wand : (P ⊢ Q -∗ R) ↔ (P ∗ Q ⊢ R) :=
⟨bi_connectives.wand_elim, bi_connectives.wand_intro⟩

/-!
## Persistently
-/

lemma persistently_mono : P ⊢ Q → persistently P ⊢ persistently Q :=
bi_persistently.persistently_mono

lemma persistently_persistently : persistently P ⊢ persistently (persistently P) :=
bi_persistently.persistently_persistently

lemma persistently_empty : (empty : ℙ) ⊢ persistently empty :=
bi_persistently.persistently_empty

lemma persistently_and : persistently P ⋀ persistently Q ⊢ persistently (P ⋀ Q) :=
bi_persistently.persistently_and

lemma persistently_exists : persistently (∃' a, Φ a) ⊢ ∃' a, persistently (Φ a) :=
bi_persistently.persistently_exists

lemma persistently_sep : persistently (P ∗ Q) ⊢ persistently P :=
bi_persistently.persistently_sep

lemma persistently_and_sep_elim : persistently (P ⋀ Q) ⊢ P ∗ Q :=
bi_persistently.persistently_and_sep_elim

/-!
# Later
-/

lemma later_nonexpansive : is_nonexpansive (bi_struct.later : ℙ → ℙ) :=
bi_later.later_nonexpansive

lemma later_mono : P ⊢ Q → ▷ P ⊢ ▷ Q :=
bi_later.later_mono

lemma later_intro : P ⊢ ▷ P :=
bi_later.later_intro

lemma forall_later : (∀' a, ▷ Φ a) ⊢ ▷ ∀' a, Φ a :=
bi_later.forall_later

lemma later_exists_false : (▷ ∃' a, Φ a) ⊢ ▷ false ⋁ (∃' a, ▷ Φ a) :=
bi_later.later_exists_false

lemma later_sep : (▷ (P ∗ Q)) = (▷ P ∗ ▷ Q) :=
propext bi_later.later_sep bi_later.later_sep'

lemma persistently_later : (▷ persistently P) = (persistently ▷ P) :=
propext bi_later.persistently_later bi_later.later_persistently

lemma later_false_em : ▷ P ⊢ ▷ false ⋁ (▷ false => P) :=
bi_later.later_false_em

/-!
# Derived connectives
-/

def iff (P Q : ℙ) : ℙ := (P => Q) ⋀ (Q => P)
infixr ` <=> `:28 := iff

def wand_iff (P Q : ℙ) : ℙ := (P -∗ Q) ⋀ (Q -∗ P)
infixr ` ∗-∗ `:90 := wand_iff

class persistent (P : ℙ) : Prop :=
(entails_persistently : P ⊢ persistently P)

def affinely (P : ℙ) := empty ⋀ P

class affine (P : ℙ) : Prop :=
(entails_empty : P ⊢ empty)

def absorbingly (P : ℙ) := true ∗ P

class absorbing (P : ℙ) : Prop :=
(absorbingly_entails : absorbingly P ⊢ P)

def intuitionistically : ℙ → ℙ := affinely ∘ persistently
prefix `□ `:100 := intuitionistically

def persistently_if (p : Prop) [decidable p] (P : ℙ) :=
if p then persistently P else P

def affinely_if (p : Prop) [decidable p] (P : ℙ) :=
if p then affinely P else P

def absorbingly_if (p : Prop) [decidable p] (P : ℙ) :=
if p then absorbingly P else P

def intuitionistically_if (p : Prop) [decidable p] (P : ℙ) :=
if p then □ P else P

def latern : Π (n : ℕ) (P : ℙ), ℙ
| 0 P := P
| (n + 1) P := ▷ latern n P

def except_zero (P : ℙ) := ▷ false ⋁ P
prefix `◇ `:100 := except_zero

class timeless (P : ℙ) : Prop :=
(later_entails_except_zero : ▷ P ⊢ ◇ P)

/-!
# Extensions

Definitions for various extensions to the BI interface.
-/

class bi_affine (ℙ : Type u) [ofe ℙ] [bi_struct ℙ] [bi ℙ] : Prop :=
(is_affine (P : ℙ) : affine P)

class bi_positive (ℙ : Type u) [ofe ℙ] [bi_struct ℙ] [bi ℙ] : Prop :=
(affinely_sep (P Q : ℙ) : affinely (P ∗ Q) ⊢ affinely P ∗ Q)

class bi_loeb (ℙ : Type u) [ofe ℙ] [bi_struct ℙ] [bi ℙ] : Prop :=
(true_entails (P : ℙ) : ▷ P ⊢ P → true ⊢ P)

class bi_later_contractive (ℙ : Type u) [ofe ℙ] [bi_struct ℙ] [bi ℙ] : Prop :=
(later_contractive : is_contractive (bi_struct.later : ℙ → ℙ))

class bi_persistently_forall (ℙ : Type u) [ofe ℙ] [bi_struct ℙ] [bi ℙ] : Prop :=
(persistently_forall {A : Type u} {Φ : A → ℙ} : (∀' a, persistently (Φ a)) ⊢ persistently ∀' a, Φ a)

class bi_pure_forall (ℙ : Type u) [ofe ℙ] [bi_struct ℙ] [bi ℙ] : Prop :=
(pure_forall {A : Type u} {Φ : A → Prop} : (∀' a, ⌜Φ a⌝ : ℙ) ⊢ ⌜∀ a, Φ a⌝)

end bi
