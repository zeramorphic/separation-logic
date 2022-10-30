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

infixr ` ⊢ `:26 := bi_struct.entails
notation `⌜`:1 p:200 `⌝` := bi_struct.pure p
infixr ` ⋀ `:35 := bi_struct.and
infixr ` ⋁ `:30 := bi_struct.or
infixr ` => `:28 := bi_struct.implies
notation `∀'` binders `, ` r:(scoped f, bi_struct.for_all _ f) := r
notation `∃'` binders `, ` r:(scoped f, bi_struct.there_exists _ f) := r
infixr ` ∗ `:80 := bi_struct.sep
infixr ` -∗ `:99 := bi_struct.wand

export bi_struct (persistently)

def bi.empty {ℙ : Type u} [bi_struct ℙ] : ℙ := bi_struct.empty
def bi.true {ℙ : Type u} [bi_struct ℙ] : ℙ := ⌜true⌝
def bi.false {ℙ : Type u} [bi_struct ℙ] : ℙ := ⌜false⌝

class bi_laws_entails (ℙ : Type u) extends bi_struct ℙ :=
(entails_preorder : is_preorder ℙ (⊢))
(propext {P Q : ℙ} : P ⊢ Q → Q ⊢ P → P = Q)

-- TODO: Is `bi_mixin_pure_ne` required given Lean's `propext`?

/-- Nonexpansivity laws. -/
class bi_laws_nonexpansive (ℙ : Type u) [ofe ℙ] [bi_struct ℙ] :=
(and_nonexpansive : is_nonexpansive (function.uncurry ((⋀) : ℙ → ℙ → ℙ)))
(or_nonexpansive : is_nonexpansive (function.uncurry ((⋁) : ℙ → ℙ → ℙ)))
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
(forall_intro {A : Type u} {P : ℙ} {Q : A → ℙ} {a : A} : (∀ a, P ⊢ Q a) → P ⊢ ∀' a, Q a)
(forall_elim {A : Type u} {P : A → ℙ} {a : A} : (∀' a, P a) ⊢ P a)
(exists_intro {A : Type u} {P : A → ℙ} {a : A} : P a ⊢ ∃' a, P a)
(exists_elim {A : Type u} {P : ℙ} {Q : A → ℙ} {a : A} : (∀ a, Q a ⊢ P) → (∃' a, Q a) ⊢ P)

/-- Laws for separating conjunction. -/
class bi_connectives (ℙ : Type u) [bi_struct ℙ] :=
(sep_mono {P Q R S : ℙ} : P ⊢ Q → R ⊢ S → P ∗ R ⊢ Q ∗ S)
(emp_sep {P : ℙ} : P ⊢ bi.empty ∗ P)
(sep_emp {P : ℙ} : P ⊢ P ∗ bi.empty)
(sep_comm {P Q : ℙ} : P ∗ Q ⊢ Q ∗ P)
(sep_assoc {P Q R : ℙ} : (P ∗ Q) ∗ R ⊢ P ∗ Q ∗ R)
(wand_intro {P Q R : ℙ} : P ∗ Q ⊢ R → P ⊢ Q -∗ R)
(wand_elim {P Q R : ℙ} : P ⊢ Q -∗ R → P ∗ Q ⊢ R)

class bi_persistently (ℙ : Type u) [bi_struct ℙ] :=
(mono {P Q : ℙ} : P ⊢ Q → persistently P ⊢ persistently Q)
(persistently_persistently {P : ℙ} : persistently P ⊢ persistently (persistently P))
(empty : (bi.empty : ℙ) ⊢ persistently bi.empty)
(and {P Q : ℙ} : persistently P ⋀ persistently Q ⊢ persistently (P ⋀ Q))
(persistently_exists {A : Type u} {P : A → ℙ} :
  persistently (∃' a, P a) ⊢ ∃' a, persistently (P a))
(sep {P Q : ℙ} : persistently (P ∗ Q) ⊢ persistently P)
(and_sep_elim {P Q : ℙ} : persistently (P ⋀ Q) ⊢ P ∗ Q)

class bi (ℙ : Type u) [ofe ℙ] [bi_struct ℙ] extends
  bi_laws_nonexpansive ℙ, bi_hol ℙ, bi_connectives ℙ, bi_persistently ℙ
