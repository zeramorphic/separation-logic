import topology.metric_space.contracting

universes u v w

/-!
# Ordered families of equivalences

### References
https://plv.mpi-sws.org/iris/appendix-4.0.pdf
-/

/-- An ordered family of equivalences on a type.

Whenever possible, we work with unbundled forms of types,
so that we can make the best of Lean's typeclass inference.
In particular, functors and categorical notions are unbundled and made explicit
wherever possible. -/
class ofe (α : Type u) : Type u :=
(eq_at : ℕ → α → α → Prop)
(eq_at_reflexive : ∀ n, reflexive (eq_at n))
(eq_at_symmetric : ∀ n, symmetric (eq_at n))
(eq_at_transitive : ∀ n, transitive (eq_at n))
(eq_at_mono' : antitone eq_at)
(eq_at_limit' (x y : α) : (∀ n, eq_at n x y) → x = y)

export ofe (eq_at_reflexive eq_at_symmetric eq_at_transitive)

notation a ` =[`:50 n `] ` b:50 := ofe.eq_at n a b

lemma eq_at_equivalence {α : Type u} [ofe α] (n : ℕ) :
  equivalence (ofe.eq_at n : α → α → Prop) :=
⟨eq_at_reflexive n, eq_at_symmetric n, eq_at_transitive n⟩

@[refl] lemma eq_at_refl {α : Type u} [ofe α] (n : ℕ) (x : α) :
  x =[n] x := eq_at_reflexive n x

@[symm] lemma eq_at_symm {α : Type u} [ofe α] (n : ℕ) (x y : α) :
  x =[n] y → y =[n] x :=
λ h, eq_at_symmetric n h

@[symm] lemma eq_at_symm_iff {α : Type u} [ofe α] (n : ℕ) (x y : α) :
  x =[n] y ↔ y =[n] x :=
⟨eq_at_symm n x y, eq_at_symm n y x⟩

@[trans] lemma eq_at_trans {α : Type u} [ofe α] {n : ℕ} {x z : α} (y : α) :
  x =[n] y → y =[n] z → x =[n] z :=
λ hxy hyz, eq_at_transitive n hxy hyz

instance {α : Type u} [ofe α] (n : ℕ) : is_refl α (ofe.eq_at n) :=
⟨eq_at_refl n⟩

instance {α : Type u} [ofe α] (n : ℕ) : is_symm α (ofe.eq_at n) :=
⟨eq_at_symmetric n⟩

instance {α : Type u} [ofe α] (n : ℕ) : is_trans α (ofe.eq_at n) :=
⟨eq_at_transitive n⟩

instance {α : Type u} [ofe α] (n : ℕ) : is_preorder α (ofe.eq_at n) := ⟨⟩

instance {α : Type u} [ofe α] (n : ℕ) : is_equiv α (ofe.eq_at n) := ⟨⟩

lemma eq_at_mono {α : Type u} [ofe α] {m n : ℕ} (hmn : m ≤ n) {x y : α} :
  x =[n] y → x =[m] y :=
ofe.eq_at_mono' hmn x y

lemma eq_at_trans_not {α : Type u} [ofe α] (n : ℕ) (x y z : α) :
  x =[n] y → ¬y =[n] z → ¬x =[n] z :=
begin
  intro h₁,
  contrapose!,
  rw eq_at_symm_iff at h₁,
  intro h₂,
  transitivity x;
  assumption,
end

lemma eq_at_forall_trans {α : Type u} [ofe α] {n : ℕ} {x y z : α} :
  x =[n] y → ∀ k ≤ n, x =[k] z ↔ y =[k] z :=
begin
  intros hxy k hk,
  split,
  { intro hxz,
    refine eq_at_trans x _ hxz,
    rw eq_at_symm_iff,
    exact eq_at_mono hk hxy, },
  { intro hyz,
    refine eq_at_trans y _ hyz,
    exact eq_at_mono hk hxy, },
end

lemma eq_at_forall_trans' {α : Type u} [ofe α] {n : ℕ} {x y z : α} :
  x =[n] y → ¬x =[n] z → ∀ k, x =[k] z ↔ y =[k] z :=
begin
  intros hxy hxz k,
  by_cases k ≤ n,
  { exact eq_at_forall_trans hxy k h, },
  rw eq_at_symm_iff at hxy,
  have := eq_at_trans_not n y x z hxy hxz,
  push_neg at h,
  have h₁ := eq_at_mono h.le,
  have h₂ := eq_at_mono h.le,
  split,
  { intro h, cases hxz (h₁ h), },
  { intro h, cases this (h₂ h), },
end

lemma eq_at_limit {α : Type u} [ofe α] (x y : α) :
  x = y ↔ ∀ n, x =[n] y :=
⟨by rintro rfl a; refl, ofe.eq_at_limit' x y⟩

lemma exists_ne_of_ne {α : Type u} [ofe α] {x y : α} : x ≠ y → ∃ n, ¬x =[n] y :=
by contrapose!; exact (eq_at_limit x y).mpr

lemma ne_of_exists_ne {α : Type u} [ofe α] {x y : α} : (∃ n, ¬x =[n] y) → x ≠ y :=
by contrapose!; exact (eq_at_limit x y).mp

lemma exists_ne_iff_ne {α : Type u} [ofe α] {x y : α} : x ≠ y ↔ ∃ n, ¬x =[n] y :=
⟨exists_ne_of_ne, ne_of_exists_ne⟩

/-- The critical point of two nonequal elements of a type with an OFE is the smallest
time index that finds that the two elements differ. -/
noncomputable def critical_point {α : Type u} [ofe α] {x y : α}
  (h : x ≠ y) : ℕ :=
@nat.find _ (λ _, classical.dec _) (exists_ne_of_ne h)

lemma critical_point_spec {α : Type u} [ofe α] {x y : α} (h : x ≠ y) :
  ¬x =[critical_point h] y :=
@nat.find_spec _ (λ _, classical.dec _) (exists_ne_of_ne h)

lemma critical_point_min {α : Type u} [ofe α] {x y : α} (h : x ≠ y) {m : ℕ} :
  m < critical_point h → x =[m] y :=
λ hm, not_not.mp (@nat.find_min _ (λ _, classical.dec _) (exists_ne_of_ne h) m hm)

lemma critical_point_min' {α : Type u} [ofe α] {x y : α} (h : x ≠ y)
  {m : ℕ} (hm : ¬x =[m] y) : critical_point h ≤ m :=
@nat.find_min' _ (λ _, classical.dec _) (exists_ne_of_ne h) m hm

/-- An equivalent description of the `eq_at` operation on distinct elements
in ordered families of equivalences. -/
lemma eq_at_iff_lt_critical_point {α : Type u} [ofe α] {x y : α} (h : x ≠ y)
  {m : ℕ} : x =[m] y ↔ m < critical_point h :=
begin
  split,
  { intro hm,
    by_contra' this,
    exact critical_point_spec h (eq_at_mono this hm), },
  { intro hm,
    by_contra this,
    exact not_le_of_lt hm (critical_point_min' h this), },
end

lemma critical_point_eq_zero {α : Type u} [ofe α] {x y : α} (h : x ≠ y) :
  critical_point h = 0 ↔ ∀ n, ¬x =[n] y :=
begin
  split,
  { intros hp n hn,
    rw eq_at_iff_lt_critical_point h at hn,
    generalize_proofs at hn,
    rw hp at hn,
    exact nat.not_lt_zero n hn, },
  { intro hp,
    have := critical_point_min' h (hp 0),
    exact le_zero_iff.mp this, },
end

/-- An element of an ordered family of equivalences on a type is *discrete*
if the equivalence at time step zero is equality. -/
def is_discrete {α : Type u} [ofe α] (x : α) : Prop :=
∀ y, x =[0] y → x = y

/-- We can make an OFE on any type which is discrete on all elements. -/
def discrete_ofe (α : Type u) : ofe α := {
  eq_at := λ _, (=),
  eq_at_reflexive := λ _, eq_equivalence.1,
  eq_at_symmetric := λ _, eq_equivalence.2.1,
  eq_at_transitive := λ _, eq_equivalence.2.2,
  eq_at_mono' := λ _ _ _, le_of_eq rfl,
  eq_at_limit' := λ x y h, h 0,
}

@[simp] lemma discrete_ofe_eq_at {α : Type u} (x y : α) (n : ℕ) :
  (discrete_ofe α).eq_at n x y ↔ x = y := iff.rfl

section nonexpansive

/-!
# Nonexpansive and contractive functions

We define nonexpansive and contractive functions, as well as their function classes.
-/

/-- Applying a non-expansive function to some data will not introduce
differences between seemingly equal data. Elements that cannot be distinguished
by programs within `n` steps remain indistinguishable after applying `f`. -/
def is_nonexpansive {α : Type u} {β : Type v} [ofe α] [ofe β] (f : α → β) : Prop :=
∀ ⦃n x y⦄, x =[n] y → f x =[n] f y

lemma is_nonexpansive.apply_eq_at {α : Type u} {β : Type v} [ofe α] [ofe β] {f : α → β}
  (h : is_nonexpansive f) {a b : α} {n : ℕ} (hab : a =[n] b) : f a =[n] f b := h hab

def is_contractive {α : Type u} {β : Type v} [ofe α] [ofe β] (f : α → β) : Prop :=
∀ n ⦃x y⦄, (∀ m < n, x =[m] y) → f x =[n] f y

lemma is_nonexpansive_of_is_contractive {α : Type u} {β : Type v} [ofe α] [ofe β] (f : α → β) :
  is_contractive f → is_nonexpansive f :=
begin
  intros hf n x y h,
  refine hf n _,
  intros m hm,
  exact eq_at_mono hm.le h,
end

@[simp] lemma is_nonexpansive_id {α : Type u} [ofe α] :
  is_nonexpansive (id : α → α) :=
λ n x y h, h

@[simp] lemma is_nonexpansive_comp {α : Type u} {β : Type v} {γ : Type w}
  [ofe α] [ofe β] [ofe γ] (f : β → γ) (g : α → β) :
  is_nonexpansive f → is_nonexpansive g → is_nonexpansive (f ∘ g) :=
λ hf hg n x y h, hf (hg h)

@[ext] structure nonexpansive_fun (α : Type u) (β : Type v) [ofe α] [ofe β] : Type (max u v) :=
(to_fun : α → β)
(is_nonexpansive' : is_nonexpansive to_fun)

class nonexpansive_fun_class (F : Type w) (α : Type u) (β : Type v) [ofe α] [ofe β]
  extends fun_like F α (λ _, β) :=
(is_nonexpansive : ∀ (f : F), is_nonexpansive f)

instance nonexpansive_fun.nonexpansive_fun_class {α : Type u} {β : Type v} [ofe α] [ofe β] :
  nonexpansive_fun_class (nonexpansive_fun α β) α β := {
  coe := nonexpansive_fun.to_fun,
  coe_injective' := begin intros f g h, ext1, exact h, end,
  is_nonexpansive := nonexpansive_fun.is_nonexpansive',
}

instance (F : Type w) (α : Type u) (β : Type v) [ofe α] [ofe β] [nonexpansive_fun_class F α β] :
  has_coe_t F (nonexpansive_fun α β) :=
⟨λ f, { to_fun := f, is_nonexpansive' := nonexpansive_fun_class.is_nonexpansive f }⟩

/-- Nonexpansive functions are nonexpansive. -/
lemma nonexpansive {α : Type u} {β : Type v} [ofe α] [ofe β] {F : Type w}
  [nonexpansive_fun_class F α β] (f : F) : is_nonexpansive f :=
nonexpansive_fun_class.is_nonexpansive f

infixr ` →ₙₑ `:25 := nonexpansive_fun

@[simp] lemma nonexpansive_fun.coe_fn_mk (α : Type u) (β : Type v) [ofe α] [ofe β]
  (f : α → β) (hf : is_nonexpansive f) : ((⟨f, hf⟩ : α →ₙₑ β) : α → β) = f := rfl

def nonexpansive_fun.id (α : Type u) [ofe α] : α →ₙₑ α :=
⟨id, is_nonexpansive_id⟩

def nonexpansive_fun.comp {α : Type u} {β : Type v} {γ : Type w} [ofe α] [ofe β] [ofe γ]
  (f : β →ₙₑ γ) (g : α →ₙₑ β) : α →ₙₑ γ :=
⟨f ∘ g, is_nonexpansive_comp f g f.is_nonexpansive' g.is_nonexpansive'⟩

@[simp] lemma nonexpansive_fun.to_fun_eq_coe_fn {α : Type u} {β : Type v} [ofe α] [ofe β]
  (f : α →ₙₑ β) : f.to_fun = f := rfl

@[simp] lemma is_contractive_comp {α : Type u} {β : Type v} {γ : Type w}
  [ofe α] [ofe β] [ofe γ] (f : β → γ) (g : α → β) :
  is_contractive f → is_contractive g → is_contractive (f ∘ g) :=
λ hf hg n x y h, hf n (λ m hm, hg m (λ k hk, eq_at_mono hk.le (h m hm)))

@[ext] structure contractive_fun (α : Type u) (β : Type v) [ofe α] [ofe β] :=
(to_fun : α → β)
(is_contractive' : is_contractive to_fun)

class contractive_fun_class (F : Type w) (α : Type u) (β : Type v) [ofe α] [ofe β]
  extends fun_like F α (λ _, β) :=
(is_contractive : ∀ (f : F), is_contractive f)

/-- Contractive functions are nonexpansive. -/
instance contractive_fun_class.nonexpansive_fun_class {α : Type u} {β : Type v}
  [ofe α] [ofe β] {F : Type w} [contractive_fun_class F α β] : nonexpansive_fun_class F α β := {
  is_nonexpansive :=
    λ f, is_nonexpansive_of_is_contractive f (contractive_fun_class.is_contractive f),
}

instance contractive_fun.contractive_fun_class {α : Type u} {β : Type v} [ofe α] [ofe β] :
  contractive_fun_class (contractive_fun α β) α β := {
  coe := contractive_fun.to_fun,
  coe_injective' := begin intros f g h, ext1, exact h, end,
  is_contractive := contractive_fun.is_contractive',
}

instance (F : Type w) (α : Type u) (β : Type v) [ofe α] [ofe β] [contractive_fun_class F α β] :
  has_coe_t F (contractive_fun α β) :=
⟨λ f, { to_fun := f, is_contractive' := contractive_fun_class.is_contractive f }⟩

/-- Contractive functions are contractive. -/
lemma contractive {α : Type u} {β : Type v} [ofe α] [ofe β] {F : Type w}
  [contractive_fun_class F α β] (f : F) : is_contractive f :=
contractive_fun_class.is_contractive f

infixr ` →ₖ `:25 := contractive_fun

@[simp] lemma contractive_fun.to_fun_eq_coe_fn {α : Type u} {β : Type v} [ofe α] [ofe β]
  (f : α →ₖ β) : f.to_fun = f := rfl

/-- The critical point of two different objects can never increase
when applying a nonexpansive function. -/
lemma critical_point_nonexpansive {α : Type u} {β : Type v} [ofe α] [ofe β] {F : Type w}
  [nonexpansive_fun_class F α β] (f : F) {x y : α} (hxy : f x ≠ f y) :
  critical_point (ne_of_apply_ne f hxy) ≤ critical_point hxy :=
begin
  refine critical_point_min' _ _,
  intro h,
  have := nonexpansive f h,
  exact critical_point_spec _ this,
end

/-- The critical point of two different objects decreases when
applying a contractive function. -/
lemma critical_point_contractive {α : Type u} {β : Type v} [ofe α] [ofe β] {F : Type w}
  [contractive_fun_class F α β] (f : F) {x y : α} (hxy : f x ≠ f y) :
  critical_point (ne_of_apply_ne f hxy) < critical_point hxy :=
begin
  rw ← eq_at_iff_lt_critical_point,
  refine contractive f (critical_point _) _,
  intros m hm,
  rw eq_at_iff_lt_critical_point (ne_of_apply_ne f hxy),
  exact hm,
end

end nonexpansive

/-- The space of nonexpansive functions forms an OFE. -/
instance nonexpansive_fun.ofe {α : Type u} {β : Type v} [ofe α] [ofe β]
  {F : Type w} [nonexpansive_fun_class F α β] : ofe F := {
  eq_at := λ n f g, ∀ x, f x =[n] g x,
  eq_at_reflexive := begin
    intros n f a,
    refl,
  end,
  eq_at_symmetric := begin
    intros n f g h x,
    rw eq_at_symm_iff,
    exact h x,
  end,
  eq_at_transitive := begin
    intros n f g h hfg hgh x,
    transitivity g x,
    exact hfg x,
    exact hgh x,
  end,
  eq_at_mono' := begin
    intros m n hmn f g h x,
    refine eq_at_mono hmn _,
    exact h x,
  end,
  eq_at_limit' := begin
    intros f g h,
    refine fun_like.coe_injective _,
    ext x,
    rw eq_at_limit,
    intro n,
    exact h n x,
  end,
}

/-!
# Locally nonexpansive functors
-/

/-- We define the notion of an OFE functor explicitly without appealing to mathlib's category
theory library in order to avoid unnecessarily complicated bundled types for this use case. -/
structure ofe_functor :=
(obj : Type u → Type u)
[ofe_obj : Π (α : Type u) [ofe α], ofe (obj α)]
(map : Π {α β : Type u} [ofe α] [ofe β], (α →ₙₑ β) → (obj α →ₙₑ obj β))
(map_id : ∀ (α : Type u) [ofe α], map (nonexpansive_fun.id α) = nonexpansive_fun.id (obj α))
(map_comp : ∀ {α β γ : Type u} [ofe α] [ofe β] [ofe γ] (f : β →ₙₑ γ) (g : α →ₙₑ β),
  map (f.comp g) = (map f).comp (map g))

/-- A contravariant-covariant bifunctor `Ofeᵒᵖ × Ofe ⥤ Ofe`. -/
structure ofe_bifunctor :=
(obj : Π (α : Type u) (β : Type u) [ofe α] [ofe β], Type u)
[ofe_obj : Π (α : Type u) (β : Type u) [ofe α] [ofe β], ofe (obj α β)]
(map : Π {α β γ δ : Type u} [ofe α] [ofe β] [ofe γ] [ofe δ],
  (γ →ₙₑ α) → (β →ₙₑ δ) → (obj α β →ₙₑ obj γ δ))
(map_id : ∀ (α β : Type u) [ofe α] [ofe β],
  map (nonexpansive_fun.id α) (nonexpansive_fun.id β) = nonexpansive_fun.id (obj α β))
(map_comp : ∀ {α β γ δ ε ζ : Type u}
  [ofe α] [ofe β] [ofe γ] [ofe δ] [ofe ε] [ofe ζ]
  (fαβ : α →ₙₑ β) (fβγ : β →ₙₑ γ) (fδε : δ →ₙₑ ε) (fεζ : ε →ₙₑ ζ),
  map (fβγ.comp fαβ) (fεζ.comp fδε) = (map fαβ fεζ).comp (map fβγ fδε))

def locally_nonexpansive_functor (F : ofe_functor) : Prop :=
∀ (α β : Type u) [ofe α] [ofe β],
begin
  resetI,
  letI := F.ofe_obj α,
  letI := F.ofe_obj β,
  exact is_nonexpansive (F.map : (α →ₙₑ β) → (F.obj α →ₙₑ F.obj β))
end

def locally_contractive_functor (F : ofe_functor) : Prop :=
∀ (α β : Type u) [ofe α] [ofe β],
begin
  resetI,
  letI := F.ofe_obj α,
  letI := F.ofe_obj β,
  exact is_contractive (F.map : (α →ₙₑ β) → (F.obj α →ₙₑ F.obj β))
end

lemma nonexpansive_fun.congr_arg {α : Type u} {β : Type v} [ofe α] [ofe β]
  {F : Type w} [nonexpansive_fun_class F α β] {f : F}
  {a b : α} (n : ℕ) : a =[n] b → f a =[n] f b :=
λ h, nonexpansive f h

lemma nonexpansive_fun.congr_fun {α : Type u} {β : Type v} [ofe α] [ofe β]
  {F : Type w} [nonexpansive_fun_class F α β] {f g : F}
  {a : α} (n : ℕ) : f =[n] g → f a =[n] g a :=
λ h, h a

lemma nonexpansive_fun.congr {α : Type u} {β : Type v} [ofe α] [ofe β]
  {F : Type w} [nonexpansive_fun_class F α β] {f g : F}
  {a b : α} (n : ℕ) : f =[n] g → a =[n] b → f a =[n] g b :=
begin
  intros h₁ h₂,
  transitivity g a,
  exact h₁ a,
  exact nonexpansive g h₂,
end

lemma nonexpansive_fun.comp_is_nonexpansive {α : Type u} {β : Type v} {γ : Type w}
  [ofe α] [ofe β] [ofe γ] (f : β →ₙₑ γ) : is_nonexpansive (f.comp : (α →ₙₑ β) → α →ₙₑ γ) :=
begin
  intros n g h hgh a,
  refine nonexpansive f _,
  exact hgh a,
end

lemma nonexpansive_fun.congr_fun_comp {α : Type u} {β : Type v} {γ : Type w}
  [ofe α] [ofe β] [ofe γ]
  {F : Type*} [nonexpansive_fun_class F β γ] {f₁ f₂ : F}
  {G : Type*} [nonexpansive_fun_class G α β] {g₁ g₂ : G}
  {a : α} (n : ℕ) : f₁ =[n] f₂ → g₁ =[n] g₂ → f₁ (g₁ a) =[n] f₂ (g₂ a) :=
begin
  intros h₁ h₂,
  transitivity f₁ (g₂ a),
  exact nonexpansive f₁ (h₂ a),
  exact h₁ _,
end

lemma nonexpansive_fun.comp_left_eq_at {α : Type u} {β : Type v} {γ : Type w}
  [ofe α] [ofe β] [ofe γ] {f : β →ₙₑ γ} {g h : α →ₙₑ β} {n : ℕ} :
  g =[n] h → f.comp g =[n] f.comp h :=
λ hgh, nonexpansive_fun.comp_is_nonexpansive f hgh

lemma nonexpansive_fun.comp_right_eq_at {α : Type u} {β : Type v} {γ : Type w}
  [ofe α] [ofe β] [ofe γ] {f g : β →ₙₑ γ} {h : α →ₙₑ β} {n : ℕ} :
  f =[n] g → f.comp h =[n] g.comp h :=
λ hfg a, hfg (h a)
