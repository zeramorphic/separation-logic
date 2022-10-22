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
class ofe (α : Type u) :=
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

@[ext] structure nonexpansive_fun (α : Type u) (β : Type v) [ofe α] [ofe β] :=
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

/-!
# OFE instances

We construct instances for OFEs on a variety of types, such as products and sums.
This will show that the category of OFEs is bicartesian closed: it has all sums, products
and exponentials, as well as an initial and terminal object.

TODO: Add definitions to map nonexpansive functions between these new types.
-/

-- TODO: Add a ton of lemmas for actually using these instances.

instance {α : Type u} {β : Type v} [ofe α] [ofe β] : ofe (α × β) := {
  eq_at := λ n x y, x.1 =[n] y.1 ∧ x.2 =[n] y.2,
  eq_at_reflexive := begin
    intros n x,
    split;
    refl,
  end,
  eq_at_symmetric := begin
    intros n x y h,
    exact ⟨eq_at_symmetric n h.1, eq_at_symmetric n h.2⟩,
  end,
  eq_at_transitive := begin
    intros n x y z hxy hyz,
    exact ⟨eq_at_trans _ hxy.1 hyz.1, eq_at_trans _ hxy.2 hyz.2⟩,
  end,
  eq_at_mono' := begin
    intros m n hmn x y h,
    exact ⟨eq_at_mono hmn h.1, eq_at_mono hmn h.2⟩,
  end,
  eq_at_limit' := begin
    intros x y h,
    ext1;
    rw eq_at_limit;
    intro n,
    exact (h n).1,
    exact (h n).2,
  end,
}

@[simp] lemma prod.eq_at {α : Type u} {β : Type v} [ofe α] [ofe β] (n : ℕ) (x y : α × β) :
  x =[n] y ↔ x.1 =[n] y.1 ∧ x.2 =[n] y.2 := iff.rfl

instance pi.ofe {α : Type u} {β : α → Type v} [ofe α] [Π (a : α), ofe (β a)] :
  ofe (Π (a : α), β a) := {
  eq_at := λ n x y, ∀ a, x a =[n] y a,
  eq_at_reflexive := begin
    intros n x a,
    refl,
  end,
  eq_at_symmetric := begin
    intros n x y h a,
    rw eq_at_symm_iff,
    exact h a,
  end,
  eq_at_transitive := begin
    intros n x y z hxy hyz a,
    transitivity y a,
    exact hxy a,
    exact hyz a,
  end,
  eq_at_mono' := begin
    intros m n hmn x y h a,
    refine eq_at_mono hmn _,
    exact h a,
  end,
  eq_at_limit' := begin
    intros x y h,
    ext a,
    rw eq_at_limit,
    intro n,
    exact h n a,
  end,
}

lemma is_nonexpansive.uncurry_apply_eq_at {α : Type u} {β : Type v} {γ : Type w}
  [ofe α] [ofe β] [ofe γ] {f : α → β → γ}
  (h : is_nonexpansive (function.uncurry f)) {a b : α} {c d : β} {n : ℕ}
  (hab : a =[n] b) (hcd : c =[n] d) : f a c =[n] f b d :=
h (⟨hab, hcd⟩ : (a, c) =[n] (b, d))

@[simp] lemma pi.eq_at {α : Type u} {β : α → Type v} [ofe α] [Π (a : α), ofe (β a)]
  (n : ℕ) (x y : Π (a : α), β a) :
  x =[n] y ↔ ∀ a, x a =[n] y a := iff.rfl

def option.eq_at {α : Type u} [ofe α] (n : ℕ) : option α → option α → Prop
| (some a) (some b) := a =[n] b
| (some a) none := false
| none (some b) := false
| none none := true

private lemma option.some_eq_at_some {α : Type u} [ofe α] {n : ℕ} {a b : α} :
  option.eq_at n (some a) (some b) ↔ a =[n] b := iff.rfl

private lemma option.some_eq_at_none {α : Type u} [ofe α] {n : ℕ} {a : α} :
  option.eq_at n (some a) none ↔ false := iff.rfl

private lemma option.none_eq_at_some {α : Type u} [ofe α] {n : ℕ} {b : α} :
  option.eq_at n none (some b) ↔ false := iff.rfl

private lemma option.none_eq_at_none {α : Type u} [ofe α] {n : ℕ}:
  option.eq_at n (none : option α) none := trivial

instance {α : Type u} [ofe α] : ofe (option α) := {
  eq_at := option.eq_at,
  eq_at_reflexive := begin
    intros n x,
    cases x,
    trivial,
    exact eq_at_refl n x,
  end,
  eq_at_symmetric := begin
    intros n x y h,
    cases x;
    cases y;
    simp only [option.some_eq_at_some,
      option.some_eq_at_none,
      option.none_eq_at_some,
      option.none_eq_at_none] at h ⊢,
    cases h,
    cases h,
    rw eq_at_symm_iff,
    exact h,
  end,
  eq_at_transitive := begin
    intros n x y z hxy hyz,
    cases x; cases y; cases z;
    simp only [option.some_eq_at_some,
      option.some_eq_at_none,
      option.none_eq_at_some,
      option.none_eq_at_none] at hxy hyz ⊢;
    try { cases hxy, };
    try { cases hyz, },
    transitivity y,
    exact hxy,
    exact hyz,
  end,
  eq_at_mono' := begin
    intros m n hmn x y h,
    cases x; cases y;
    simp only [option.some_eq_at_some,
      option.some_eq_at_none,
      option.none_eq_at_some,
      option.none_eq_at_none] at h ⊢,
    exact h,
    exact h,
    exact eq_at_mono hmn h,
  end,
  eq_at_limit' := begin
    intros x y h,
    cases x; cases y;
    simp only [option.some_eq_at_some,
      option.some_eq_at_none,
      option.none_eq_at_some,
      option.none_eq_at_none] at h ⊢,
    cases h 0,
    exact h 0,
    rw eq_at_limit,
    exact h,
  end,
}

instance {α : Type u} [ofe α] : ofe (part α) := {
  eq_at := λ n a b, (¬a.dom ∧ ¬b.dom) ∨ ∃ (ha : a.dom) (hb : b.dom), a.get ha =[n] b.get hb,
  eq_at_reflexive := begin
    intros n a,
    by_cases a.dom,
    { right,
      refine ⟨h, h, _⟩,
      refl, },
    { left,
      exact ⟨h, h⟩, },
  end,
  eq_at_symmetric := begin
    rintros n a b (⟨ha, hb⟩ | ⟨ha, hb, hab⟩),
    { left,
      exact ⟨hb, ha⟩, },
    { right,
      refine ⟨hb, ha, _⟩,
      symmetry,
      exact hab, },
  end,
  eq_at_transitive := begin
    rintros n a b c (⟨ha, hb⟩ | ⟨ha, hb, hab⟩) (⟨hb', hc⟩ | ⟨hb', hc, hbc⟩),
    { left,
      exact ⟨ha, hc⟩, },
    { cases hb hb', },
    { cases hb' hb, },
    { right,
      refine ⟨ha, hc, _⟩,
      transitivity b.get hb,
      exact hab,
      exact hbc, },
  end,
  eq_at_mono' := begin
    rintros m n hmn a b (⟨ha, hb⟩ | ⟨ha, hb, hab⟩),
    { left,
      exact ⟨ha, hb⟩, },
    { right,
      refine ⟨ha, hb, _⟩,
      exact eq_at_mono hmn hab, },
  end,
  eq_at_limit' := begin
    intros a b h,
    rcases h 0 with (h' | ⟨ha, hb, h'⟩),
    { refine part.ext' _ _;
      tauto, },
    { refine part.ext' _ _,
      { tauto, },
      intros _ _,
      rw eq_at_limit,
      intro n,
      rcases h n with (h'' | ⟨ha, hb, h''⟩),
      { cases h''.1 ha, },
      { exact h'', }, },
  end,
}

instance {α : Type u} {β : Type v} [ofe α] [ofe β] : ofe (α ⊕ β) := {
  eq_at := λ n x y, sum.elim
    (λ a, sum.elim (λ b, a =[n] b) (λ _, false) y)
    (λ a, sum.elim (λ _, false) (λ b, a =[n] b) y) x,
  eq_at_reflexive := begin
    intros n x,
    cases x;
    simp only [sum.elim_inl, sum.elim_inr],
  end,
  eq_at_symmetric := begin
    intros n x y h,
    cases x; cases y;
    simp only [sum.elim_inl, sum.elim_inr] at h ⊢;
    try { exact h, };
    exact eq_at_symmetric n h,
  end,
  eq_at_transitive := begin
    intros n x y z hxy hyz,
    cases x; cases y; cases z;
    simp only [sum.elim_inl, sum.elim_inr] at hxy hyz ⊢;
    try { cases hyz, };
    try { cases hxy, };
    transitivity y;
    assumption,
  end,
  eq_at_mono' := begin
    intros m n hmn x y h,
    cases x; cases y;
    simp only [sum.elim_inl, sum.elim_inr] at h ⊢;
    try { exact h, };
    exact eq_at_mono hmn h,
  end,
  eq_at_limit' := begin
    intros x y h,
    cases x; cases y;
    simp only [sum.elim_inl, sum.elim_inr] at h ⊢;
    try { exact (h 0), };
    rw eq_at_limit;
    exact h,
  end,
}

/-- TODO: Make nicer versions of this lemma. -/
@[simp] lemma sum.eq_at {α : Type u} {β : Type v} [ofe α] [ofe β] (n : ℕ) (x y : α ⊕ β) :
  x =[n] y ↔ sum.elim
    (λ a, sum.elim (λ b, a =[n] b) (λ _, false) y)
    (λ a, sum.elim (λ _, false) (λ b, a =[n] b) y) x := iff.rfl

/-- Applies `γ` to two `Σ` types. If their first components match, applies `γ` as expected,
otherwise, returns `false`. The cast is alright here, because we're inside `Prop`. -/
def map_or_false {α : Type u} {β : α → Type v} (γ : Π (x : α), β x → β x → Prop)
  (x y : Σ (x : α), β x) : Prop :=
@dite _ (x.fst = y.fst) (classical.dec _)
  (λ h, γ x.fst x.snd (cast (congr_arg β h.symm) y.snd))
  (λ _, false)

@[simp] lemma map_or_false_self {α : Type u} {β : α → Type v} (γ : Π (x : α), β x → β x → Prop)
  (x : Σ (x : α), β x) : map_or_false γ x x = γ x.fst x.snd x.snd :=
begin
  unfold map_or_false,
  rw dif_pos rfl,
  refl,
end

@[simp] lemma map_or_false_mk {α : Type u} {β : α → Type v} (γ : Π (x : α), β x → β x → Prop)
  (x : α) (y z : β x) : map_or_false γ ⟨x, y⟩ ⟨x, z⟩ = γ x y z :=
begin
  unfold map_or_false,
  rw dif_pos rfl,
  refl,
end

lemma map_or_false_implies {α : Type u} {β : α → Type v} {γ : Π (x : α), β x → β x → Prop}
  {x₁ x₂ : α} {y₁ : β x₁} {y₂ : β x₂} : map_or_false γ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ → x₁ = x₂ :=
begin
  unfold map_or_false,
  split_ifs,
  { cases h,
    exact λ _, rfl, },
  { intro h,
    cases h, },
end

instance {α : Type u} {β : α → Type v} [ofe α] [Π (a : α), ofe (β a)] :
  ofe (Σ (a : α), β a) := {
  eq_at := λ n x y, map_or_false (λ a b c, b =[n] c) x y,
  eq_at_reflexive := begin
    intros n x,
    rw map_or_false_self,
  end,
  eq_at_symmetric := begin
    rintros n ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h,
    cases map_or_false_implies h,
    rw map_or_false_mk at h ⊢,
    rw eq_at_symm_iff,
    exact h,
  end,
  eq_at_transitive := begin
    rintros n ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨z₁, z₂⟩ hxy hyz,
    cases map_or_false_implies hxy,
    cases map_or_false_implies hyz,
    rw map_or_false_mk at hxy hyz ⊢,
    transitivity y₂,
    exact hxy,
    exact hyz,
  end,
  eq_at_mono' := begin
    rintros m n hmn ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h,
    cases map_or_false_implies h,
    rw map_or_false_mk at h ⊢,
    exact eq_at_mono hmn h,
  end,
  eq_at_limit' := begin
    rintros ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h,
    cases map_or_false_implies (h 0),
    simp only [eq_self_iff_true, heq_iff_eq, true_and],
    rw eq_at_limit,
    intro n,
    have := h n,
    rw map_or_false_mk at this,
    exact this,
  end,
}

/-- TODO: Make nicer versions of this lemma. -/
@[simp] lemma sigma.eq_at {α : Type u} {β : α → Type v} [ofe α] [Π (a : α), ofe (β a)]
  (n : ℕ) (x y : Σ (a : α), β a) :
  x =[n] y ↔ map_or_false (λ a b c, b =[n] c) x y := iff.rfl

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

def locally_nonexpansive_bifunctor (F : ofe_bifunctor) : Prop :=
∀ (α β γ δ : Type u) [ofe α] [ofe β] [ofe γ] [ofe δ],
begin
  resetI,
  letI := F.ofe_obj α β,
  letI := F.ofe_obj γ δ,
  exact is_nonexpansive (λ f, F.map f.1 f.2 :
    (γ →ₙₑ α) × (β →ₙₑ δ) → (F.obj α β →ₙₑ F.obj γ δ)),
end

def locally_contractive_bifunctor (F : ofe_bifunctor) : Prop :=
∀ (α β γ δ : Type u) [ofe α] [ofe β] [ofe γ] [ofe δ],
begin
  resetI,
  letI := F.ofe_obj α β,
  letI := F.ofe_obj γ δ,
  exact is_contractive (λ f, F.map f.1 f.2 :
    (γ →ₙₑ α) × (β →ₙₑ δ) → (F.obj α β →ₙₑ F.obj γ δ)),
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

def pi.ofe_bifunctor : ofe_bifunctor := {
  obj := λ α β [ofe α] [ofe β], by exactI α →ₙₑ β,
  map := λ α β γ δ [ofe α] [ofe β] [ofe γ] [ofe δ] f g,
    by exactI ⟨λ h, g.comp (h.comp f), begin
      intros n g h hgh,
      refine nonexpansive_fun.comp_left_eq_at _,
      refine nonexpansive_fun.comp_right_eq_at _,
      exact hgh,
    end⟩,
  map_id := by intros; ext; refl,
  map_comp := by intros; refl,
}

lemma pi.ofe_bifunctor_locally_nonexpansive : locally_nonexpansive_bifunctor pi.ofe_bifunctor :=
begin
  introsI α β γ δ _ _ _ _ _ _ n f₁ f₂ h g a,
  refine nonexpansive_fun.congr_fun_comp _ h.2 _,
  exact nonexpansive_fun.comp_left_eq_at h.1,
end

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

/-- A *step-indexed proposition* is a proposition at each time step `n : ℕ`, such that if `p n`,
we must have `p m` for all `m ≤ n`. -/
@[ext] structure {u'} sprop : Type u' :=
(p : ℕ → Prop)
(mono : antitone p)

instance sprop.fun_like : fun_like sprop.{u} ℕ (λ _, Prop) := {
  coe := sprop.p,
  coe_injective' := λ p q h, by ext1; exact h,
}

@[simp] lemma sprop.coe_fn_mk
  (p : ℕ → Prop) (mono : antitone p) : ((⟨p, mono⟩ : sprop) : ℕ → Prop) = p := rfl

instance : ofe sprop := {
  eq_at := λ n p q, ∀ m ≤ n, p m ↔ q m,
  eq_at_reflexive := by intros _ _ _ _; refl,
  eq_at_symmetric := begin
    intros n p q h m hmn,
    rw h m hmn,
  end,
  eq_at_transitive := begin
    intros n p q r hpq hqr m hmn,
    rw hpq m hmn,
    rw hqr m hmn,
  end,
  eq_at_mono' := begin
    intros m n hmn p q h k hkm,
    rw h _ (hkm.trans hmn),
  end,
  eq_at_limit' := begin
    intros p q h,
    ext n,
    exact h n n le_rfl,
  end,
}

instance : cofe sprop := {
  lim := λ c, ⟨λ n, c n n,
    λ m n hmn h, (c.prop m n hmn m le_rfl).mpr ((c n).mono hmn h)⟩,
  complete := λ n c m hmn, c.prop m n hmn m le_rfl,
}

instance : has_le sprop := ⟨λ p q, ∀ m n, m ≤ n → p m → q m⟩

instance : partial_order sprop := {
  le_refl := λ a m n h, id,
  le_trans := λ p q r hpq hqr m n h, (hqr m n h) ∘ (hpq m n h),
  le_antisymm := λ a b h₁ h₂, by ext n; exact ⟨h₁ n n le_rfl, h₂ n n le_rfl⟩,
  ..sprop.has_le
}

instance : semilattice_inf sprop := {
  inf := λ p q, ⟨λ n, p n ∧ q n, λ m n hmn h, ⟨p.mono hmn h.1, q.mono hmn h.2⟩⟩,
  inf_le_left := λ p q m n hmn h, h.1,
  inf_le_right := λ p q m n hmn h, h.2,
  le_inf := λ p q r hpq hpr m n hmn hp, ⟨hpq m n hmn hp, hpr m n hmn hp⟩,
  ..sprop.partial_order
}

instance : semilattice_sup sprop := {
  sup := λ p q, ⟨λ n, p n ∨ q n, λ m n hmn h,
    h.elim (λ h, or.inl $ p.mono hmn h) (λ h, or.inr $ q.mono hmn h)⟩,
  le_sup_left := λ p q m n hmn h, or.inl h,
  le_sup_right := λ p q m n hmn h, or.inr h,
  sup_le := λ p q r hpr hqr m n hmn hpq, hpq.elim
    (λ hpq, hpr m n hmn hpq) (λ hpq, hqr m n hmn hpq),
  ..sprop.partial_order
}

instance : distrib_lattice sprop := {
  le_sup_inf := λ p q r m n hmn h, h.1.elim
    (λ hp, or.inl hp) (λ hq, h.2.elim (λ hp, or.inl hp) (λ hr, or.inr ⟨hq, hr⟩)),
  ..sprop.semilattice_inf,
  ..sprop.semilattice_sup,
}

@[simp] lemma sprop.inf_apply {p q : sprop} {n : ℕ} : (p ⊓ q) n ↔ p n ∧ q n := iff.rfl
@[simp] lemma sprop.sup_apply {p q : sprop} {n : ℕ} : (p ⊔ q) n ↔ p n ∨ q n := iff.rfl

lemma sprop.inf_eq_at {p q r s : sprop} {n : ℕ} : p =[n] q → r =[n] s → p ⊓ r =[n] q ⊓ s :=
λ h₁ h₂ m hmn, and_congr (h₁ m hmn) (h₂ m hmn)

lemma sprop.sup_eq_at {p q r s : sprop} {n : ℕ} : p =[n] q → r =[n] s → p ⊔ r =[n] q ⊔ s :=
λ h₁ h₂ m hmn, or_congr (h₁ m hmn) (h₂ m hmn)

def sprop.incln (p q : sprop) (n : ℕ) := ∀ m ≤ n, p m → q m

notation p ` ⊆[`:50 n `] ` q:50 := p.incln q n

section metric

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

-- TODO: Add the relevant lemmas for fixed-point constructions.

end metric
