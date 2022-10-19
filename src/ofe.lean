import order.basic
import category_theory.concrete_category.basic
import category_theory.concrete_category.bundled_hom
import category_theory.closed.cartesian
import topology.category.UniformSpace
import topology.metric_space.contracting

open category_theory

universes u v

/-! https://plv.mpi-sws.org/iris/appendix-4.0.pdf -/

/-- Ordered families of equivalences. -/
structure ofe (α : Type u) :=
(eq_at : ℕ → α → α → Prop)
(eq_at_equiv : ∀ n, equivalence (eq_at n))
(eq_at_mono : antitone eq_at)
(eq_at_limit (x y : α) : x = y ↔ ∀ n, eq_at n x y)

notation a ` =[`:50 α `,` n `] ` b:50 := ofe.eq_at α n a b

@[refl] lemma eq_at_refl {α : Type u} (o : ofe α) (n : ℕ) (x : α) :
  x =[o, n] x := (o.eq_at_equiv n).1 x

@[symm] lemma eq_at_symm {α : Type u} (o : ofe α) (n : ℕ) (x y : α) :
  x =[o, n] y ↔ y =[o, n] x :=
⟨λ h, (o.eq_at_equiv n).2.1 h, λ h, (o.eq_at_equiv n).2.1 h⟩

@[trans] lemma eq_at_trans {α : Type u} (o : ofe α) (n : ℕ) (x y z : α) :
  x =[o, n] y → y =[o, n] z → x =[o, n] z :=
λ hxy hyz, (o.eq_at_equiv n).2.2 hxy hyz

lemma eq_at_trans_not {α : Type u} (o : ofe α) (n : ℕ) (x y z : α) :
  x =[o, n] y → ¬y =[o, n] z → ¬x =[o, n] z :=
begin
  intro h,
  contrapose!,
  rw eq_at_symm at h,
  exact eq_at_trans _ _ _ _ _ h,
end

lemma eq_at_forall_trans {α : Type u} {o : ofe α} {n : ℕ} {x y z : α} :
  x =[o, n] y → ∀ k ≤ n, o.eq_at k x z ↔ o.eq_at k y z :=
begin
  intros hxy k hk,
  split,
  { intro hxz,
    refine eq_at_trans o k y x z _ hxz,
    rw eq_at_symm,
    exact o.eq_at_mono hk x y hxy, },
  { intro hyz,
    refine eq_at_trans o k x y z _ hyz,
    exact o.eq_at_mono hk x y hxy, },
end

lemma eq_at_forall_trans' {α : Type u} {o : ofe α} {n : ℕ} {x y z : α} :
  x =[o, n] y → ¬x =[o, n] z → ∀ k, o.eq_at k x z ↔ o.eq_at k y z :=
begin
  intros hxy hxz k,
  by_cases k ≤ n,
  { exact eq_at_forall_trans hxy k h, },
  rw eq_at_symm at hxy,
  have := eq_at_trans_not o n y x z hxy hxz,
  push_neg at h,
  have h₁ := o.eq_at_mono h.le x z,
  have h₂ := o.eq_at_mono h.le y z,
  split,
  { intro h, cases hxz (h₁ h), },
  { intro h, cases this (h₂ h), },
end

noncomputable def critical_point {α : Type u} {o : ofe α} {x y : α}
  (h : ∃ n, ¬x =[o, n] y) : ℕ :=
@nat.find _ (λ _, classical.dec _) h

lemma critical_point_spec {α : Type u} {o : ofe α} {x y : α} (h : ∃ n, ¬x =[o, n] y) :
  ¬o.eq_at (critical_point h) x y := @nat.find_spec _ (λ _, classical.dec _) h

lemma critical_point_min {α : Type u} {o : ofe α} {x y : α} (h : ∃ n, ¬x =[o, n] y) {m : ℕ} :
  m < critical_point h → o.eq_at m x y :=
λ hm, not_not.mp (@nat.find_min _ (λ _, classical.dec _) h m hm)

lemma critical_point_min' {α : Type u} {o : ofe α} {x y : α} (h : ∃ n, ¬x =[o, n] y)
  {m : ℕ} (hm : ¬o.eq_at m x y) : critical_point h ≤ m :=
@nat.find_min' _ (λ _, classical.dec _) h m hm

lemma exists_ne_of_ne {α : Type u} (o : ofe α) {x y : α} : x ≠ y → ∃ n, ¬x =[o, n] y :=
by contrapose!; exact (o.eq_at_limit x y).mpr

lemma ne_of_exists_ne {α : Type u} (o : ofe α) {x y : α} : (∃ n, ¬x =[o, n] y) → x ≠ y :=
by contrapose!; exact (o.eq_at_limit x y).mp

lemma exists_ne_iff_ne {α : Type u} (o : ofe α) {x y : α} : x ≠ y ↔ ∃ n, ¬x =[o, n] y :=
⟨exists_ne_of_ne o, ne_of_exists_ne o⟩

/-- An equivalent description of the `eq_at` operation on distinct elements
in ordered families of equivalences. -/
lemma eq_at_iff_lt_critical_point {α : Type u} {o : ofe α} {x y : α} (h : x ≠ y)
  {m : ℕ} : o.eq_at m x y ↔ m < critical_point (exists_ne_of_ne o h) :=
begin
  split,
  { intro hm,
    by_contra' this,
    exact critical_point_spec (exists_ne_of_ne o h) (o.eq_at_mono this x y hm), },
  { intro hm,
    by_contra this,
    exact not_le_of_lt hm (critical_point_min' (exists_ne_of_ne o h) this), },
end

lemma critical_point_eq_zero {α : Type u} {o : ofe α} {x y : α} (h : ∃ n, ¬x =[o, n] y) :
  critical_point h = 0 ↔ ∀ n, ¬x =[o, n] y :=
begin
  split,
  { intros hp n hn,
    rw eq_at_iff_lt_critical_point (ne_of_exists_ne o h) at hn,
    generalize_proofs at hn,
    rw hp at hn,
    exact nat.not_lt_zero n hn, },
  { intro hp,
    have := critical_point_min' h (hp 0),
    exact le_zero_iff.mp this, },
end

def Ofe := bundled ofe

instance : has_coe_to_sort Ofe Type* := bundled.has_coe_to_sort

def is_discrete {α : Type u} (o : ofe α) (x : α) : Prop :=
∀ y, o.eq_at 0 x y → x = y

def discrete_ofe (α : Type u) : ofe α := {
  eq_at := λ _, (=),
  eq_at_equiv := λ _, eq_equivalence,
  eq_at_mono := λ _ _ _, le_of_eq rfl,
  eq_at_limit := λ x y, (forall_const ℕ).symm,
}

@[simp] lemma discrete_ofe_eq_at {α : Type u} (x y : α) (n : ℕ) :
  (discrete_ofe α).eq_at n x y ↔ x = y := iff.rfl

lemma discrete_ofe_is_discrete {α : Type u} (x : α) :
  is_discrete (discrete_ofe α) x :=
begin
  intros y h,
  cases h,
  refl,
end

/-- Applying a non-expansive function to some data will not introduce
differences between seemingly equal data. Elements that cannot be distinguished
by programs within `n` steps remain indistinguishable after applying `f`. -/
def nonexpansive {α β : Type u} (f : α → β) (oα : ofe α) (oβ : ofe β) : Prop :=
∀ n x y, x =[oα, n] y → f x =[oβ, n] f y

def contractive {α β : Type u} (f : α → β) (oα : ofe α) (oβ : ofe β) : Prop :=
∀ n x y, (∀ m < n, x =[oα, m] y) → f x =[oβ, n] f y

lemma nonexpansive_of_contractive {α β : Type u} (f : α → β) (oα : ofe α) (oβ : ofe β) :
  contractive f oα oβ → nonexpansive f oα oβ :=
begin
  intros hf n x y h,
  refine hf n x y _,
  intros m hm,
  exact oα.eq_at_mono hm.le x y h,
end

@[simp] lemma nonexpansive_id {α : Type u} (o : ofe α) :
  nonexpansive id o o :=
λ n x y h, h

@[simp] lemma nonexpansive_comp {α β γ : Type u} (f : β → γ) (g : α → β)
  (oα : ofe α) (oβ : ofe β) (oγ : ofe γ) :
  nonexpansive f oβ oγ → nonexpansive g oα oβ → nonexpansive (f ∘ g) oα oγ :=
λ hf hg n x y h, hf n (g x) (g y) (hg n x y h)

@[ext] structure nonexpansive_fun (α β : Ofe) :=
(to_fun : α → β)
(prop : nonexpansive to_fun α.str β.str)

instance nonexpansive_fun_like {α β : Ofe} : fun_like (nonexpansive_fun α β) α (λ _, β) := {
  coe := nonexpansive_fun.to_fun,
  coe_injective' := begin intros f g h, ext1, exact h, end,
}

infixr ` →ₙₑ `:25 := nonexpansive_fun

@[simp] lemma to_fun_eq_coe_fn {α β : Ofe} (f : α →ₙₑ β) : f.to_fun = ⇑f := rfl
@[simp] lemma coe_fn_mk {α β : Ofe} (f : α → β) (h : nonexpansive f α.str β.str) :
  ⇑{ nonexpansive_fun . to_fun := f,prop := h } = f := rfl

lemma critical_point_nonexpansive {α β : Ofe} (x y : α) (f : α → β)
  (hf : nonexpansive f α.str β.str) (hxy : f x ≠ f y) :
  critical_point (exists_ne_of_ne α.str (ne_of_apply_ne f hxy)) ≤
    critical_point (exists_ne_of_ne β.str hxy) :=
begin
  refine critical_point_min' _ _,
  intro h,
  have := hf (critical_point _) x y h,
  exact critical_point_spec _ this,
end

lemma critical_point_contractive {α β : Ofe} (x y : α) (f : α → β)
  (hf : contractive f α.str β.str) (hxy : f x ≠ f y) :
  critical_point (exists_ne_of_ne α.str (ne_of_apply_ne f hxy)) <
    critical_point (exists_ne_of_ne β.str hxy) :=
begin
  rw ← eq_at_iff_lt_critical_point,
  refine hf (critical_point _) x y _,
  intros m hm,
  rw eq_at_iff_lt_critical_point,
  exact hm,
end

instance : quiver Ofe := {
  hom := nonexpansive_fun,
}

instance : category_struct Ofe := {
  id := λ α, ⟨id, nonexpansive_id α.str⟩,
  comp := λ α β γ f g, ⟨g ∘ f,
    nonexpansive_comp g f α.str β.str γ.str g.prop f.prop⟩
}

instance : category Ofe := {}

@[simp] lemma coe_comp' {α β γ : Ofe} (f : α ⟶ β) (g : β ⟶ γ) :
  (f ≫ g : α → γ) = (g : β → γ) ∘ (f : α → β) := rfl

instance : concrete_category Ofe := {
  forget := {
    obj := coe_sort,
    map := λ _ _, coe_fn,
  },
  forget_faithful := ⟨λ α β f g h, fun_like.coe_injective h⟩,
}

notation a ` =[`:50 n `] ` b:50 := (bundled.str _ : ofe _).eq_at n a b

/-! `Ofe` is bicartesian closed: it has all sums, products and exponentials, as well as an
initial and terminal object. -/

def binary_product_ofe {α β : Type u} (oα : ofe α) (oβ : ofe β) : ofe (α × β) := {
  eq_at := λ n x y, x.1 =[oα, n] y.1 ∧ x.2 =[oβ, n] y.2,
  eq_at_equiv := begin
    intro n,
    refine ⟨_, _, _⟩,
    { intro x,
      split;
      refl, },
    { intros x y h,
      exact ⟨(oα.eq_at_equiv n).2.1 h.1, (oβ.eq_at_equiv n).2.1 h.2⟩, },
    { intros x y z hxy hyz,
      exact ⟨(oα.eq_at_equiv n).2.2 hxy.1 hyz.1, (oβ.eq_at_equiv n).2.2 hxy.2 hyz.2⟩, },
  end,
  eq_at_mono := begin
    intros m n hmn x y h,
    exact ⟨oα.eq_at_mono hmn x.1 y.1 h.1, oβ.eq_at_mono hmn x.2 y.2 h.2⟩,
  end,
  eq_at_limit := begin
    intros x y,
    split,
    { rintro rfl n,
      split;
      refl, },
    intro h,
    ext1,
    { rw oα.eq_at_limit,
      exact λ n, (h n).1, },
    { rw oβ.eq_at_limit,
      exact λ n, (h n).2, },
  end,
}

def product (J : Type v) (o : J → Ofe.{u}) : Ofe.{max u v} := {
  α := Π (j : J), o j,
  str := {
    eq_at := λ n x y, ∀ j : J, x j =[n] y j,
    eq_at_equiv := begin
      intro n,
      refine ⟨_, _, _⟩,
      { intros x j,
        refl, },
      { intros x y h j,
        rw eq_at_symm,
        exact h j, },
      { intros x y z hxy hyz j,
        exact eq_at_trans (o j).str n (x j) (y j) (z j) (hxy j) (hyz j), },
    end,
    eq_at_mono := begin
      intros m n hmn x y hxy j,
      exact (o j).str.eq_at_mono hmn (x j) (y j) (hxy j),
    end,
    eq_at_limit := begin
      intros x y,
      split,
      { rintro rfl n j, refl, },
      intro h,
      ext j,
      rw (o j).str.eq_at_limit (x j) (y j),
      exact λ n, h n j,
    end,
  },
}

def product_cone (J : Type v) (F : discrete J ⥤ Ofe) : limits.limit_cone F := {
  cone := ⟨product (discrete J) F.obj, begin
    refine ⟨_, _⟩,
    { intro j,
      refine ⟨λ α, α j, _⟩,
      intros n x y h,
      exact h j, },
    { intros j k f,
      cases discrete.ext _ _ (discrete.eq_of_hom f),
      simp only [discrete.functor_map_id, category.id_comp, category.comp_id], },
  end⟩,
  is_limit := begin
    refine ⟨_, _, _⟩,
    { intro s,
      refine ⟨λ α j, s.π.app j α, _⟩,
      intros n x y h j,
      exact (s.π.app j).prop n x y h, },
    { intros s j,
      ext x,
      refl, },
    { intros s f h,
      ext _ j,
      specialize h j,
      dsimp at ⊢,
      rw ← h,
      refl, },
  end
}

instance : limits.has_products Ofe := λ (J : Type v), ⟨λ F, ⟨⟨product_cone J F⟩⟩⟩

instance : limits.has_finite_products.{u u+1} Ofe.{u} :=
@limits.has_finite_products_of_has_products Ofe _ Ofe.category_theory.limits.has_products.{u u}

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

def coproduct (J : Type v) (o : J → Ofe.{u}) : Ofe.{max u v} := {
  α := Σ (j : J), o j,
  str := {
    eq_at := λ n x y, map_or_false (λ a b c, (o a).str.eq_at n b c) x y,
    eq_at_equiv := begin
      classical,
      intro n,
      refine ⟨_, _, _⟩,
      { intro x,
        rw map_or_false_self, },
      { rintros ⟨x₁, x₂⟩ ⟨y₁, y₂⟩,
        unfold map_or_false,
        by_cases x₁ = y₁,
        { cases h,
          rw [dif_pos h, dif_pos h],
          intro h,
          exact ((o x₁).str.eq_at_equiv n).2.1 h, },
        { rw [dif_neg h, false_implies_iff],
          trivial, }, },
      { rintros ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨z₁, z₂⟩,
        unfold map_or_false,
        by_cases x₁ = y₁,
        { cases h,
          rw dif_pos h,
          by_cases x₁ = z₁,
          { cases h,
            rw [dif_pos h, dif_pos h],
            intros h₁ h₂,
            exact ((o x₁).str.eq_at_equiv n).2.2 h₁ h₂, },
          { rw [dif_neg h, false_implies_iff, implies_true_iff],
            trivial, }, },
        { rw [dif_neg h, false_implies_iff],
          trivial, }, },
    end,
    eq_at_mono := begin
      unfold map_or_false,
      rintros m n hmn ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ hxy,
      by_cases x₁ = y₁,
      { cases h,
        rw dif_pos h at hxy ⊢,
        exact (o x₁).str.eq_at_mono hmn _ _ hxy, },
      { rw dif_neg h at hxy ⊢,
        exact hxy, },
    end,
    eq_at_limit := begin
      rintros ⟨x₁, x₂⟩ ⟨y₁, y₂⟩,
      split,
      { intros h n,
        cases h,
        rw map_or_false_self, },
      { intro hxy,
        unfold map_or_false at hxy,
        by_cases x₁ = y₁,
        { cases h,
          simp only [eq_self_iff_true, heq_iff_eq, true_and],
          rw (o x₁).str.eq_at_limit,
          intro n,
          simp_rw dif_pos at hxy,
          exact hxy n, },
        { have := hxy 0,
          split_ifs at this with hx₁ hx₁,
          { cases h hx₁, },
          { cases this, }, }, },
    end,
  },
}

lemma coproduct_eq_at (J : Type v) (o : J → Ofe.{u}) :
  (coproduct J o).str.eq_at = λ n x y, map_or_false (λ a b c, (o a).str.eq_at n b c) x y := rfl

def coproduct_cocone (J : Type v) (F : discrete J ⥤ Ofe) : limits.colimit_cocone F := {
  cocone := ⟨coproduct (discrete J) F.obj, begin
    refine ⟨λ j, ⟨sigma.mk j, _⟩, _⟩,
    { intros n x y h,
      dsimp,
      rw [coproduct_eq_at, map_or_false_mk],
      exact h, },
    { intros α β f,
      cases discrete.ext _ _ (discrete.eq_of_hom f),
      simp only [discrete.functor_map_id, category.id_comp, category.comp_id], },
  end⟩,
  is_colimit := begin
    refine ⟨_, _, _⟩,
    { intro s,
      refine ⟨λ a, s.ι.app a.fst a.snd, _⟩,
      rintros n ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h,
      rw coproduct_eq_at at h,
      cases map_or_false_implies h,
      rw map_or_false_mk at h,
      exact (s.ι.app x₁).prop n x₂ y₂ h, },
    { intros s j,
      ext x,
      simp only [to_fun_eq_coe_fn, coe_comp', coe_fn_mk], },
    { intros s f h,
      ext x,
      simp only [to_fun_eq_coe_fn, ← h x.fst, coe_comp',
        coe_fn_mk, function.comp_app, sigma.eta], },
  end,
}

instance : limits.has_coproducts Ofe := λ (J : Type v), ⟨λ F, ⟨⟨coproduct_cocone J F⟩⟩⟩

instance : limits.has_finite_coproducts.{u u+1} Ofe.{u} :=
@limits.has_finite_coproducts_of_has_coproducts Ofe _ Ofe.category_theory.limits.has_coproducts.{u u}

noncomputable def product_iso_prod (α β : Ofe) :
  (α ⨯ β) ≅ (product_cone _ (limits.pair α β)).cone.X :=
limits.limit.iso_limit_cone _

noncomputable def coproduct_iso_coprod (α β : Ofe) :
  (α ⨿ β) ≅ (coproduct_cocone _ (limits.pair α β)).cocone.X :=
limits.colimit.iso_colimit_cocone _

@[simp] lemma prod_eq_at {α β : Ofe.{u}} (n : ℕ) (x y : α ⨯ β) :
  x =[n] y ↔
    @limits.prod.fst Ofe _ α β _ x =[n] @limits.prod.fst Ofe _ α β _ y ∧
    @limits.prod.snd Ofe _ α β _ x =[n] @limits.prod.snd Ofe _ α β _ y :=
begin
  split,
  { intro h,
    exact ⟨(@limits.prod.fst Ofe _ α β _).prop n x y h,
      (@limits.prod.snd Ofe _ α β _).prop n x y h⟩, },
  rintro ⟨hα, hβ⟩,
  convert ((limits.prod_is_prod α β).lift (product_cone _ (limits.pair α β)).cone).prop
    n ((product_iso_prod α β).hom x) ((product_iso_prod α β).hom y) _,
  { exact (congr_hom (product_iso_prod α β).hom_inv_id x).symm, },
  { exact (congr_hom (product_iso_prod α β).hom_inv_id y).symm, },
  { rintro (p | p),
    exact hα,
    exact hβ, },
end

@[simp] lemma prod_ext {α β : Ofe} (x y : α ⨯ β) :
  x = y ↔
    @limits.prod.fst Ofe _ α β _ x = @limits.prod.fst Ofe _ α β _ y ∧
    @limits.prod.snd Ofe _ α β _ x = @limits.prod.snd Ofe _ α β _ y :=
begin
  rw [(α ⨯ β).str.eq_at_limit, α.str.eq_at_limit, β.str.eq_at_limit],
  simp only [prod_eq_at],
  finish,
end

-- coprod eq at, coprod ext

def const_fun (α : Ofe) {β : Ofe} (x : β) : α →ₙₑ β :=
⟨function.const α x, by intros n y z h; refl⟩

def discretise : Ofe ⥤ Ofe := {
  obj := λ α, ⟨α, discrete_ofe α⟩,
  map := λ α β f, ⟨f, by intros n x y h; cases h; refl⟩,
}

def exp (α β : Ofe) : Ofe := {
  α := β ⟶ α,
  str := {
    eq_at := λ n f g, ∀ x, f x =[n] g x,
    eq_at_equiv := begin
      intro n,
      refine ⟨_, _, _⟩,
      { intros f x,
        refl, },
      { intros f g h x,
        rw eq_at_symm,
        exact h x, },
      { intros f g h hfg hgh x,
        exact eq_at_trans _ _ _ _ _ (hfg x) (hgh x), },
    end,
    eq_at_mono := begin
      intros m n hmn f g hfg x,
      exact α.str.eq_at_mono hmn _ _ (hfg x),
    end,
    eq_at_limit := begin
      intros f g,
      split,
      { rintro rfl n j, refl, },
      intro h,
      ext x,
      have := α.str.eq_at_limit (f x) (g x),
      rw [to_fun_eq_coe_fn, to_fun_eq_coe_fn, this],
      exact λ n, h n x,
    end,
  }
}

def exp_functor (α : Ofe) : Ofe ⥤ Ofe := {
  obj := λ β, exp β α,
  map := λ β γ f, ⟨λ g, ⟨f.to_fun ∘ g.to_fun,
    nonexpansive_comp f.to_fun g.to_fun _ β.str _ f.prop g.prop⟩,
    λ n x y h a, f.prop n _ _ (h a)⟩,
  map_id' := by intro; ext; refl,
  map_comp' := by intros; refl,
}

lemma exp_functor_map (α : Ofe) {β γ : Ofe} :
  ((exp_functor α).map : (β ⟶ γ) → (exp β α ⟶ exp γ α)) = λ f, ⟨λ g, ⟨f.to_fun ∘ g.to_fun,
    nonexpansive_comp f.to_fun g.to_fun _ β.str _ f.prop g.prop⟩,
    λ n x y h a, f.prop n _ _ (h a)⟩ := rfl

noncomputable def exp_const (α β : Ofe) : β ⟶ (exp_functor α).obj (α ⨯ β) := {
  to_fun := λ b, (limits.prod.lift (𝟙 α) (const_fun α b)),
  prop := begin
    intros n x y hxy a,
    refine (prod_eq_at n _ _).mpr ⟨_, _⟩,
    { convert (α.str.eq_at_equiv n).1 _ using 1,
      rw [← comp_apply, ← comp_apply, limits.prod.lift_fst, limits.prod.lift_fst], },
    { convert hxy using 1,
      rw [← comp_apply, limits.prod.lift_snd],
      refl,
      rw [← comp_apply, limits.prod.lift_snd],
      refl, },
  end,
}

noncomputable def exp_eval (α β : Ofe) : α ⨯ (exp_functor α).obj β ⟶ β := {
  to_fun := λ x, ((limits.prod.snd : α ⨯ _ ⟶ (exp_functor α).obj β) x).to_fun
    ((limits.prod.fst : α ⨯ _ ⟶ α) x),
  prop := begin
    intros n x y hxy,
    rw prod_eq_at at hxy,
    have h₁ := ((limits.prod.snd : α ⨯ _ ⟶ (exp_functor α).obj β) x).prop n
      ((limits.prod.fst : α ⨯ _ ⟶ α) x) ((limits.prod.fst : α ⨯ _ ⟶ α) y) hxy.1,
    have h₂ := hxy.2 ((limits.prod.fst : α ⨯ _ ⟶ α) y),
    exact (β.str.eq_at_equiv n).2.2 h₁ h₂,
  end,
}

noncomputable instance : cartesian_closed Ofe.{u} :=
begin
  split,
  intro α,
  split,
  refine ⟨_, _⟩,
  { exact exp_functor α, },
  refine_struct { .. },
  { intros β γ,
    refine ⟨_, _, _, _⟩,
    { intro h,
      refine exp_const α β ≫ _,
      exact ⟨λ f, f ≫ h, λ n x y hxy a, h.prop n _ _ (hxy a)⟩, },
    { intro h,
      refine ⟨λ b, (h (@limits.prod.snd Ofe _ α β _ b)).to_fun
        (@limits.prod.fst Ofe _ α β _ b), _⟩,
      intros n x y hxy,
      obtain ⟨hα, hβ⟩ := (prod_eq_at n x y).mp hxy,
      have h₁ := (h (@limits.prod.snd Ofe _ α β _ x)).prop n
        (@limits.prod.fst Ofe _ α β _ x) (@limits.prod.fst Ofe _ α β _ y) hα,
      have h₂ := h.prop n (@limits.prod.snd Ofe _ α β _ x) (@limits.prod.snd Ofe _ α β _ y) hβ
        (@limits.prod.fst Ofe _ α β _ y),
      exact (γ.str.eq_at_equiv n).2.2 h₁ h₂, },
    { intro f,
      ext x,
      simp only [coe_fn_mk, to_fun_eq_coe_fn, coe_comp', function.comp_app],
      refine congr_arg _ _,
      rw [prod_ext, exp_const],
      split,
      { rw ← comp_apply, simp only [coe_fn_mk, limits.prod.lift_fst, id_apply], },
      { rw ← comp_apply, simp only [coe_fn_mk, limits.prod.lift_snd], refl, }, },
    { intro f,
      ext x y,
      simp only [to_fun_eq_coe_fn, coe_comp', coe_fn_mk, function.comp_app],
      rw [← comp_apply, ← comp_apply, ← comp_apply, ← comp_apply, exp_const],
      simp only [coe_fn_mk, limits.prod.lift_snd_assoc, coe_comp', function.comp_app,
        limits.prod.lift_fst_assoc, category.id_comp],
      refl, }, },
  { refine ⟨exp_const α, _⟩,
    intros β γ f,
    simp only [functor.id_map, functor.comp_map, monoidal_category.tensor_left_map,
      monoidal_of_has_finite_products.tensor_hom],
    ext x y,
    simp only [to_fun_eq_coe_fn, coe_comp', function.comp_app, exp_const, coe_fn_mk,
      const_fun, prod_ext],
    split,
    { rw [← comp_apply, ← comp_apply],
      simp only [limits.prod.lift_fst, id_apply, coe_comp', function.comp_app],
      rw exp_functor_map,
      simp only [to_fun_eq_coe_fn, coe_fn_mk, function.comp_app],
      rw [← comp_apply, ← comp_apply],
      simp only [limits.prod.map_fst, category.comp_id, limits.prod.lift_fst, id_apply], },
    { rw [← comp_apply, ← comp_apply],
      simp only [limits.prod.lift_snd, coe_comp', function.comp_app, coe_fn_mk, function.const_apply],
      rw exp_functor_map,
      simp only [to_fun_eq_coe_fn, coe_fn_mk, function.comp_app],
      rw [← comp_apply, ← comp_apply],
      simp only [limits.prod.map_snd, limits.prod.lift_snd_assoc, coe_comp', coe_fn_mk], }, },
  { refine ⟨exp_eval α, _⟩,
    intros β γ f,
    simp only [functor.comp_map, monoidal_category.tensor_left_map,
      monoidal_of_has_finite_products.tensor_hom, functor.id_map],
    ext x,
    simp only [to_fun_eq_coe_fn, coe_comp', function.comp_app],
    rw [exp_eval, exp_eval],
    simp only [to_fun_eq_coe_fn, coe_fn_mk],
    rw [← comp_apply, ← comp_apply, ← comp_apply, ← comp_apply, ← comp_apply],
    simp only [limits.prod.map_snd, coe_comp', function.comp_app,
      limits.prod.map_fst_assoc, category.id_comp],
    refl, },
  { intros β γ f, refl, },
  { intros β γ f,
    simp only [monoidal_category.tensor_left_map, monoidal_of_has_finite_products.tensor_hom,
      to_fun_eq_coe_fn, equiv.coe_fn_symm_mk],
    rw exp_eval,
    ext x,
    rw [to_fun_eq_coe_fn, coe_fn_mk, ← comp_apply, ← comp_apply],
    simp only [coe_comp', function.comp_app, to_fun_eq_coe_fn, coe_fn_mk],
    rw [← comp_apply, ← comp_apply, ← comp_apply, ← comp_apply, ← comp_apply],
    simp only [limits.prod.map_snd, limits.prod.map_fst_assoc, category.id_comp], },
end

instance terminal_unique (α : Ofe) : unique (α ⟶ product pempty pempty.elim) := {
  default := ⟨λ a b, b.elim, λ n x y h b, b.elim⟩,
  uniq := begin
    intro f,
    ext x b,
    exact b.elim,
  end,
}

instance : limits.has_terminal Ofe := limits.has_terminal_of_unique (product pempty pempty.elim)

instance initial_unique (α : Ofe) : unique (coproduct pempty pempty.elim ⟶ α) := {
  default := ⟨λ a, a.fst.elim, λ n x, x.fst.elim⟩,
  uniq := begin
    intro f,
    ext x b,
    exact x.fst.elim,
  end,
}

instance : limits.has_initial Ofe := limits.has_initial_of_unique (coproduct pempty pempty.elim)

def locally_nonexpansive_functor (F : Ofe ⥤ Ofe) : Prop :=
∀ α β : Ofe, nonexpansive (F.map : (α ⟶ β) → (F.obj α ⟶ F.obj β))
  (exp β α).str (exp (F.obj β) (F.obj α)).str

def locally_contractive_functor (F : Ofe ⥤ Ofe) : Prop :=
∀ α β : Ofe, contractive (F.map : (α ⟶ β) → (F.obj α ⟶ F.obj β))
  (exp β α).str (exp (F.obj β) (F.obj α)).str

/-! Note that `internal_hom` is the bifunctor mapping pairs `(α, β)` to `α →ₙₑ β` as an OFE. -/

-- TODO: What does it mean to be locally nonexpansive as a bifunctor?

@[ext] structure chain (α : Type u) (eq_at : ℕ → α → α → Prop) :=
(c : ℕ → α)
(prop : ∀ m n, m ≤ n → eq_at m (c m) (c n))

instance chain.fun_like (α : Type u) (eq_at : ℕ → α → α → Prop) :
  fun_like (chain α eq_at) ℕ (λ _, α) := {
  coe := chain.c,
  coe_injective' := λ p q h, by ext1; exact h,
}

structure cofe (α : Type u) extends ofe α :=
(lim : chain α eq_at → α)
(complete : ∀ n c, eq_at n (lim c) (c n))

def Cofe := bundled cofe

instance : has_coe_to_sort Cofe Type* := bundled.has_coe_to_sort

instance : quiver Cofe := {
  hom := λ α β, nonexpansive_fun ⟨α, α.str.to_ofe⟩ ⟨β, β.str.to_ofe⟩,
}

instance : category_struct Cofe := {
  id := λ α, ⟨id, nonexpansive_id α.str.to_ofe⟩,
  comp := λ α β γ f g, ⟨g ∘ f,
    nonexpansive_comp g f α.str.to_ofe β.str.to_ofe γ.str.to_ofe g.prop f.prop⟩
}

instance : category Cofe := {}

instance : concrete_category Cofe := {
  forget := {
    obj := coe_sort,
    map := λ _ _, coe_fn,
  },
  forget_faithful := ⟨λ α β f g h, fun_like.coe_injective h⟩,
}

instance has_forget_to_Ofe : has_forget₂ Cofe Ofe := {
  forget₂ := {
    obj := λ α, ⟨α, α.str.to_ofe⟩,
    map := λ α β, id,
  },
}

instance : has_coe Cofe Ofe :=
{ coe := (forget₂ Cofe Ofe).obj, }

/-- A *step-indexed proposition* is a proposition at each time step `n : ℕ`, such that if `p n`,
we must have `p m` for all `m ≤ n`. -/
@[ext] structure {u'} step_indexed_prop : Type u' :=
(p : ℕ → Prop)
(prop : antitone p)

instance step_indexed_prop.fun_like : fun_like step_indexed_prop.{u} ℕ (λ _, Prop) := {
  coe := step_indexed_prop.p,
  coe_injective' := λ p q h, by ext1; exact h,
}

def SProp : Cofe.{u} := {
  α := step_indexed_prop,
  str := {
    eq_at := λ n p q, ∀ m ≤ n, p m ↔ q m,
    eq_at_equiv := begin
      intro n,
      refine ⟨_, _, _⟩,
      { intros p m h,
        refl, },
      { intros p q h m hm,
        exact iff.symm (h m hm), },
      { intros p q r hpq hqr m hm,
        exact iff.trans (hpq m hm) (hqr m hm), },
    end,
    eq_at_mono := begin
      intros m n hm p q h k hk,
      refine h k _,
      exact le_trans hk hm,
    end,
    eq_at_limit := begin
      intros p q,
      split,
      { rintros rfl m n h,
        refl, },
      { intro h,
        ext n,
        exact h n n le_rfl, },
    end,
    lim := λ c, ⟨λ n, c n n,
      λ m n hmn h, (c.prop m n hmn m le_rfl).mpr ((c n).prop hmn h)⟩,
    complete := λ n c m hmn, c.prop m n hmn m le_rfl,
  }
}

instance : has_le SProp := ⟨λ p q, ∀ m n, m ≤ n → p.p m → q.p m⟩

instance : partial_order SProp := {
  le_refl := λ a m n h, id,
  le_trans := λ p q r hpq hqr m n h, (hqr m n h) ∘ (hpq m n h),
  le_antisymm := λ a b h₁ h₂, by ext n; exact ⟨h₁ n n le_rfl, h₂ n n le_rfl⟩,
  ..SProp.has_le
}

instance : has_le (↑SProp.{u} : Ofe.{u}) := SProp.has_le
instance : partial_order (↑SProp.{u} : Ofe.{u}) := SProp.partial_order

def SProp.incln (p q : SProp) (n : ℕ) := ∀ m ≤ n, p.p m → q.p m

def ofe_with_bot : Ofe ⥤ Ofe := {
  obj := λ α, ⟨with_bot α, {
    eq_at := λ n a, @with_bot.rec_bot_coe _ (λ _, Prop) (a = ⊥)
      (λ b, @with_bot.rec_bot_coe _ (λ _, Prop) false (λ a, a =[n] b) a),
    eq_at_equiv := begin
      intro n,
      refine ⟨_, _, _⟩,
      { intro a,
        induction a using with_bot.rec_bot_coe,
        { rw with_bot.rec_bot_coe_bot, },
        { rw [with_bot.rec_bot_coe_coe, with_bot.rec_bot_coe_coe], }, },
      { intros a b h,
        induction a using with_bot.rec_bot_coe,
        { rw with_bot.rec_bot_coe_bot,
          induction b using with_bot.rec_bot_coe,
          { refl, },
          { cases h, }, },
        { rw with_bot.rec_bot_coe_coe,
          induction b using with_bot.rec_bot_coe,
          { cases h, },
          { simp only [with_bot.rec_bot_coe_coe] at h ⊢,
            rw eq_at_symm,
            exact h, }, }, },
      { intros a b c hab hbc,
        induction c using with_bot.rec_bot_coe,
        { rw with_bot.rec_bot_coe_bot,
          induction a using with_bot.rec_bot_coe,
          { refl, },
          { cases hbc,
            cases hab, }, },
        { induction a using with_bot.rec_bot_coe,
          { induction b using with_bot.rec_bot_coe,
            cases hab,
            cases hbc,
            cases hab, },
          { induction b using with_bot.rec_bot_coe,
            cases hab,
            exact eq_at_trans _ n _ _ _ hab hbc, }, }, },
    end,
    eq_at_mono := begin
      intros m n hmn a b h,
      induction b using with_bot.rec_bot_coe,
      { exact h, },
      induction a using with_bot.rec_bot_coe,
      { exact h, },
      exact α.str.eq_at_mono hmn a b h,
    end,
    eq_at_limit := begin
      intros a b,
      split,
      { rintros rfl n,
        induction a using with_bot.rec_bot_coe,
        { rw with_bot.rec_bot_coe_bot, },
        exact (α.str.eq_at_limit a a).mp rfl n, },
      intro h,
      induction b using with_bot.rec_bot_coe,
      { exact h 0, },
      induction a using with_bot.rec_bot_coe,
      { cases h 0, },
      rw [with_bot.coe_eq_coe, α.str.eq_at_limit],
      exact h,
    end,
  }⟩,
  map := λ α β f, ⟨with_bot.map f, begin
    intros n a b h,
    induction b using with_bot.rec_bot_coe,
    { cases h,
      refl, },
    induction a using with_bot.rec_bot_coe,
    { cases h, },
    exact f.prop n a b h,
  end⟩,
  map_id' := begin
    intro α,
    ext1, ext1 a,
    induction a using with_bot.rec_bot_coe,
    refl,
    refl,
  end,
  map_comp' := begin
    intros α β γ f g,
    ext1, ext1 a,
    induction a using with_bot.rec_bot_coe,
    refl,
    refl,
  end,
}

instance (α : Ofe) : has_bot (ofe_with_bot.obj α) := ⟨(⊥ : with_bot α)⟩

section metric

noncomputable theory
open_locale classical

def ofe_dist {α : Type u} (o : ofe α) (a b : α) : ℝ :=
⨅ (n : ℕ), if a =[o, n] b then (2 ^ n)⁻¹ else 2

lemma ofe_dist_bdd_below {α : Type u} (o : ofe α) (a b : α) :
  bdd_below (set.range (λ n, if a =[o, n] b then ((2 : ℝ) ^ n)⁻¹ else 2)) :=
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

lemma ofe_dist_le' {α : Type u} (o : ofe α) (a b : α) (n : ℕ) :
  ofe_dist o a b ≤ if a =[o, n] b then (2 ^ n)⁻¹ else 2 :=
cinfi_le (ofe_dist_bdd_below o a b) _

lemma ofe_dist_le {α : Type u} (o : ofe α) (a b : α) (n : ℕ) (h : a =[o, n] b) :
  ofe_dist o a b ≤ (2 ^ n)⁻¹ :=
begin
  have := ofe_dist_le' o a b n,
  rw if_pos h at this,
  exact this,
end

lemma ofe_dist_le_two {α : Type u} (o : ofe α) (a b : α) :
  ofe_dist o a b ≤ 2 :=
begin
  refine le_trans (ofe_dist_le' o a b 0) _,
  split_ifs,
  { norm_num, },
  { refl, },
end

lemma le_ofe_dist' {α : Type u} (o : ofe α) (a b : α) (r : ℝ)
  (h : ∀ n, r ≤ if a =[o, n] b then (2 ^ n)⁻¹ else 2) :
  r ≤ ofe_dist o a b :=
le_cinfi h

lemma le_ofe_dist {α : Type u} (o : ofe α) (a b : α) (r : ℝ)
  (h₁ : ∀ n, a =[o, n] b → r ≤ (2 ^ n)⁻¹) (h₂ : r ≤ 2) :
  r ≤ ofe_dist o a b :=
begin
  refine le_ofe_dist' o a b r _,
  intro n,
  split_ifs,
  exact h₁ n h,
  exact h₂,
end

lemma ofe_dist_eq_one {α : Type u} (o : ofe α) {a b : α} (h : a ≠ b) :
  critical_point (exists_ne_of_ne o h) = 0 → ofe_dist o a b = 2 :=
begin
  intro hp,
  rw critical_point_eq_zero at hp,
  unfold ofe_dist,
  convert cinfi_const,
  { ext n,
    rw if_neg (hp n), },
  { apply_instance, },
end

lemma ofe_dist_eq_of_ne {α : Type u} (o : ofe α) {a b : α} (h : a ≠ b) :
  ofe_dist o a b = 2 * (2 ^ critical_point (exists_ne_of_ne o h))⁻¹ :=
begin
  have := critical_point_spec (exists_ne_of_ne o h),
  refine le_antisymm _ _,
  { generalize hp : critical_point (exists_ne_of_ne o h) = p,
    cases p,
    { rw ofe_dist_eq_one o h hp,
      norm_num, },
    { refine le_of_le_of_eq (ofe_dist_le o a b p _) _,
      { rw eq_at_iff_lt_critical_point h,
        rw hp,
        exact lt_add_one p, },
      { rw [pow_succ, mul_inv],
        simp only [mul_inv_cancel_left₀, ne.def,
          bit0_eq_zero, one_ne_zero, not_false_iff], }, }, },
  { refine le_ofe_dist o a b _ _ _,
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

lemma lt_ofe_dist {α : Type u} (o : ofe α) (a b : α) (n : ℕ) (h : ¬a =[o, n] b) :
  (2 ^ n)⁻¹ < ofe_dist o a b :=
begin
  rw ofe_dist_eq_of_ne o (ne_of_exists_ne o ⟨n, h⟩),
  obtain ⟨k, hk⟩ := le_iff_exists_add.mp (critical_point_min' ⟨n, h⟩ h),
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

lemma ofe_dist_nonneg {α : Type u} (o : ofe α) (a b : α) :
  0 ≤ ofe_dist o a b :=
begin
  refine le_ofe_dist o a b 0 _ zero_le_two,
  intros n h,
  rw inv_nonneg,
  exact pow_nonneg zero_le_two _,
end

lemma ofe_dist_le_of_eq_at {α : Type u} (o : ofe α) {a b c d : α} :
  (∀ n, a =[o, n] b → c =[o, n] d) → ofe_dist o c d ≤ ofe_dist o a b :=
begin
  intro h,
  refine le_ofe_dist _ _ _ _ _ (ofe_dist_le_two o c d),
  intros n hab,
  exact ofe_dist_le o c d n (h n hab),
end

lemma ofe_dist_eq_of_eq_at {α : Type u} (o : ofe α) {a b c d : α} :
  (∀ n, a =[o, n] b ↔ c =[o, n] d) → ofe_dist o a b = ofe_dist o c d :=
begin
  intro h,
  refine le_antisymm _ _,
  { exact ofe_dist_le_of_eq_at o (λ n, (h n).mpr), },
  { exact ofe_dist_le_of_eq_at o (λ n, (h n).mp), },
end

/-- Ordered families of equivalences induce a metric space. -/
def ofe_to_metric_space {α : Type u} (o : ofe α) : metric_space α := {
  dist := ofe_dist o,
  dist_self := begin
    intro a,
    refine le_antisymm _ (ofe_dist_nonneg o a a),
    have : ∀ n, ofe_dist o a a ≤ (2 ^ n)⁻¹,
    { intro n,
      refine ofe_dist_le o a a _ _,
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
    rw (o.eq_at_equiv n).2.1.iff,
  end,
  dist_triangle := begin
    intros x y z,
    unfold dist,
    by_contra',
    rw ← lt_sub_iff_add_lt at this,
    obtain ⟨n, hn⟩ := exists_lt_of_cinfi_lt this,
    dsimp only at hn,
    split_ifs at hn with hxy,
    { by_cases hxz : x =[o, n] z,
      { have := ofe_dist_le o x z n hxz,
        have := ofe_dist_nonneg o y z,
        linarith, },
      by_cases hyz : y =[o, n] z,
      { exact hxz ((o.eq_at_equiv n).2.2 hxy hyz), },
      suffices : ofe_dist o x z = ofe_dist o y z,
      { rw [this, sub_self, inv_lt_zero] at hn,
        refine not_le_of_lt hn _,
        exact pow_nonneg zero_le_two _, },
      by_cases hz : ∃ m, x =[o, m] z,
      { obtain ⟨m, hxz'⟩ := hz,
        by_cases h : n ≤ m,
        { cases hxz (o.eq_at_mono h x z hxz'), },
        push_neg at h,
        have hxy' := o.eq_at_mono h.le x y hxy,
        exact ofe_dist_eq_of_eq_at o (eq_at_forall_trans' hxy hxz), },
      { push_neg at hz,
        refine ofe_dist_eq_of_eq_at o _,
        intro m,
        split,
        { intro h,
          cases hz m h, },
        { intro h,
          have h₁ := o.eq_at_mono (min_le_right m n) x y hxy,
          have h₂ := o.eq_at_mono (min_le_left m n) y z h,
          cases hz _ ((o.eq_at_equiv (min m n)).2.2 h₁ h₂), }, }, },
    { have := ofe_dist_le_two o x z,
      have := ofe_dist_nonneg o y z,
      linarith, },
  end,
  eq_of_dist_eq_zero := begin
    intros a b h,
    rw o.eq_at_limit a b,
    intro n,
    by_contra hxy,
    have := lt_ofe_dist o a b n hxy,
    unfold dist at h,
    rw h at this,
    refine not_le_of_lt this _,
    rw inv_nonneg,
    exact pow_nonneg zero_le_two _,
  end,
}

instance Ofe_to_metric_space (α : Ofe) : metric_space α :=
ofe_to_metric_space α.str

lemma Ofe_dist_eq_of_ne {α : Ofe} {a b : α} (h : a ≠ b) :
  dist a b = 2 * (2 ^ critical_point (exists_ne_of_ne α.str h))⁻¹ :=
ofe_dist_eq_of_ne α.str h

@[simp] lemma Ofe_dist_eq {α : Ofe} {a b : α} :
  dist a b = if h : a = b then 0 else 2 * (2 ^ critical_point (exists_ne_of_ne α.str h))⁻¹ :=
begin
  split_ifs,
  { rw dist_eq_zero,
    exact h, },
  { rw Ofe_dist_eq_of_ne, },
end

instance Cofe_to_metric_space (α : Cofe) : metric_space α :=
ofe_to_metric_space α.str.to_ofe

instance Cofe_to_complete_space (α : Cofe) : complete_space α :=
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
  have hchain : ∀ (m n : ℕ), m ≤ n → α.str.to_ofe.eq_at m (t m) (t n),
  { intros m n hmn,
    have := hs₂ (2 ^ m)⁻¹ (hpow m) (t n) (hts m n hmn) (t m) (hts m m le_rfl),
    by_contra,
    refine not_le_of_lt this _,
    rw dist_comm,
    exact (lt_ofe_dist _ _ _ _ h).le, },
  refine ⟨α.str.lim ⟨t, hchain⟩, _⟩,
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
  refine le_trans (dist_triangle x (t (n + 1)) (α.str.lim ⟨t, hchain⟩)) _,
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
  exact ofe_dist_le _ _ _ _ (α.str.complete (n + 1) ⟨t, hchain⟩),
end

def contractive_is_contracting_with {α : Ofe} (f : α → α) (hf : contractive f α.str α.str) :
  contracting_with (1 / 2) f :=
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
    simp only [dist_self, _root_.mul_zero], },
  rw Ofe_dist_eq_of_ne h,
  rw Ofe_dist_eq,
  split_ifs with hfxy,
  { simp only [one_div, inv_mul_cancel_left₀, ne.def, bit0_eq_zero,
      one_ne_zero, not_false_iff, inv_nonneg, pow_nonneg,
      zero_le_bit0, zero_le_one], },
  have := critical_point_contractive x y f hf hfxy,
  obtain ⟨k, hk⟩ := le_iff_exists_add.mp (nat.succ_le_of_lt this),
  rw hk,
  rw pow_add,
  rw pow_succ,
  rw mul_inv,
  rw mul_inv,
  rw ← mul_assoc,
  rw ← mul_assoc,
  simp only [mul_inv_cancel, ne.def, bit0_eq_zero, one_ne_zero,
    not_false_iff, one_mul, one_div, inv_mul_cancel_left₀,
    mul_le_iff_le_one_right, inv_pos, pow_pos, zero_lt_bit0, zero_lt_one],
  refine inv_le_one _,
  refine one_le_pow_of_one_le one_le_two _,
end

lemma uniform_continuous_of_nonexpansive {α β : Ofe} (f : α ⟶ β) : uniform_continuous f :=
begin
  rw metric.uniform_continuous_iff,
  intros ε hε,
  refine ⟨ε, hε, _⟩,
  intros a b ha,
  by_cases f a = f b,
  { rw h,
    simp only [Ofe_dist_eq, dif_pos],
    exact hε, },
  have := critical_point_nonexpansive a b f f.prop h,
  rw Ofe_dist_eq at ha ⊢,
  rw dif_neg h,
  rw dif_neg (ne_of_apply_ne f h) at ha,
  refine lt_of_le_of_lt _ ha,
  rw mul_le_mul_left,
  rw inv_le_inv,
  refine pow_le_pow _ this,
  exact one_le_two,
  exact pow_pos zero_lt_two _,
  exact pow_pos zero_lt_two _,
  exact zero_lt_two,
end

lemma continuous_of_nonexpansive {α β : Ofe} (f : α ⟶ β) : continuous f :=
(uniform_continuous_of_nonexpansive f).continuous

def Cofe_to_Csus : Cofe ⥤ CpltSepUniformSpace := {
  obj := λ α, ⟨α⟩,
  map := λ α β f, ⟨f, uniform_continuous_of_nonexpansive f⟩,
}

def contractive_fixed_point {α : Cofe} [nonempty α] (f : α → α)
  (hf : contractive f α.str.to_ofe α.str.to_ofe) : α :=
contracting_with.fixed_point f
  (@contractive_is_contracting_with ((forget₂ Cofe Ofe).obj α) f hf)

-- TODO: Add the relevant lemmas for fixed-point constructions.

end metric
