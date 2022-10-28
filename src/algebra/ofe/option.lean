import algebra.ofe.basic

universe u

/-!
# OFEs for `option` and `part`
-/

inductive option.eq_at_prop {α : Type u} [ofe α] (n : ℕ) : option α → option α → Prop
| some : Π {a b : α}, a =[n] b → option.eq_at_prop (some a) (some b)
| none : option.eq_at_prop none none

instance {α : Type u} [ofe α] : ofe (option α) := {
  eq_at := option.eq_at_prop,
  eq_at_reflexive := begin
    intros n x,
    cases x,
    exact option.eq_at_prop.none,
    refine option.eq_at_prop.some _,
    refl,
  end,
  eq_at_symmetric := begin
    intros n x y h,
    cases h,
    refine option.eq_at_prop.some _, symmetry, assumption,
    exact option.eq_at_prop.none,
  end,
  eq_at_transitive := begin
    intros n x y z hxy hyz,
    cases hxy,
    case none { cases hyz, exact option.eq_at_prop.none, },
    cases hyz,
    refine option.eq_at_prop.some _,
    transitivity, skip, assumption, assumption,
  end,
  eq_at_mono' := begin
    intros m n hmn x y h,
    cases h,
    case none { exact option.eq_at_prop.none, },
    refine option.eq_at_prop.some _,
    refine eq_at_mono hmn _,
    assumption,
  end,
  eq_at_limit' := begin
    intros x y h,
    cases h 0,
    case none { refl },
    refine congr_arg _ _, rw eq_at_limit,
    intro n, cases h n, assumption,
  end,
}

@[simp] lemma option.some_is_nonexpansive {α : Type u} [ofe α] :
  is_nonexpansive (some : α → option α) :=
λ n x y h, option.eq_at_prop.some h

-- TODO: Refactor this to use an inductive equality.

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
