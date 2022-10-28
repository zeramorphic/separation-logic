import algebra.camera.basic

universes u v

@[ext] structure agree_struct (α : Type u) :=
(elts : finset α)
(nonempty : elts.nonempty)

instance agree_struct.has_mem {α : Type u} : has_mem α (agree_struct α) :=
⟨λ x a, x ∈ a.elts⟩

@[simp] lemma agree_struct.has_mem_iff {α : Type u} (x : α) (a : agree_struct α) :
  x ∈ a.elts ↔ x ∈ a := iff.rfl

@[simp] lemma agree_struct.mem_mk {α : Type u} (x : α) (elts : finset α) (nonempty : elts.nonempty) :
  x ∈ (⟨elts, nonempty⟩ : agree_struct α) ↔ x ∈ elts := iff.rfl

structure agree_struct.eq_at {α : Type u} [ofe α] (n : ℕ) (a b : agree_struct α) : Prop :=
(left : ∀ x ∈ a, ∃ y ∈ b, x =[n] y)
(right : ∀ y ∈ b, ∃ x ∈ a, x =[n] y)

lemma agree_struct.eq_at_reflexive {α : Type u} [ofe α] (n : ℕ) :
  reflexive (agree_struct.eq_at n : agree_struct α → agree_struct α → Prop) :=
begin
  intros a,
  split;
  { intros x hx,
    refine ⟨x, hx, _⟩,
    refl, },
end

@[refl] lemma agree_struct.eq_at_refl {α : Type u} [ofe α] {n : ℕ} (a : agree_struct α) :
  agree_struct.eq_at n a a := agree_struct.eq_at_reflexive n a

lemma agree_struct.eq_at_symmetric {α : Type u} [ofe α] (n : ℕ) :
  symmetric (agree_struct.eq_at n : agree_struct α → agree_struct α → Prop) :=
begin
  intros a b hab,
  split,
  { intros x hx,
    obtain ⟨y, hy, h⟩ := hab.right x hx,
    refine ⟨y, hy, _⟩,
    symmetry,
    assumption, },
  { intros x hx,
    obtain ⟨y, hy, h⟩ := hab.left x hx,
    refine ⟨y, hy, _⟩,
    symmetry,
    assumption, },
end

@[symm] lemma agree_struct.eq_at_symm {α : Type u} [ofe α] {n : ℕ} (a b : agree_struct α) :
  agree_struct.eq_at n a b → agree_struct.eq_at n b a := λ h, agree_struct.eq_at_symmetric n h

lemma agree_struct.eq_at_transitive {α : Type u} [ofe α] (n : ℕ) :
  transitive (agree_struct.eq_at n : agree_struct α → agree_struct α → Prop) :=
begin
  intros a b c hab hbc,
  split,
  { intros x hx,
    obtain ⟨y, hy₁, hy₂⟩ := hab.left x hx,
    obtain ⟨z, hz₁, hz₂⟩ := hbc.left y hy₁,
    refine ⟨z, hz₁, _⟩,
    transitivity y; assumption, },
  { intros x hx,
    obtain ⟨y, hy₁, hy₂⟩ := hbc.right x hx,
    obtain ⟨z, hz₁, hz₂⟩ := hab.right y hy₁,
    refine ⟨z, hz₁, _⟩,
    transitivity y; assumption, },
end

@[trans] lemma agree_struct.eq_at_trans {α : Type u} [ofe α] {n : ℕ} (a b c : agree_struct α) :
  agree_struct.eq_at n a b → agree_struct.eq_at n b c → agree_struct.eq_at n a c :=
λ h₁ h₂, agree_struct.eq_at_transitive n h₁ h₂

lemma agree_struct.eq_at_equivalence {α : Type u} [ofe α] (n : ℕ) :
  equivalence (agree_struct.eq_at n : agree_struct α → agree_struct α → Prop) :=
⟨agree_struct.eq_at_reflexive n, agree_struct.eq_at_symmetric n, agree_struct.eq_at_transitive n⟩

lemma agree_struct.eq_at_mono {α : Type u} [ofe α] :
  antitone (agree_struct.eq_at : ℕ → agree_struct α → agree_struct α → Prop) :=
begin
  intros m n hmn a b h,
  split,
  { intros x hx,
    obtain ⟨y, hy₁, hy₂⟩ := h.left x hx,
    refine ⟨y, hy₁, _⟩,
    exact eq_at_mono hmn hy₂, },
  { intros x hx,
    obtain ⟨y, hy₁, hy₂⟩ := h.right x hx,
    refine ⟨y, hy₁, _⟩,
    exact eq_at_mono hmn hy₂, },
end

lemma agree_struct.mem_of_forall_eq_at {α : Type u} [ofe α] (a b : agree_struct α) :
  (∀ (n : ℕ), agree_struct.eq_at n a b) → ∀ x ∈ a, x ∈ b :=
begin
  intros h x hx,
  have : ∀ n, ∃ y ∈ b, x =[n] y := λ n, (h n).left x hx,
  choose Y hY₁ hY₂ using this,
  set f : ℕ → b.elts := λ n, ⟨Y n, hY₁ n⟩,
  obtain ⟨⟨y, hy₁⟩, hy₂⟩ := finite.exists_infinite_fiber f,
  suffices : x = y,
  { rw this, exact hy₁, },
  rw set.infinite_coe_iff at hy₂,
  refine eq_at_infinite _ _ hy₂ _,
  intros n hn,
  simp only [set.mem_preimage, set.mem_singleton_iff, subtype.mk_eq_mk] at hn,
  rw ← hn,
  exact hY₂ n,
end

lemma agree_struct.eq_at_limit {α : Type u} [ofe α] (a b : agree_struct α) :
  (∀ (n : ℕ), agree_struct.eq_at n a b) → a = b :=
begin
  intros h,
  ext x,
  split,
  { exact agree_struct.mem_of_forall_eq_at _ _ h _, },
  { refine agree_struct.mem_of_forall_eq_at _ _ _ _,
    intro n,
    symmetry,
    exact h n, },
end

def agree_struct.rel {α : Type u} [ofe α] (a b : agree_struct α) : Prop :=
∀ n, agree_struct.eq_at n a b

lemma agree_struct.rel_reflexive {α : Type u} [ofe α] :
  reflexive (agree_struct.rel : agree_struct α → agree_struct α → Prop) :=
λ a n, agree_struct.eq_at_reflexive n a

@[refl] lemma agree_struct.rel_refl {α : Type u} [ofe α] (a : agree_struct α) :
  agree_struct.rel a a := agree_struct.rel_reflexive a

lemma agree_struct.rel_symmetric {α : Type u} [ofe α] :
  symmetric (agree_struct.rel : agree_struct α → agree_struct α → Prop) :=
λ a b hab n, agree_struct.eq_at_symmetric n (hab n)

@[symm] lemma agree_struct.rel_symm {α : Type u} [ofe α] (a b : agree_struct α) :
  agree_struct.rel a b → agree_struct.rel b a := λ h, agree_struct.rel_symmetric h

lemma agree_struct.rel_transitive {α : Type u} [ofe α] :
  transitive (agree_struct.rel : agree_struct α → agree_struct α → Prop) :=
λ a b c hab hbc n, agree_struct.eq_at_transitive n (hab n) (hbc n)

@[trans] lemma agree_struct.rel_trans {α : Type u} [ofe α] (a b c : agree_struct α) :
  agree_struct.rel a b → agree_struct.rel b c → agree_struct.rel a c :=
λ h₁ h₂, agree_struct.rel_transitive h₁ h₂

lemma agree_struct.rel_equivalence {α : Type u} [ofe α] :
  equivalence (agree_struct.rel : agree_struct α → agree_struct α → Prop) :=
⟨agree_struct.rel_reflexive, agree_struct.rel_symmetric, agree_struct.rel_transitive⟩

instance {α : Type u} [ofe α] : setoid (agree_struct α) :=
⟨agree_struct.rel, agree_struct.rel_equivalence⟩

def agree (α : Type u) [ofe α] : Type u := quotient (agree_struct.setoid : setoid (agree_struct α))

lemma agree_struct.eq_at_respects_rel {α : Type u} [ofe α] (n : ℕ) (a₁ a₂ b₁ b₂ : agree_struct α) :
  a₁ ≈ b₁ → a₂ ≈ b₂ → agree_struct.eq_at n a₁ a₂ = agree_struct.eq_at n b₁ b₂ :=
begin
  intros h₁ h₂,
  ext1,
  split; intro h,
  { transitivity a₁,
    { symmetry, exact h₁ n, },
    transitivity a₂,
    { exact h, },
    { exact h₂ n, }, },
  { transitivity b₁,
    { exact h₁ n, },
    transitivity b₂,
    { exact h, },
    { symmetry, exact h₂ n, }, },
end

def agree.eq_at {α : Type u} [ofe α] (n : ℕ) : agree α → agree α → Prop :=
quotient.lift₂ (agree_struct.eq_at n) (agree_struct.eq_at_respects_rel n)

private lemma agree.eq_at_reflexive {α : Type u} [ofe α] (n : ℕ) :
  reflexive (agree.eq_at n : agree α → agree α → Prop) :=
begin
  intro a, refine quotient.induction_on a _, clear a, intro a,
  simp only [agree.eq_at, quotient.lift₂_mk],
end

private lemma agree.eq_at_symmetric {α : Type u} [ofe α] (n : ℕ) :
  symmetric (agree.eq_at n : agree α → agree α → Prop) :=
begin
  intros a b, refine quotient.induction_on₂ a b _, clear a b, intros a b,
  simp only [agree.eq_at, quotient.lift₂_mk],
  intro h, symmetry, exact h,
end

private lemma agree.eq_at_transitive {α : Type u} [ofe α] (n : ℕ) :
  transitive (agree.eq_at n : agree α → agree α → Prop) :=
begin
  intros a b c, refine quotient.induction_on₃ a b c _, clear a b c, intros a b c,
  simp only [agree.eq_at, quotient.lift₂_mk],
  intros h₁ h₂, transitivity b; assumption,
end

private lemma agree.eq_at_mono {α : Type u} [ofe α] :
  antitone (agree.eq_at : ℕ → agree α → agree α → Prop) :=
begin
  intros m n hmn a b,
  refine quotient.induction_on₂ a b _, clear a b, intros a b,
  simp only [agree.eq_at, quotient.lift₂_mk],
  exact agree_struct.eq_at_mono hmn a b,
end

private lemma agree.eq_at_limit {α : Type u} [ofe α] (a b : agree α) :
  (∀ (n : ℕ), agree.eq_at n a b) → a = b :=
begin
  refine quotient.induction_on₂ a b _, clear a b, intros a b,
  intros h,
  refine quotient.sound _,
  intro n,
  rw agree_struct.eq_at_limit a b h,
end

instance agree.ofe (α : Type u) [ofe α] : ofe (agree α) := {
  eq_at := agree.eq_at,
  eq_at_reflexive := agree.eq_at_reflexive,
  eq_at_symmetric := agree.eq_at_symmetric,
  eq_at_transitive := agree.eq_at_transitive,
  eq_at_mono' := agree.eq_at_mono,
  eq_at_limit' := agree.eq_at_limit,
}

@[simp] lemma agree.eq_at_mk' {α : Type u} [ofe α] (n : ℕ) (a b : agree_struct α) :
  agree.eq_at n ⟦a⟧ ⟦b⟧ ↔ agree_struct.eq_at n a b := iff.rfl

@[simp] lemma agree.eq_at_mk {α : Type u} [ofe α] (n : ℕ) (a b : agree_struct α) :
  (@ofe.eq_at (agree α) _ n ⟦a⟧ ⟦b⟧) ↔ agree_struct.eq_at n a b := iff.rfl

instance agree_struct.comm_semigroup (α : Type u) [ofe α] [decidable_eq α] :
  comm_semigroup (agree_struct α) := {
  mul := λ a b, ⟨a.elts ∪ b.elts, begin
    rw [← finset.coe_nonempty, finset.coe_union, set.union_nonempty, finset.coe_nonempty],
    exact or.inl a.nonempty,
  end⟩,
  mul_assoc := begin
    intros a b c,
    ext x,
    simp only [finset.union_assoc],
  end,
  mul_comm := begin
    intros a b,
    ext x,
    simp only [has_mul.mul, finset.mem_union],
    exact or.comm,
  end,
}

@[simp] lemma agree_struct.mul_elts {α : Type u} [ofe α] [decidable_eq α]
  (a b : agree_struct α) : (a * b).elts = a.elts ∪ b.elts := rfl

@[simp] lemma agree_struct.mem_mul {α : Type u} [ofe α] [decidable_eq α]
  (x : α) (a b : agree_struct α) : x ∈ a * b ↔ x ∈ a ∨ x ∈ b :=
begin
  rw [← agree_struct.has_mem_iff, agree_struct.mul_elts, finset.mem_union],
  refl,
end

lemma agree_struct.eq_at_mul {α : Type u} [ofe α] [decidable_eq α]
  {n : ℕ} (a b c d : agree_struct α) :
  agree_struct.eq_at n a b → agree_struct.eq_at n c d → agree_struct.eq_at n (a * c) (b * d) :=
begin
  intros ha hb,
  split,
  { intros x hx,
    rw agree_struct.mem_mul at hx,
    cases hx,
    { obtain ⟨y, hy₁, hy₂⟩ := ha.left x hx,
      refine ⟨y, _, hy₂⟩,
      rw agree_struct.mem_mul,
      exact or.inl hy₁, },
    { obtain ⟨y, hy₁, hy₂⟩ := hb.left x hx,
      refine ⟨y, _, hy₂⟩,
      rw agree_struct.mem_mul,
      exact or.inr hy₁, }, },
  { intros x hx,
    rw agree_struct.mem_mul at hx,
    cases hx,
    { obtain ⟨y, hy₁, hy₂⟩ := ha.right x hx,
      refine ⟨y, _, hy₂⟩,
      rw agree_struct.mem_mul,
      exact or.inl hy₁, },
    { obtain ⟨y, hy₁, hy₂⟩ := hb.right x hx,
      refine ⟨y, _, hy₂⟩,
      rw agree_struct.mem_mul,
      exact or.inr hy₁, }, },
end

lemma agree_struct.mul_respects_rel {α : Type u} [ofe α] [decidable_eq α]
  (a₁ a₂ b₁ b₂ : agree_struct α) : a₁ ≈ b₁ → a₂ ≈ b₂ → ⟦a₁ * a₂⟧ = ⟦b₁ * b₂⟧ :=
λ ha hb, quotient.sound (λ n, agree_struct.eq_at_mul a₁ b₁ a₂ b₂ (ha n) (hb n))

instance agree.comm_semigroup (α : Type u) [ofe α] [decidable_eq α] : comm_semigroup (agree α) := {
  mul := quotient.lift₂ (λ a b, ⟦a * b⟧) agree_struct.mul_respects_rel,
  mul_assoc := begin
    intros a b c, refine quotient.induction_on₃ a b c _, clear a b c, intros a b c,
    refine quotient.sound _,
    rw mul_assoc,
    exact setoid.refl _,
  end,
  mul_comm := begin
    intros a b, refine quotient.induction_on₂ a b _, clear a b, intros a b,
    refine quotient.sound _,
    rw mul_comm,
    exact setoid.refl _,
  end,
}

@[simp] lemma agree_struct.mul_self {α : Type u} [ofe α] [decidable_eq α] (a : agree_struct α) :
  a * a = a :=
by ext; rw [agree_struct.mul_elts, finset.union_idempotent]

@[simp] lemma agree.mul_self {α : Type u} [ofe α] [decidable_eq α] (a : agree α) :
  a * a = a :=
begin
  refine quotient.induction_on a _, clear a, intro a,
  refine quotient.sound _,
  rw agree_struct.mul_self,
  exact setoid.refl _,
end

@[simp] lemma agree_struct.mul_mk {α : Type u} [ofe α] [decidable_eq α]
  (a b : agree_struct α) : @has_mul.mul (agree α) _ ⟦a⟧ ⟦b⟧ = ⟦a * b⟧ := rfl

def agree_struct.validn {α : Type u} [ofe α] (a : agree_struct α) : sprop :=
⟨λ n, ∀ x y ∈ a, x =[n] y, λ m n hmn h x hx y hy, eq_at_mono hmn (h x hx y hy)⟩

lemma agree_struct.validn_mul {α : Type u} [ofe α] [decidable_eq α] (a b : agree_struct α) :
  agree_struct.validn (a * b) ≤ agree_struct.validn a :=
begin
  intros n h x hx y hy,
  refine h x _ y _;
  rw agree_struct.mem_mul;
  exact or.inl ‹_›,
end

lemma agree_struct.validn_respects_rel {α : Type u} [ofe α] (a b : agree_struct α) :
  a ≈ b → a.validn = b.validn :=
begin
  intro hab,
  ext n,
  split,
  { intros h x hx y hy,
    obtain ⟨z, hz₁, hz₂⟩ := (hab n).right x hx,
    obtain ⟨w, hw₁, hw₂⟩ := (hab n).right y hy,
    have := h z hz₁ w hw₁,
    symmetry' at hz₂,
    transitivity, assumption, transitivity; assumption, },
  { intros h x hx y hy,
    obtain ⟨z, hz₁, hz₂⟩ := (hab n).left x hx,
    obtain ⟨w, hw₁, hw₂⟩ := (hab n).left y hy,
    have := h z hz₁ w hw₁,
    symmetry' at hw₂,
    transitivity, assumption, transitivity; assumption, },
end

def agree.validn {α : Type u} [ofe α] : agree α → sprop :=
quotient.lift agree_struct.validn agree_struct.validn_respects_rel

@[simp] lemma agree.validn_mk {α : Type u} [ofe α] (a : agree_struct α) :
  agree.validn ⟦a⟧ = a.validn := rfl

lemma agree.validn_is_nonexpansive {α : Type u} [ofe α] :
  is_nonexpansive (agree.validn : agree α → sprop) :=
begin
  intros n a b, refine quotient.induction_on₂ a b _, clear a b, intros a b,
  intros h m hmn,
  rw [agree.validn_mk, agree.validn_mk],
  rw agree.eq_at_mk at h,
  split,
  { intros hm x hx y hy,
    obtain ⟨z, hz₁, hz₂⟩ := h.right x hx,
    obtain ⟨w, hw₁, hw₂⟩ := h.right y hy,
    have hz₃ := eq_at_mono hmn hz₂,
    have hw₃ := eq_at_mono hmn hw₂,
    have := hm z hz₁ w hw₁,
    symmetry' at hz₃,
    transitivity, assumption, transitivity; assumption, },
  { intros hm x hx y hy,
    obtain ⟨z, hz₁, hz₂⟩ := h.left x hx,
    obtain ⟨w, hw₁, hw₂⟩ := h.left y hy,
    have hz₃ := eq_at_mono hmn hz₂,
    have hw₃ := eq_at_mono hmn hw₂,
    have := hm z hz₁ w hw₁,
    symmetry' at hw₃,
    transitivity, assumption, transitivity; assumption, },
end

instance agree_struct.decidable_exists_mem {α : Type u} [ofe α] [decidable_eq α] [decidable_eq_at α]
  {n : ℕ} {a : agree_struct α} {x : α} : decidable (∃ y ∈ a, x =[n] y) :=
begin
  refine decidable_of_decidable_of_iff _ _,
  exact (finset.filter (λ y, x =[n] y) a.elts).nonempty,
  { apply_instance, },
  split,
  { rintro ⟨y, hy⟩,
    simp only [finset.mem_filter, agree_struct.has_mem_iff] at hy,
    exact ⟨y, hy.1, hy.2⟩, },
  { rintro ⟨y, hy₁, hy₂⟩,
    refine ⟨y, _⟩,
    simp only [finset.mem_filter, agree_struct.has_mem_iff],
    exact ⟨hy₁, hy₂⟩, },
end

/-- Keeps those elements of `a` that have an element of `b` that it is `n`-equal to. -/
def agree_struct.filter_eq {α : Type u} [ofe α] [decidable_eq α] [decidable_eq_at α]
  (a b : agree_struct α) (n : ℕ) (h : ∃ x ∈ a, ∃ y ∈ b, x =[n] y) : agree_struct α :=
⟨finset.filter (λ x, ∃ y ∈ b, x =[n] y) a.elts, begin
  obtain ⟨x, hx, y, hy, h⟩ := h,
  refine ⟨x, _⟩,
  simp only [finset.mem_filter, agree_struct.has_mem_iff],
  exact ⟨hx, y, hy, h⟩,
end⟩

@[simp] lemma agree_struct.mem_filter_eq {α : Type u} [ofe α] [decidable_eq α] [decidable_eq_at α]
  (x : α) (a b : agree_struct α) (n : ℕ) (h : ∃ x ∈ a, ∃ y ∈ b, x =[n] y) :
  x ∈ a.filter_eq b n h ↔ x ∈ a ∧ ∃ y ∈ b, x =[n] y :=
by simp only [agree_struct.filter_eq, agree_struct.mem_mk,
  finset.mem_filter, agree_struct.has_mem_iff]

lemma agree_struct.exists_eq_at_of_mul_eq_at {α : Type u} [ofe α] [decidable_eq α] [decidable_eq_at α]
  {n : ℕ} {a b₁ b₂ : agree_struct α} (hb : agree_struct.eq_at n a (b₁ * b₂)) :
    ∃ x ∈ a, ∃ y ∈ b₁, x =[n] y :=
begin
  obtain ⟨y, hy⟩ := b₁.nonempty,
  obtain ⟨x, hx₁, hx₂⟩ := hb.right y _,
  refine ⟨x, hx₁, y, hy, hx₂⟩,
  rw agree_struct.mem_mul,
  exact or.inl hy,
end

lemma agree_struct.exists_eq_at_of_mul_eq_at' {α : Type u} [ofe α] [decidable_eq α] [decidable_eq_at α]
  {n : ℕ} {a b₁ b₂ : agree_struct α} (hb : agree_struct.eq_at n a (b₁ * b₂)) :
    ∃ x ∈ a, ∃ y ∈ b₂, x =[n] y :=
begin
  refine agree_struct.exists_eq_at_of_mul_eq_at _,
  exact b₁,
  rw mul_comm,
  exact hb,
end

def agree_struct.extend {α : Type u} [ofe α] [decidable_eq α] [decidable_eq_at α]
  {n : ℕ} {a b₁ b₂ : agree_struct α} (hb : agree_struct.eq_at n a (b₁ * b₂)) :
    agree_struct α × agree_struct α :=
⟨a.filter_eq b₁ n (agree_struct.exists_eq_at_of_mul_eq_at hb),
  a.filter_eq b₂ n (agree_struct.exists_eq_at_of_mul_eq_at' hb)⟩

lemma agree_struct.extend_mul_eq {α : Type u} [ofe α] [decidable_eq α] [decidable_eq_at α]
  {n : ℕ} {a b₁ b₂ : agree_struct α} (hb : agree_struct.eq_at n a (b₁ * b₂)) :
    a = (agree_struct.extend hb).1 * (agree_struct.extend hb).2 :=
begin
  unfold agree_struct.extend,
  ext x,
  simp only [agree_struct.has_mem_iff, agree_struct.mul_elts, finset.mem_union,
    agree_struct.mem_filter_eq, exists_prop],
  split,
  { intro hx,
    obtain ⟨y, hy₁, hy₂⟩ := hb.left x hx,
    rw agree_struct.mem_mul at hy₁,
    cases hy₁,
    exact or.inl ⟨hx, y, hy₁, hy₂⟩,
    exact or.inr ⟨hx, y, hy₁, hy₂⟩, },
  { rintro (hx | hx);
    exact hx.1, },
end

lemma agree_struct.extend_eq_at_left {α : Type u} [ofe α] [decidable_eq α] [decidable_eq_at α]
  {n : ℕ} {a b₁ b₂ : agree_struct α}
  (ha : agree_struct.validn a n) (hb : agree_struct.eq_at n a (b₁ * b₂)) :
    agree_struct.eq_at n (agree_struct.extend hb).1 b₁ :=
begin
  unfold agree_struct.extend,
  split,
  { intros x hx,
    rw agree_struct.mem_filter_eq at hx,
    obtain ⟨hx, y, hy₁, hy₂⟩ := hx,
    exact ⟨y, hy₁, hy₂⟩, },
  { intros x hx,
    obtain ⟨y, hy₁, hy₂⟩ := hb.right x _,
    refine ⟨y, _, hy₂⟩,
    rw agree_struct.mem_filter_eq,
    exact ⟨hy₁, x, hx, hy₂⟩,
    rw agree_struct.mem_mul,
    exact or.inl hx, },
end

lemma agree_struct.extend_eq_at_right {α : Type u} [ofe α] [decidable_eq α] [decidable_eq_at α]
  {n : ℕ} {a b₁ b₂ : agree_struct α}
  (ha : agree_struct.validn a n) (hb : agree_struct.eq_at n a (b₁ * b₂)) :
    agree_struct.eq_at n (agree_struct.extend hb).2 b₂ :=
begin
  unfold agree_struct.extend,
  split,
  { intros x hx,
    rw agree_struct.mem_filter_eq at hx,
    obtain ⟨hx, y, hy₁, hy₂⟩ := hx,
    exact ⟨y, hy₁, hy₂⟩, },
  { intros x hx,
    obtain ⟨y, hy₁, hy₂⟩ := hb.right x _,
    refine ⟨y, _, hy₂⟩,
    rw agree_struct.mem_filter_eq,
    exact ⟨hy₁, x, hx, hy₂⟩,
    rw agree_struct.mem_mul,
    exact or.inr hx, },
end

attribute [reducible, elab_as_eliminator]
protected def quotient.dlift {α : Sort u} [s : setoid α] {φ : quotient s → Sort v}
  (f : Π (a : α), φ ⟦a⟧) (c : ∀ a b, a ≈ b → f a == f b)
  (q : quotient s) : φ q :=
begin
  refine quotient.rec f _ q,
  intros a b h,
  have := c a b h,
  cc,
end

@[simp] lemma quotient.dlift_mk {α : Sort u} [s : setoid α] {φ : quotient s → Sort v}
  (f : Π (a : α), φ ⟦a⟧) (c : ∀ a b, a ≈ b → f a == f b) (q : α) :
  (quotient.dlift f c ⟦q⟧ : φ ⟦q⟧) = f q := rfl

attribute [reducible, elab_as_eliminator]
protected def quotient.dlift₂ {α β : Sort*} [s₁ : setoid α] [s₂ : setoid β]
  {φ : quotient s₁ → quotient s₂ → Sort*}
  (f : Π (a : α) (b : β), φ ⟦a⟧ ⟦b⟧) (c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ == f b₁ b₂)
  (q₁ : quotient s₁) (q₂ : quotient s₂) : φ q₁ q₂ :=
begin
  refine quotient.dlift (λ a, quotient.dlift (λ b, f a b) _ q₂) _ q₁,
  { intros b₁ b₂ hb,
    exact c a b₁ a b₂ (setoid.refl a) hb, },
  { intros b₁ b₂ hb,
    refine quotient.induction_on q₂ _, clear q₂, intro q₂,
    rw [quotient.dlift_mk, quotient.dlift_mk],
    exact c b₁ q₂ b₂ q₂ hb (setoid.refl q₂), },
end

@[simp] lemma quotient.dlift₂_mk {α β : Sort*} [s₁ : setoid α] [s₂ : setoid β]
  {φ : quotient s₁ → quotient s₂ → Sort u}
  (f : Π (a : α) (b : β), φ ⟦a⟧ ⟦b⟧) (c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ == f b₁ b₂)
  (q₁ : α) (q₂ : β) : (quotient.dlift₂ f c ⟦q₁⟧ ⟦q₂⟧ : φ ⟦q₁⟧ ⟦q₂⟧) = f q₁ q₂ := rfl

attribute [reducible, elab_as_eliminator]
protected def quotient.dlift₃ {α β γ : Sort*} [s₁ : setoid α] [s₂ : setoid β] [s₃ : setoid γ]
  {φ : quotient s₁ → quotient s₂ → quotient s₃ → Sort*}
  (f : Π (a : α) (b : β) (c : γ), φ ⟦a⟧ ⟦b⟧ ⟦c⟧)
  (c : ∀ a₁ a₂ a₃ b₁ b₂ b₃, a₁ ≈ b₁ → a₂ ≈ b₂ → a₃ ≈ b₃ → f a₁ a₂ a₃ == f b₁ b₂ b₃)
  (q₁ : quotient s₁) (q₂ : quotient s₂) (q₃ : quotient s₃) : φ q₁ q₂ q₃ :=
begin
  refine quotient.dlift (λ a, quotient.dlift₂ (λ b c, f a b c) _ q₂ q₃) _ q₁,
  { intros a₂ a₃ b₂ b₃ h₂ h₃,
    exact c a a₂ a₃ a b₂ b₃ (setoid.refl a) h₂ h₃, },
  { intros b₁ b₂ hb,
    refine quotient.induction_on₂ q₂ q₃ _, clear q₂ q₃, intros q₂ q₃,
    simp only [quotient.dlift₂_mk],
    exact c b₁ q₂ q₃ b₂ q₂ q₃ hb (setoid.refl q₂) (setoid.refl q₃), },
end

@[simp] lemma quotient.dlift₃_mk {α β γ : Sort*} [s₁ : setoid α] [s₂ : setoid β] [s₃ : setoid γ]
  {φ : quotient s₁ → quotient s₂ → quotient s₃ → Sort*}
  (f : Π (a : α) (b : β) (c : γ), φ ⟦a⟧ ⟦b⟧ ⟦c⟧)
  (c : ∀ a₁ a₂ a₃ b₁ b₂ b₃, a₁ ≈ b₁ → a₂ ≈ b₂ → a₃ ≈ b₃ → f a₁ a₂ a₃ == f b₁ b₂ b₃)
  (q₁ : α) (q₂ : β) (q₃ : γ) :
    (quotient.dlift₃ f c ⟦q₁⟧ ⟦q₂⟧ ⟦q₃⟧ : φ ⟦q₁⟧ ⟦q₂⟧ ⟦q₃⟧) = f q₁ q₂ q₃ := rfl

attribute [reducible, elab_as_eliminator]
protected def quotient.lift₃ {α β γ φ : Sort*} [s₁ : setoid α] [s₂ : setoid β] [s₃ : setoid γ]
  (f : α → β → γ → φ) (c : ∀ a₁ a₂ a₃ b₁ b₂ b₃, a₁ ≈ b₁ → a₂ ≈ b₂ → a₃ ≈ b₃ → f a₁ a₂ a₃ = f b₁ b₂ b₃)
  (q₁ : quotient s₁) (q₂ : quotient s₂) (q₃ : quotient s₃) : φ :=
begin
  refine quotient.lift (λ a₁, quotient.lift₂ (f a₁) _ q₂ q₃) _ q₁,
  { intros a₂ a₃ b₂ b₃ h₂ h₃,
    exact c a₁ a₂ a₃ a₁ b₂ b₃ (setoid.refl a₁) h₂ h₃, },
  { intros a b h,
    refine quotient.induction_on₂ q₂ q₃ _, clear q₂ q₃, intros q₂ q₃,
    exact c a q₂ q₃ b q₂ q₃ h (setoid.refl q₂) (setoid.refl q₃), },
end

lemma agree.filter_eq_exists_mem {α : Type u} {n m : ℕ} [ofe α] [decidable_eq α] [decidable_eq_at α]
  {a₁ a₂ b₁ b₂ : agree_struct α} (h₁ : a₁ ≈ b₁) (h₂ : a₂ ≈ b₂)
  (b : ∃ x ∈ a₁, ∃ y ∈ a₂, x =[n] y) (b' : ∃ x ∈ b₁, ∃ y ∈ b₂, x =[n] y) :
  ∀ x ∈ a₁.filter_eq a₂ n b, ∃ y ∈ b₁.filter_eq b₂ n b', x =[m] y :=
begin
  intros x hx,
  simp only [agree_struct.mem_filter_eq, exists_prop] at hx ⊢,
  obtain ⟨hx, z, hz₁, hz₂⟩ := hx,
  obtain ⟨y, hy₁, hy₂⟩ := (h₁ (max m n)).left x hx,
  rw eq_at_max at hy₂,
  obtain ⟨w, hw₁, hw₂⟩ := (h₂ n).left z hz₁,
  refine ⟨y, _, hy₂.1⟩,
  refine ⟨hy₁, _⟩,
  refine ⟨w, hw₁, _⟩,
  transitivity x, exact eq_at_symmetric n hy₂.2,
  transitivity; assumption,
end

lemma agree.filter_eq_exists_mem' {α : Type u} {n m : ℕ} [ofe α] [decidable_eq α] [decidable_eq_at α]
  {a₁ a₂ b₁ b₂ : agree_struct α} (h₁ : b₁ ≈ a₁) (h₂ : b₂ ≈ a₂)
  (b : ∃ x ∈ a₁, ∃ y ∈ a₂, x =[n] y) (b' : ∃ x ∈ b₁, ∃ y ∈ b₂, x =[n] y) :
  ∀ x ∈ a₁.filter_eq a₂ n b, ∃ y ∈ b₁.filter_eq b₂ n b', y =[m] x :=
begin
  intros,
  obtain ⟨y, hy₁, hy₂⟩ := agree.filter_eq_exists_mem (setoid.symm h₁) (setoid.symm h₂) b b' x ‹_›,
  refine ⟨y, hy₁, _⟩,
  symmetry,
  assumption,
end

def agree.extend {α : Type u} [ofe α] [decidable_eq α] [decidable_eq_at α]
  {n : ℕ} : Π {a b₁ b₂ : agree α}, agree.validn a n → a =[n] b₁ * b₂ → agree α × agree α :=
begin
  refine quotient.dlift₃ _ _,
  { intros a b c h₁ h₂,
    exact prod.map quotient.mk quotient.mk (agree_struct.extend h₂), },
  { intros a₁ a₂ a₃ b₁ b₂ b₃ h₁ h₂ h₃,
    ext,
    { rw quotient.sound h₁, },
    intros a a' haa',
    ext,
    { rw [quotient.sound h₁, quotient.sound h₂, quotient.sound h₃], },
    intros b b' hbb',
    simp only [prod_map, heq_iff_eq, prod.mk.inj_iff, quotient.eq],
    split; intro; split,
    { apply agree.filter_eq_exists_mem; assumption, },
    { apply agree.filter_eq_exists_mem'; assumption, },
    { apply agree.filter_eq_exists_mem; assumption, },
    { apply agree.filter_eq_exists_mem'; assumption, }, },
end

lemma agree.extend_mul_eq {α : Type u} [ofe α] [decidable_eq α] [decidable_eq_at α]
  {n : ℕ} {a b₁ b₂ : agree α} (ha : agree.validn a n) (hb : agree.eq_at n a (b₁ * b₂)) :
    a = (agree.extend ha hb).1 * (agree.extend ha hb).2 :=
begin
  revert ha hb,
  refine quotient.induction_on₃ a b₁ b₂ _, clear a b₁ b₂, intros a b₁ b₂,
  intros ha hb,
  refine quotient.sound _,
  rw ← agree_struct.extend_mul_eq hb,
  exact setoid.refl a,
end

lemma agree.extend_eq_at_left {α : Type u} [ofe α] [decidable_eq α] [decidable_eq_at α]
  {n : ℕ} {a b₁ b₂ : agree α} (ha : agree.validn a n) (hb : agree.eq_at n a (b₁ * b₂)) :
    agree.eq_at n (agree.extend ha hb).1 b₁ :=
begin
  revert ha hb,
  refine quotient.induction_on₃ a b₁ b₂ _, clear a b₁ b₂, intros a b₁ b₂,
  intros ha hb,
  exact agree_struct.extend_eq_at_left ha hb,
end

lemma agree.extend_eq_at_right {α : Type u} [ofe α] [decidable_eq α] [decidable_eq_at α]
  {n : ℕ} {a b₁ b₂ : agree α} (ha : agree.validn a n) (hb : agree.eq_at n a (b₁ * b₂)) :
    agree.eq_at n (agree.extend ha hb).2 b₂ :=
begin
  revert ha hb,
  refine quotient.induction_on₃ a b₁ b₂ _, clear a b₁ b₂, intros a b₁ b₂,
  intros ha hb,
  exact agree_struct.extend_eq_at_right ha hb,
end

lemma agree.mul_is_nonexpansive {α : Type u} [ofe α] [decidable_eq α] :
  is_nonexpansive (function.uncurry ((*) : agree α → agree α → agree α)) :=
begin
  rintros n ⟨a₁, a₂⟩ ⟨b₁, b₂⟩,
  refine quotient.induction_on₂ a₁ a₂ _, clear a₁ a₂, intros a₁ a₂,
  refine quotient.induction_on₂ b₁ b₂ _, clear b₁ b₂, intros b₁ b₂,
  simp only [prod.eq_at, agree.eq_at_mk, function.uncurry_apply_pair, agree_struct.mul_mk, and_imp],
  intros h₁ h₂,
  exact agree_struct.eq_at_mul a₁ b₁ a₂ b₂ h₁ h₂,
end

lemma agree.validn_mul {α : Type u} [ofe α] [decidable_eq α] (a b : agree α) :
  agree.validn (a * b) ≤ agree.validn a :=
begin
  refine quotient.induction_on₂ a b _, clear a b, intros a b,
  intros n h,
  simp only [agree_struct.mul_mk, agree.validn_mk] at h ⊢,
  exact agree_struct.validn_mul a b n h,
end

instance agree.camera (α : Type u) [ofe α] [decidable_eq α] [decidable_eq_at α] :
  camera (agree α) := {
  validn := ⟨agree.validn, agree.validn_is_nonexpansive⟩,
  core := ⟨some, option.some_is_nonexpansive⟩,
  extend := @agree.extend _ _ _ _,
  mul_is_nonexpansive := agree.mul_is_nonexpansive,
  extend_mul_eq := @agree.extend_mul_eq _ _ _ _,
  extend_eq_at_left := @agree.extend_eq_at_left _ _ _ _,
  extend_eq_at_right := @agree.extend_eq_at_right _ _ _ _,
  core_mul_self := begin
    intros a ca hca,
    cases hca,
    rw agree.mul_self,
  end,
  core_core := λ a ca hca, rfl,
  core_mono_some := λ a b ca hca h, ⟨b, rfl⟩,
  core_mono := λ a ca h₁ h₂ h₃,
    ⟨some h₃.some, by simp only [h₃.some_spec, nonexpansive_fun.coe_fn_mk, some_mul_some]⟩,
  validn_mul := agree.validn_mul,
  ..agree.ofe α,
  ..agree.comm_semigroup α,
}
