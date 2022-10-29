import algebra.ofe.complete

universe u

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

def sprop.const (p : Prop) : sprop := ⟨λ _, p, λ m n hmn h, h⟩

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

instance : has_le sprop := ⟨λ p q, (p : ℕ → Prop) ≤ q⟩

instance : partial_order sprop := {
  le_refl := λ p, le_refl (p : ℕ → Prop),
  le_trans := λ p q r hpq hqr, pi.partial_order.le_trans p q r hpq hqr,
  le_antisymm := λ a b h₁ h₂, by ext1; exact pi.partial_order.le_antisymm a b h₁ h₂,
  ..sprop.has_le
}

instance : semilattice_inf sprop := {
  inf := λ p q, ⟨λ n, p n ∧ q n, λ m n hmn h, ⟨p.mono hmn h.1, q.mono hmn h.2⟩⟩,
  inf_le_left := λ p q n h, h.1,
  inf_le_right := λ p q n h, h.2,
  le_inf := λ p q r hpq hpr n h, ⟨hpq n h, hpr n h⟩,
  ..sprop.partial_order
}

instance : semilattice_sup sprop := {
  sup := λ p q, ⟨λ n, p n ∨ q n, λ m n hmn h,
    h.elim (λ h, or.inl $ p.mono hmn h) (λ h, or.inr $ q.mono hmn h)⟩,
  le_sup_left := λ p q n h, or.inl h,
  le_sup_right := λ p q n h, or.inr h,
  sup_le := λ p q r hpr hqr n hpq, hpq.elim
    (λ hpq, hpr n hpq) (λ hpq, hqr n hpq),
  ..sprop.partial_order
}

instance : distrib_lattice sprop := {
  le_sup_inf := λ p q r n h, h.1.elim
    (λ hp, or.inl hp) (λ hq, h.2.elim (λ hp, or.inl hp) (λ hr, or.inr ⟨hq, hr⟩)),
  ..sprop.semilattice_inf,
  ..sprop.semilattice_sup,
}

instance : complete_semilattice_Inf sprop := {
  Inf := λ P, ⟨λ n, ∀ p : sprop, p ∈ P → p n, λ m n hmn h p hp, p.mono hmn (h p hp)⟩,
  Inf_le := λ P p hpP n hpn, hpn p hpP,
  le_Inf := λ P p hP n hpn q hqP, hP q hqP n hpn,
  ..sprop.distrib_lattice
}

instance : complete_semilattice_Sup sprop := {
  Sup := λ P, ⟨λ n, ∃ p : sprop, p ∈ P ∧ p n, λ m n hmn h,
    ⟨h.some, h.some_spec.1, h.some.mono hmn h.some_spec.2⟩⟩,
  le_Sup := λ P p hpP n hpn, ⟨p, hpP, hpn⟩,
  Sup_le := λ P p hP n hpn, hP hpn.some hpn.some_spec.1 n hpn.some_spec.2,
  ..sprop.distrib_lattice
}

instance : complete_lattice sprop := {
  top := ⟨λ n, true, λ n m hmn h, trivial⟩,
  bot := ⟨λ n, false, λ n m hmn h, h⟩,
  le_top := λ p n h, trivial,
  bot_le := λ p n h, false.rec _ h,
  ..sprop.distrib_lattice,
  ..sprop.complete_semilattice_Inf,
  ..sprop.complete_semilattice_Sup,
}

@[simp] lemma sprop.inf_apply {p q : sprop} {n : ℕ} : (p ⊓ q) n ↔ p n ∧ q n := iff.rfl
@[simp] lemma sprop.sup_apply {p q : sprop} {n : ℕ} : (p ⊔ q) n ↔ p n ∨ q n := iff.rfl

lemma sprop.inf_eq_at {p q r s : sprop} {n : ℕ} : p =[n] q → r =[n] s → p ⊓ r =[n] q ⊓ s :=
λ h₁ h₂ m hmn, and_congr (h₁ m hmn) (h₂ m hmn)

lemma sprop.sup_eq_at {p q r s : sprop} {n : ℕ} : p =[n] q → r =[n] s → p ⊔ r =[n] q ⊔ s :=
λ h₁ h₂ m hmn, or_congr (h₁ m hmn) (h₂ m hmn)

def sprop.incln (p q : sprop) (n : ℕ) := ∀ m ≤ n, p m → q m

notation p ` ⊆[`:50 n `] ` q:50 := p.incln q n
