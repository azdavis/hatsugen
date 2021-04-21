import statics
import dynamics

theorem subset_trans
  {t: Type}
  (a b c: set t)
  (ab: a ⊆ b) (bc: b ⊆ c): a ⊆ c
:=
begin
  intros _ h,
  exact bc (ab h)
end

@[reducible]
def fv (e: exp): set var :=
  exp.rec_on e
  -- int
  (fun _, ∅)
  -- true
  ∅
  -- false
  ∅
  -- if_
  (fun _ _ _ s1 s2 s3, s1 ∪ s2 ∪ s3)

theorem subset_if (e1 e2 e3: exp):
  fv e1 ⊆ fv (exp.if_ e1 e2 e3) ∧
  fv e2 ⊆ fv (exp.if_ e1 e2 e3) ∧
  fv e3 ⊆ fv (exp.if_ e1 e2 e3) :=
begin
  simp [fv],
  split,
  intros _ a,
  left,
  left,
  exact a,
  split,
  intros _ b,
  left,
  right,
  exact b,
  intros _ c,
  right,
  exact c,
end

theorem lookup_same
  (Γ: cx typ) (x: var) (τ: typ) (τ': typ)
  (l1: lookup Γ x τ)
  (l2: lookup Γ x τ')
  : τ = τ' :=
begin
  induction l1,
  cases l2,
  refl,
  contradiction,
  cases l2,
  contradiction,
  exact l1_ih l2_a_1,
end

theorem inversion_if
  (Γ: cx typ) (e1: exp) (e2: exp) (e3: exp) (τ: typ)
  (et: has_typ Γ (exp.if_ e1 e2 e3) τ)
  : has_typ Γ e1 typ.bool ∧ has_typ Γ e2 τ ∧ has_typ Γ e3 τ :=
begin
  cases et,
  split,
  exact et_a,
  split,
  exact et_a_1,
  exact et_a_2,
end

theorem bool_canonical_forms
  (Γ: cx typ) (e: exp) (value: val e)
  (et: has_typ Γ e typ.bool)
  : e = exp.true ∨ e = exp.false :=
begin
  cases et,
  left,
  refl,
  right,
  refl,
  cases value,
end
