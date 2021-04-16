import statics
import dynamics

theorem lookup_same
  (Γ: cx) (x: var) (τ: typ) (τ': typ)
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
  (Γ: cx) (e1: exp) (e2: exp) (e3: exp) (τ: typ)
  (typing: has_typ Γ (exp.if_ e1 e2 e3) τ)
  : has_typ Γ e1 typ.bool ∧ has_typ Γ e2 τ ∧ has_typ Γ e3 τ :=
begin
  cases typing,
  split,
  exact typing_a,
  split,
  exact typing_a_1,
  exact typing_a_2,
end

theorem bool_canonical_forms
  (Γ: cx) (e: exp)
  (typing: has_typ Γ e typ.bool)
  (value: val e)
  : e = exp.true ∨ e = exp.false :=
begin
  cases typing,
  left,
  refl,
  right,
  refl,
  cases value,
end
