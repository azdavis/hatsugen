import statics
import dynamics

theorem inversion_if_e1
  (e1: exp) (e2: exp) (e3: exp) (τ: typ)
  (typing: has_typ (exp.if_ e1 e2 e3) τ)
  : has_typ e1 typ.bool :=
begin
  cases typing,
  exact typing_a,
end

theorem inversion_if_e2
  (e1: exp) (e2: exp) (e3: exp) (τ: typ)
  (typing: has_typ (exp.if_ e1 e2 e3) τ)
  : has_typ e2 τ :=
begin
  cases typing,
  exact typing_a_1,
end

theorem inversion_if_e3
  (e1: exp) (e2: exp) (e3: exp) (τ: typ)
  (typing: has_typ (exp.if_ e1 e2 e3) τ)
  : has_typ e3 τ :=
begin
  cases typing,
  exact typing_a_2,
end

theorem bool_canonical_forms
  (e: exp)
  (typing: has_typ e typ.bool)
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
