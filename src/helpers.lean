import statics
import dynamics

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

theorem inversion_pure
  (Γ: cx typ) (v: val) (τ: typ)
  (et: exp_typ Γ (exp.pure v) τ):
  val_typ Γ v τ :=
begin
  cases et,
  exact et_a,
end

theorem inversion_if
  (Γ: cx typ) (e1: exp) (e2: exp) (e3: exp) (τ: typ)
  (et: exp_typ Γ (exp.if_ e1 e2 e3) τ)
  : exp_typ Γ e1 typ.bool ∧ exp_typ Γ e2 τ ∧ exp_typ Γ e3 τ :=
begin
  cases et,
  split,
  exact et_a,
  split,
  exact et_a_1,
  exact et_a_2,
end

theorem bool_canonical_forms
  (Γ: cx typ) (v: val)
  (et: val_typ Γ v typ.bool)
  : v = val.true ∨ v = val.false :=
begin
  cases et,
  left,
  refl,
  right,
  refl,
end
