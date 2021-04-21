import defs.statics

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
