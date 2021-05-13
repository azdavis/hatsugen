import defs.statics

theorem inversion_if
  {Γ: cx typ} {e1 e2 e3: exp} {τ: typ}
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

theorem inversion_app
  {Γ: cx typ} {e1 e2: exp} {τ2: typ}
  (et: has_typ Γ (exp.app e1 e2) τ2)
  : ∃ (τ1: typ), has_typ Γ e1 (typ.arrow τ1 τ2) ∧ has_typ Γ e2 τ1 :=
begin
  cases et,
  existsi et_τ1,
  split,
  exact et_a,
  exact et_a_1,
end

theorem inversion_fn
  {Γ: cx typ} {x: var} {τ1 τ: typ} {e: exp}
  (et: has_typ Γ (exp.fn x τ1 e) τ)
  : ∃ (τ2: typ), τ = typ.arrow τ1 τ2 ∧ has_typ (cx.insert Γ x τ1) e τ2 :=
begin
  cases et,
  existsi et_τ2,
  split,
  refl,
  exact et_a,
end
