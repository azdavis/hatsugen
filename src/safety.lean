import helpers

theorem progress
  (Γ: cx typ)
  (tcx_nil: Γ = list.nil)
  (e: exp) (τ: typ)
  (et: has_typ Γ e τ)
  : val e ∨ (∃ (e': exp), steps e e') :=
begin
  induction et,
  left,
  exact val.int et_n,
  left,
  exact val.true,
  left,
  exact val.false,
  right,
  cases et_ih_a tcx_nil,
  cases bool_canonical_forms et_Γ et_e1 h et_a,
  rewrite h_1,
  existsi et_e2,
  exact steps.if_true et_e2 et_e3,
  rewrite h_1,
  existsi et_e3,
  exact steps.if_false et_e2 et_e3,
  cases h,
  existsi exp.if_ h_w et_e2 et_e3,
  exact steps.if_e1 et_e1 h_w et_e2 et_e3 h_h,
end

theorem preservation
  (Γ: cx typ)
  (tcx_nil: Γ = list.nil)
  (e: exp) (e': exp) (τ: typ)
  (et: has_typ Γ e τ)
  (st: steps e e')
  : has_typ Γ e' τ :=
begin
  induction st generalizing Γ τ,
  let inv := inversion_if Γ st_e1 st_e2 st_e3 τ et,
  let e1_typ := st_ih Γ typ.bool tcx_nil inv.left,
  exact has_typ.if_ Γ st_e1' st_e2 st_e3 τ e1_typ inv.right.left inv.right.right,
  let inv := inversion_if Γ exp.true st_e2 st_e3 τ et,
  exact inv.right.left,
  let inv := inversion_if Γ exp.false st_e2 st_e3 τ et,
  exact inv.right.right,
end
