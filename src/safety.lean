import helpers

theorem progress
  (Γ: cx typ) (Δ: cx val)
  (tcx_nil: Γ = list.nil)
  (vcx_nil: Δ = list.nil)
  (e: exp) (τ: typ)
  (et: exp_typ Γ e τ)
  : (∃ (v: val), e = exp.pure v) ∨ (∃ (e': exp), steps Δ e e') :=
begin
  induction et,
  left,
  existsi et_v,
  refl,
  right,
  cases et_ih_a tcx_nil,
  cases h,
  rewrite h_h at *,
  cases bool_canonical_forms et_Γ h_w (inversion_pure et_Γ h_w typ.bool et_a),
  rewrite h,
  existsi et_e2,
  exact steps.if_true Δ et_e2 et_e3,
  rewrite h,
  existsi et_e3,
  exact steps.if_false Δ et_e2 et_e3,
  cases h,
  existsi exp.if_ h_w et_e2 et_e3,
  exact steps.if_e1 Δ et_e1 h_w et_e2 et_e3 h_h,
end

theorem preservation
  (Γ: cx typ) (Δ: cx val)
  (tcx_nil: Γ = list.nil)
  (vcx_nil: Δ = list.nil)
  (e: exp) (e': exp) (τ: typ)
  (et: exp_typ Γ e τ)
  (st: steps Δ e e')
  : exp_typ Γ e' τ :=
begin
  induction st generalizing Γ τ,
  let inv := inversion_if Γ st_e1 st_e2 st_e3 τ et,
  let e1_typ := st_ih vcx_nil Γ typ.bool tcx_nil inv.left,
  exact exp_typ.if_ Γ st_e1' st_e2 st_e3 τ e1_typ inv.right.left inv.right.right,
  let inv := inversion_if Γ (exp.pure val.true) st_e2 st_e3 τ et,
  exact inv.right.left,
  let inv := inversion_if Γ (exp.pure val.false) st_e2 st_e3 τ et,
  exact inv.right.right,
end
