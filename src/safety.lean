import helpers

-- seems like we have to write this as taking in a general context and also a
-- proof that it is nil, rather than just having `et: has_typ cx.nil e tau`.
theorem progress
  (Γ: cx)
  (e: exp) (τ: typ)
  (is_nil: Γ = cx.nil)
  (et: exp_typ Γ e τ)
  : (∃ (v: val), e = exp.pure v) ∨ (∃ (e': exp), steps e e') :=
begin
  induction et,
  left,
  existsi et_v,
  refl,
  right,
  cases et_ih_a is_nil,
  cases h,
  rewrite h_h at *,
  cases bool_canonical_forms et_Γ h_w (inversion_pure et_Γ h_w typ.bool et_a),
  rewrite h at *,
  existsi et_e2,
  exact steps.if_e2 et_e2 et_e3,
  rewrite h at *,
  existsi et_e3,
  exact steps.if_e3 et_e2 et_e3,
  cases h,
  existsi exp.if_ h_w et_e2 et_e3,
  exact steps.if_e1 et_e1 h_w et_e2 et_e3 h_h,
end

theorem preservation
  (Γ: cx) (e: exp) (e': exp) (τ: typ)
  (et: exp_typ Γ e τ)
  (is_nil: Γ = cx.nil)
  (st: steps e e')
  : exp_typ Γ e' τ :=
begin
  induction st generalizing Γ τ,
  let inv := inversion_if Γ st_e1 st_e2 st_e3 τ et,
  let e1_typ := st_ih Γ typ.bool inv.left is_nil,
  exact exp_typ.if_ Γ st_e1' st_e2 st_e3 τ e1_typ inv.right.left inv.right.right,
  let inv := inversion_if Γ (exp.pure val.true) st_e2 st_e3 τ et,
  exact inv.right.left,
  let inv := inversion_if Γ (exp.pure val.false) st_e2 st_e3 τ et,
  exact inv.right.right,
end
