import helpers

theorem progress
  (Γ: cx typ) (Δ: cx exp)
  (tcx_nil: Γ = list.nil)
  (vcx_nil: Δ = list.nil)
  (e: exp) (τ: typ)
  (et: has_typ Γ e τ)
  : val e ∨ (∃ (Δ': cx exp) (e': exp), steps Δ e Δ' e') :=
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
  -- rewrite h_h at *,
  cases bool_canonical_forms et_Γ et_e1 h et_a,
  rewrite h_1,
  existsi [Δ, et_e2],
  exact steps.if_true Δ et_e2 et_e3,
  rewrite h_1,
  existsi [Δ, et_e3],
  exact steps.if_false Δ et_e2 et_e3,
  cases h,
  cases h_h,
  existsi [h_w, exp.if_ h_h_w et_e2 et_e3],
  exact steps.if_e1 Δ h_w et_e1 h_h_w et_e2 et_e3 h_h_h,
end

theorem preservation
  (Γ: cx typ) (Δ: cx exp) (Δ': cx exp)
  (tcx_nil: Γ = list.nil)
  (vcx_nil: Δ = list.nil)
  (e: exp) (e': exp) (τ: typ)
  (et: has_typ Γ e τ)
  (st: steps Δ e Δ' e')
  : has_typ Γ e' τ :=
begin
  induction st generalizing Γ τ,
  let inv := inversion_if Γ st_e1 st_e2 st_e3 τ et,
  let e1_typ := st_ih vcx_nil Γ typ.bool tcx_nil inv.left,
  exact has_typ.if_ Γ st_e1' st_e2 st_e3 τ e1_typ inv.right.left inv.right.right,
  let inv := inversion_if Γ exp.true st_e2 st_e3 τ et,
  exact inv.right.left,
  let inv := inversion_if Γ exp.false st_e2 st_e3 τ et,
  exact inv.right.right,
end
