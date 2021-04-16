import helpers

-- seems like we have to write this as taking in a general context and also a
-- proof that it is nil, rather than just having `typing: has_typ cx.nil e tau`.
theorem progress
  (Γ: cx)
  (e: exp) (τ: typ)
  (is_nil: Γ = cx.nil)
  (typing: has_typ Γ e τ)
  : val e ∨ (∃ (e': exp), steps e e') :=
begin
  induction typing,
  left,
  exact val.int typing_n,
  left,
  exact val.true,
  left,
  exact val.false,
  right,
  cases typing_ih_a is_nil,
  cases bool_canonical_forms typing_Γ typing_e1 typing_a h,
  existsi typing_e2,
  rewrite h_1,
  exact steps.if_e2 typing_e2 typing_e3,
  existsi typing_e3,
  rewrite h_1,
  exact steps.if_e3 typing_e2 typing_e3,
  cases h,
  existsi exp.if_ h_w typing_e2 typing_e3,
  exact steps.if_e1 typing_e1 h_w typing_e2 typing_e3 h_h,
end

theorem preservation
  (Γ: cx) (e: exp) (e': exp) (τ: typ)
  (typing: has_typ Γ e τ)
  (is_nil: Γ = cx.nil)
  (stepping: steps e e')
  : has_typ Γ e' τ :=
begin
  induction stepping generalizing Γ τ,
  let inv := inversion_if Γ stepping_e1 stepping_e2 stepping_e3 τ typing,
  apply has_typ.if_ Γ stepping_e1' stepping_e2 stepping_e3 τ,
  exact stepping_ih Γ typ.bool inv.left is_nil,
  exact inv.right.left,
  exact inv.right.right,
  let inv := inversion_if Γ exp.true stepping_e2 stepping_e3 τ typing,
  exact inv.right.left,
  let inv := inversion_if Γ exp.false stepping_e2 stepping_e3 τ typing,
  exact inv.right.right,
end
