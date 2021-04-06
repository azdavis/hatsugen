import helpers

theorem progress
  (e: exp) (τ: typ)
  (typing: has_typ e τ)
  : val e ∨ (∃ (e': exp), steps e e') :=
begin
  induction typing,
  left,
  exact (val.int typing),
  left,
  exact val.true,
  left,
  exact val.false,
  right,
  cases typing_ih_a,
  cases bool_canonical_forms typing_e1 typing_a typing_ih_a,
  existsi typing_e2,
  rewrite h,
  exact steps.if_e2 typing_e2 typing_e3,
  existsi typing_e3,
  rewrite h,
  exact steps.if_e3 typing_e2 typing_e3,
  cases typing_ih_a,
  existsi (exp.if_ typing_ih_a_w typing_e2 typing_e3),
  exact steps.if_e1 typing_e1 typing_ih_a_w typing_e2 typing_e3 typing_ih_a_h,
end

theorem preservation
  (e: exp) (e': exp) (τ: typ)
  (typing: has_typ e τ)
  (stepping: steps e e')
  : has_typ e' τ :=
begin
  induction stepping generalizing τ,
  apply has_typ.if_ stepping_e1' stepping_e2 stepping_e3 τ,
  exact stepping_ih typ.bool (inversion_if_e1 stepping_e1 stepping_e2 stepping_e3 τ typing),
  exact inversion_if_e2 stepping_e1 stepping_e2 stepping_e3 τ typing,
  exact inversion_if_e3 stepping_e1 stepping_e2 stepping_e3 τ typing,
  exact inversion_if_e2 exp.true stepping_e2 stepping_e3 τ typing,
  exact inversion_if_e3 exp.false stepping_e2 stepping_e3 τ typing,
end
