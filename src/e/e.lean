import e.helpers

theorem preservation
  (e: exp) (e': exp) (t: typ)
  (typing: has_typ e t)
  (stepping: steps e e')
  : has_typ e' t :=
begin
  induction stepping generalizing t,
  let inv := inversion_succ stepping_e t typing,
  let left := inv.left,
  rewrite inv.right at *,
  apply has_typ.succ stepping_e',
  exact stepping_ih typ.nat left,
  let inv := inversion_if_cond stepping_cond stepping_yes stepping_no t typing,
  apply has_typ.if_ stepping_cond' stepping_yes stepping_no t,
  exact stepping_ih typ.bool inv,
  exact inversion_if_yes stepping_cond stepping_yes stepping_no t typing,
  exact inversion_if_no stepping_cond stepping_yes stepping_no t typing,
  exact inversion_if_yes exp.true stepping_yes stepping_no t typing,
  exact inversion_if_no exp.false stepping_yes stepping_no t typing,
end

theorem progress
  (e: exp) (t: typ)
  (typing: has_typ e t)
  : val e ∨ (∃ (e': exp), steps e e') :=
begin
  induction typing,
  left,
  exact val.zero,
  cases typing_ih,
  left,
  exact val.succ typing_e typing_ih,
  right,
  cases typing_ih,
  existsi exp.succ typing_ih_w,
  exact steps.succ typing_e typing_ih_w typing_ih_h,
  left,
  exact val.true,
  left,
  exact val.false,
  right,
  cases typing_ih_a,
  cases bool_canonical_forms typing_cond typing_a typing_ih_a,
  existsi typing_yes,
  rewrite h,
  exact steps.if_yes typing_yes typing_no,
  existsi typing_no,
  rewrite h,
  exact steps.if_no typing_yes typing_no,
  cases typing_ih_a,
  existsi (exp.if_ typing_ih_a_w typing_yes typing_no),
  exact steps.if_cond typing_cond typing_ih_a_w typing_yes typing_no typing_ih_a_h,
end
