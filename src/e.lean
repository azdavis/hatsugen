-- The E programming language.

-- definitions

inductive exp: Type
| zero: exp
| succ: exp -> exp
| true: exp
| false: exp
| if_: exp -> exp -> exp -> exp

inductive typ: Type
| nat: typ
| bool: typ

inductive has_typ: exp -> typ -> Prop
| zero: has_typ exp.zero typ.nat
| succ (e: exp): has_typ e typ.nat -> has_typ (exp.succ e) typ.nat
| true: has_typ exp.true typ.bool
| false: has_typ exp.false typ.bool
| if_
    (cond: exp) (yes: exp) (no: exp) (t: typ):
    has_typ cond typ.bool ->
    has_typ yes t ->
    has_typ no t ->
    has_typ (exp.if_ cond yes no) t

inductive val: exp -> Prop
| zero: val exp.zero
| succ (e: exp): val e -> val (exp.succ e)
| true: val exp.true
| false: val exp.false

inductive steps: exp -> exp -> Prop
| succ (e: exp) (e': exp): steps e e' -> steps (exp.succ e) (exp.succ e')
| if_cond
    (cond: exp) (cond': exp) (yes: exp) (no: exp):
    steps cond cond' ->
    steps (exp.if_ cond yes no) (exp.if_ cond' yes no)
| if_yes
    (yes: exp) (no: exp):
    steps (exp.if_ exp.true yes no) yes
| if_no
    (yes: exp) (no: exp):
    steps (exp.if_ exp.false yes no) no

-- helper theorems

theorem inversion_succ
  (e: exp) (t: typ)
  (typing: has_typ (exp.succ e) t)
  : has_typ e t ∧ t = typ.nat :=
begin
  cases typing,
  split,
  exact typing_a,
  refl,
end

theorem inversion_if_cond
  (cond: exp) (yes: exp) (no: exp) (t: typ)
  (typing: has_typ (exp.if_ cond yes no) t)
  : has_typ cond typ.bool :=
begin
  cases typing,
  exact typing_a,
end

theorem inversion_if_yes
  (cond: exp) (yes: exp) (no: exp) (t: typ)
  (typing: has_typ (exp.if_ cond yes no) t)
  : has_typ yes t :=
begin
  cases typing,
  exact typing_a_1,
end

theorem inversion_if_no
  (cond: exp) (yes: exp) (no: exp) (t: typ)
  (typing: has_typ (exp.if_ cond yes no) t)
  : has_typ no t :=
begin
  cases typing,
  exact typing_a_2,
end

theorem bool_canonical_forms
  (e: exp)
  (typing: has_typ e typ.bool)
  (value: val e)
  : e = exp.true ∨ e = exp.false :=
begin
  cases typing,
  left,
  refl,
  right,
  refl,
  cases value,
end

-- preservation

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

-- progress

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
