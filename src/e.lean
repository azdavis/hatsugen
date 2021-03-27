-- The E programming language.

-- definitions

inductive exp: Type
| zero: exp
| succ: exp -> exp
| true: exp
| false: exp

inductive typ: Type
| nat: typ
| bool: typ

inductive has_typ: exp -> typ -> Prop
| zero: has_typ exp.zero typ.nat
| succ (e: exp): has_typ e typ.nat -> has_typ (exp.succ e) typ.nat
| true: has_typ exp.true typ.bool
| false: has_typ exp.false typ.bool

inductive val: exp -> Prop
| zero: val exp.zero
| succ (e: exp): val e -> val (exp.succ e)
| true: val exp.true
| false: val exp.false

inductive steps: exp -> exp -> Prop
| succ (e: exp) (e': exp): steps e e' -> steps (exp.succ e) (exp.succ e')

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

-- preservation

theorem preservation
  (e: exp) (e': exp) (t: typ)
  (typing: has_typ e t)
  (stepping: steps e e')
  : has_typ e' t :=
begin
  induction stepping,
  let inv := inversion_succ stepping_e t typing,
  let left := inv.left,
  rewrite inv.right at *,
  apply has_typ.succ stepping_e',
  exact stepping_ih left,
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
end
