import e.statics
import e.dynamics

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
