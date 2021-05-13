import defs.var

-- types
@[derive decidable_eq]
inductive typ: Type
| int: typ
| bool: typ
| arrow: typ -> typ -> typ

def typ_lt: typ -> typ -> Prop
| typ.int typ.int := false
| typ.int _ := true
| typ.bool typ.bool := false
| typ.bool typ.int := false
| typ.bool _ := true
| (typ.arrow a b) (typ.arrow c d) := if a = c then typ_lt b d else typ_lt a c
| (typ.arrow _ _) _ := false

def typ_le (a b: typ): Prop := (a = b) ∨ (typ_lt a b)

theorem typ_lt_arrow {a b t: typ}:
  typ_lt (typ.arrow a b) t ->
  ∃ (c d: typ), t = typ.arrow c d ∧ (if a = c then typ_lt b d else typ_lt a c) :=
begin
  intro h,
  cases t,
  simp [typ_lt] at h,
  exfalso,
  exact h,
  simp [typ_lt] at h,
  exfalso,
  exact h,
  simp [typ_lt] at h,
  existsi t_a,
  existsi t_a_1,
  split,
  refl,
  exact h,
end

instance typ_decidable_linear_order: decidable_linear_order typ :=
decidable_linear_order.mk
typ_le
typ_lt
begin
  intro a,
  simp,
  simp [typ_le],
end
begin
  intros a b c ab bc,
  simp [(≤)] at *,
  simp [typ_le] at *,
  cases ab,
  cases bc,
  rw bc at ab,
  left,
  exact ab,
  rw symm ab at bc,
  right,
  exact bc,
  cases bc,
  rw bc at ab,
  right,
  exact ab,
  -- hm
  right,
  induction a generalizing b c,
  cases b,
  simp [typ_lt] at ab,
  exfalso,
  exact ab,
  cases c,
  simp [typ_lt] at bc,
  exfalso,
  exact bc,
  simp [typ_lt] at bc,
  simp [typ_lt] at bc,
  cases typ_lt_arrow bc,
  cases h,
  rw h_h.left,
  simp [typ_lt],
  cases b,
  simp [typ_lt] at ab,
  exfalso,
  exact ab,
  simp [typ_lt] at ab,
  exfalso,
  exact ab,
  cases typ_lt_arrow bc,
  cases h,
  rw h_h.left,
  simp [typ_lt],
  -- don't need?
  induction b generalizing c,
  simp [typ_lt] at ab,
  exfalso,
  exact ab,
  simp [typ_lt] at ab,
  exfalso,
  exact ab,
  simp [typ_lt] at ab,
  cases typ_lt_arrow bc,
  cases h,
  cases h_h,
  rw h_h_left at *,
  by_cases h1: a_a = b_a,
  rw h1 at *,
  simp at ab,
  by_cases h2: b_a = w,
  rw h2 at *,
  simp at h_h_right,
  simp [typ_lt],
  exact a_ih_a_1 b_a_1 h_w ab h_h_right,
  simp [h2] at h_h_right,
  simp [typ_lt],
  simp [h2],
  exact h_h_right,
  simp [h1] at ab,
  by_cases h2: b_a = w,
  rw h2 at *,
  simp at h_h_right,
  simp [typ_lt],
  simp [h1],
  exact ab,
  simp [h2] at h_h_right,
  simp [typ_lt],
  by_cases h3: a_a = w,
  simp [h3],
  sorry,
  sorry,
end
begin
  intros a b,
  sorry,
end
begin
  intros a b ab ba,
  sorry,
end
begin
  intros a b,
  sorry,
end
begin
  intros a b,
  sorry,
end
typ.decidable_eq
begin
  intros a b,
  sorry,
end

-- expressions
inductive exp: Type
| int: ℤ -> exp
| true: exp
| false: exp
| if_: exp -> exp -> exp -> exp
| var: var -> exp
| fn: var -> typ -> exp -> exp
| app: exp -> exp -> exp
