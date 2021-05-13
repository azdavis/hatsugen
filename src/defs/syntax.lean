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
