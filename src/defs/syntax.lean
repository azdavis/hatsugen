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
| (typ.arrow _ _) typ.int := false
| (typ.arrow _ _) typ.bool := false

instance typ_decidable_linear_order: decidable_linear_order typ := sorry

-- expressions
inductive exp: Type
| int: ℤ -> exp
| true: exp
| false: exp
| if_: exp -> exp -> exp -> exp
| var: var -> exp
| fn: var -> typ -> exp -> exp
| app: exp -> exp -> exp
