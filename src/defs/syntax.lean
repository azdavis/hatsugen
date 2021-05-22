import defs.var

-- types
@[derive decidable_eq]
inductive typ: Type
| int: typ
| bool: typ
| arrow: typ -> typ -> typ
| unit: typ
| prod: typ -> typ -> typ

-- expressions
inductive exp: Type
| int: ℤ -> exp
| true: exp
| false: exp
| if_: exp -> exp -> exp -> exp
| var: var -> exp
| fn: var -> typ -> exp -> exp
| app: exp -> exp -> exp
| unit: exp
| prod: exp -> exp -> exp
| prod_left: exp -> exp
| prod_right: exp -> exp
