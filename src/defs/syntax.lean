import defs.var

-- types
@[derive decidable_eq]
inductive typ: Type
| int: typ
| bool: typ
| arrow: typ -> typ -> typ
| unit: typ
| pair: typ -> typ -> typ
| never: typ
| either: typ -> typ -> typ

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
| pair: exp -> exp -> exp
| pair_left: exp -> exp
| pair_right: exp -> exp
| either_left: typ -> exp -> exp
| either_right: typ -> exp -> exp
| case_never: typ -> exp -> exp
| case: exp -> var -> exp -> var -> exp -> exp
