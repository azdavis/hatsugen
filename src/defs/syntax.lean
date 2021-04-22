import defs.var

inductive typ: Type
| int: typ
| bool: typ
| arrow: typ -> typ -> typ

inductive exp: Type
| int: ℤ -> exp
| true: exp
| false: exp
| if_: exp -> exp -> exp -> exp
| var: var -> exp
| fn: var -> typ -> exp -> exp
| app: exp -> exp -> exp
