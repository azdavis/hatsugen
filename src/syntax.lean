inductive exp: Type
| int: ℤ -> exp
| true: exp
| false: exp
| if_: exp -> exp -> exp -> exp

inductive typ: Type
| int: typ
| bool: typ
