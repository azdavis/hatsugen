def var: Type := string

inductive typ: Type
| int: typ
| bool: typ

inductive exp: Type
| int: ℤ -> exp
| true: exp
| false: exp
| if_: exp -> exp -> exp -> exp
