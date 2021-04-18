import var

inductive typ: Type
| int: typ
| bool: typ

inductive val: Type
| int: ℤ -> val
| true: val
| false: val

inductive exp: Type
| pure: val -> exp
| if_: exp -> exp -> exp -> exp
