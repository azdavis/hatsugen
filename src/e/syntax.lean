inductive exp: Type
| zero: exp
| succ: exp -> exp
| true: exp
| false: exp
| if_: exp -> exp -> exp -> exp

inductive typ: Type
| nat: typ
| bool: typ
