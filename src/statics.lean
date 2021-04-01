import syntax

inductive has_typ: exp -> typ -> Prop
| int (n: ℤ): has_typ (exp.int n) typ.int
| true: has_typ exp.true typ.bool
| false: has_typ exp.false typ.bool
| if_
    (cond: exp) (yes: exp) (no: exp) (t: typ):
    has_typ cond typ.bool ->
    has_typ yes t ->
    has_typ no t ->
    has_typ (exp.if_ cond yes no) t
