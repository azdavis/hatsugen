import syntax

inductive has_typ: exp -> typ -> Prop
| int (n: ℤ): has_typ (exp.int n) typ.int
| true: has_typ exp.true typ.bool
| false: has_typ exp.false typ.bool
| if_
    (e1: exp) (e2: exp) (e3: exp) (t: typ):
    has_typ e1 typ.bool ->
    has_typ e2 t ->
    has_typ e3 t ->
    has_typ (exp.if_ e1 e2 e3) t
