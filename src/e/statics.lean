import e.syntax

inductive has_typ: exp -> typ -> Prop
| zero: has_typ exp.zero typ.nat
| succ (e: exp): has_typ e typ.nat -> has_typ (exp.succ e) typ.nat
| true: has_typ exp.true typ.bool
| false: has_typ exp.false typ.bool
| if_
    (cond: exp) (yes: exp) (no: exp) (t: typ):
    has_typ cond typ.bool ->
    has_typ yes t ->
    has_typ no t ->
    has_typ (exp.if_ cond yes no) t
