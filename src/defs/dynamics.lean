import defs.syntax

inductive val: exp -> Prop
| int (n: ℤ): val (exp.int n)
| true: val exp.true
| false: val exp.false

inductive steps: exp -> exp -> Prop
| if_e1
    (e1 e1' e2 e3: exp):
    steps e1 e1' ->
    steps (exp.if_ e1 e2 e3) (exp.if_ e1' e2 e3)
| if_true
    (e2 e3: exp):
    steps (exp.if_ exp.true e2 e3) e2
| if_false
    (e2 e3: exp):
    steps (exp.if_ exp.false e2 e3) e3