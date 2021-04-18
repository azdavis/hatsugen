import syntax

inductive steps: exp -> exp -> Prop
| if_e1
    (e1: exp) (e1': exp) (e2: exp) (e3: exp):
    steps e1 e1' ->
    steps (exp.if_ e1 e2 e3) (exp.if_ e1' e2 e3)
| if_true
    (e2: exp) (e3: exp):
    steps (exp.if_ (exp.pure val.true) e2 e3) e2
| if_false
    (e2: exp) (e3: exp):
    steps (exp.if_ (exp.pure val.false) e2 e3) e3
