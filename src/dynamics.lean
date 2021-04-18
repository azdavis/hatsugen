import syntax

inductive vcx: Type
| nil: vcx
| cons: vcx -> var -> val -> vcx

inductive steps: vcx -> exp -> exp -> Prop
| if_e1
    (Δ: vcx)
    (e1: exp) (e1': exp) (e2: exp) (e3: exp):
    steps Δ e1 e1' ->
    steps Δ (exp.if_ e1 e2 e3) (exp.if_ e1' e2 e3)
| if_true
    (Δ: vcx)
    (e2: exp) (e3: exp):
    steps Δ (exp.if_ (exp.pure val.true) e2 e3) e2
| if_false
    (Δ: vcx)
    (e2: exp) (e3: exp):
    steps Δ (exp.if_ (exp.pure val.false) e2 e3) e3
