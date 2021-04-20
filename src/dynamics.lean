import syntax

inductive val: exp -> Prop
| int (n: ℤ): val (exp.int n)
| true: val exp.true
| false: val exp.false

inductive steps: cx exp -> exp -> cx exp -> exp -> Prop
| if_e1
    (Δ: cx exp) (Δ': cx exp)
    (e1: exp) (e1': exp) (e2: exp) (e3: exp):
    steps Δ e1 Δ' e1' ->
    steps Δ (exp.if_ e1 e2 e3) Δ' (exp.if_ e1' e2 e3)
| if_true
    (Δ: cx exp)
    (e2: exp) (e3: exp):
    steps Δ (exp.if_ exp.true e2 e3) Δ e2
| if_false
    (Δ: cx exp)
    (e2: exp) (e3: exp):
    steps Δ (exp.if_ exp.false e2 e3) Δ e3
