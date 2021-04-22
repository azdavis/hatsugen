import defs.syntax

inductive subst: cx exp -> exp -> exp -> Prop
| int (Δ: cx exp) (n: ℤ): subst Δ (exp.int n) (exp.int n)
| true (Δ: cx exp): subst Δ exp.true exp.true
| false (Δ: cx exp): subst Δ exp.false exp.false
| if_
    (Δ: cx exp)
    (e1 e1' e2 e2' e3 e3': exp):
    subst Δ e1 e1' ->
    subst Δ e2 e2' ->
    subst Δ e3 e3' ->
    subst Δ (exp.if_ e1 e2 e3) (exp.if_ e1' e2' e3')
