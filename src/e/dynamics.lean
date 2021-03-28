import e.syntax

inductive val: exp -> Prop
| zero: val exp.zero
| succ (e: exp): val e -> val (exp.succ e)
| true: val exp.true
| false: val exp.false

inductive steps: exp -> exp -> Prop
| succ (e: exp) (e': exp): steps e e' -> steps (exp.succ e) (exp.succ e')
| if_cond
    (cond: exp) (cond': exp) (yes: exp) (no: exp):
    steps cond cond' ->
    steps (exp.if_ cond yes no) (exp.if_ cond' yes no)
| if_yes
    (yes: exp) (no: exp):
    steps (exp.if_ exp.true yes no) yes
| if_no
    (yes: exp) (no: exp):
    steps (exp.if_ exp.false yes no) no
