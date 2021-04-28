import defs.syntax
import defs.subst

inductive val: exp -> Prop
| int (n: ℤ): val (exp.int n)
| true: val exp.true
| false: val exp.false
| fn (x: var) (τ: typ) (e: exp): val (exp.fn x τ e)

inductive steps: exp -> exp -> Prop
| if_e1
    {e1 e2 e3 e1': exp}:
    steps e1 e1' ->
    steps (exp.if_ e1 e2 e3) (exp.if_ e1' e2 e3)
| if_true
    {e2 e3: exp}:
    steps (exp.if_ exp.true e2 e3) e2
| if_false
    {e2 e3: exp}:
    steps (exp.if_ exp.false e2 e3) e3
| app_e1
    {e1 e2 e1': exp}:
    steps e1 e1' ->
    steps (exp.app e1 e2) (exp.app e1' e2)
| app_e2
    {e1 e2 e2': exp}:
    val e1 ->
    steps e2 e2' ->
    steps (exp.app e1 e2) (exp.app e1 e2')
| app_done
    {x: var} {τ: typ} {e e2: exp} (h: fv e2 = []):
    val e2 ->
    steps (exp.app (exp.fn x τ e) e2) (subst e2 x e h)
