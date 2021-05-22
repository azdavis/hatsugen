import defs.syntax
import defs.subst

-- e val
inductive val: exp -> Prop
| int (n: ℤ): val (exp.int n)
| true: val exp.true
| false: val exp.false
| fn (x: var) (τ: typ) (e: exp): val (exp.fn x τ e)
| unit: val exp.unit
| prod {e1 e2: exp}: val e1 -> val e2 -> val (exp.prod e1 e2)

-- e ↦ e'
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
    {x: var} {τ: typ} {e e2: exp} (fv_e2: fv e2 = []):
    val e2 ->
    steps (exp.app (exp.fn x τ e) e2) (subst e2 x fv_e2 e)
| prod_e1
    {e1 e2 e1': exp}:
    steps e1 e1' ->
    steps (exp.prod e1 e2) (exp.prod e1' e2)
| prod_e2
    {e1 e2 e2': exp}:
    val e1 ->
    steps e2 e2' ->
    steps (exp.prod e1 e2) (exp.prod e1 e2')
| prod_left_arg
    {e e': exp}:
    steps e e' ->
    steps (exp.prod_left e) (exp.prod_left e')
| prod_left_done
    {e1 e2: exp}:
    val (exp.prod e1 e2) ->
    steps (exp.prod_left (exp.prod e1 e2)) e1
| prod_right_arg
    {e e': exp}:
    steps e e' ->
    steps (exp.prod_right e) (exp.prod_right e')
| prod_right_done
    {e1 e2: exp}:
    val (exp.prod e1 e2) ->
    steps (exp.prod_right (exp.prod e1 e2)) e2
