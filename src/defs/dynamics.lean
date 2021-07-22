import defs.syntax
import defs.subst

-- e val
inductive val: exp -> Prop
| int (n: ℤ): val (exp.int n)
| true: val exp.true
| false: val exp.false
| fn (x: var) (τ: typ) (e: exp): val (exp.fn x τ e)
| unit: val exp.unit
| pair {e1 e2: exp}: val e1 -> val e2 -> val (exp.pair e1 e2)
| either_left {τ: typ} {e: exp}: val e -> val (exp.either_left τ e)
| either_right {τ: typ} {e: exp}: val e -> val (exp.either_right τ e)

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
| pair_e1
    {e1 e2 e1': exp}:
    steps e1 e1' ->
    steps (exp.pair e1 e2) (exp.pair e1' e2)
| pair_e2
    {e1 e2 e2': exp}:
    val e1 ->
    steps e2 e2' ->
    steps (exp.pair e1 e2) (exp.pair e1 e2')
| pair_left_arg
    {e e': exp}:
    steps e e' ->
    steps (exp.pair_left e) (exp.pair_left e')
| pair_left_done
    {e1 e2: exp}:
    val (exp.pair e1 e2) ->
    steps (exp.pair_left (exp.pair e1 e2)) e1
| pair_right_arg
    {e e': exp}:
    steps e e' ->
    steps (exp.pair_right e) (exp.pair_right e')
| pair_right_done
    {e1 e2: exp}:
    val (exp.pair e1 e2) ->
    steps (exp.pair_right (exp.pair e1 e2)) e2
| either_left_arg
    {τ: typ} {e e': exp}:
    steps e e' ->
    steps (exp.either_left τ e) (exp.either_left τ e')
| either_right_arg
    {τ: typ} {e e': exp}:
    steps e e' ->
    steps (exp.either_right τ e) (exp.either_right τ e')
| case_never_arg
    {τ: typ} {e e': exp}:
    steps e e' ->
    steps (exp.case_never τ e) (exp.case_never τ e')
| case_arg
    {eh eh' e1 e2: exp} {x1 x2: var}:
    steps eh eh' ->
    steps (exp.case eh x1 e1 x2 e2) (exp.case eh' x1 e1 x2 e2)
| case_done_left
    {τ: typ} {e e1 e2: exp} {x1 x2: var} (fv_e: fv e = []):
    val (exp.either_left τ e) ->
    steps (exp.case (exp.either_left τ e) x1 e1 x2 e2) (subst e x1 fv_e e1)
| case_done_right
    {τ: typ} {e e1 e2: exp} {x1 x2: var} (fv_e: fv e = []):
    val (exp.either_right τ e) ->
    steps (exp.case (exp.either_right τ e) x1 e1 x2 e2) (subst e x2 fv_e e2)
