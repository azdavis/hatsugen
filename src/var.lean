-- any infinite set would work
def var: Type := string

@[reducible]
def cx (t: Type) := list (prod var t)

inductive lookup {t: Type}: cx t -> var -> t -> Prop
| hd (Γ: cx t) (x: var) (out: t): lookup (list.cons (prod.mk x out) Γ) x out
| tl (Γ: cx t) (x: var) (out: t) (y: var) (out_y: t):
    x ≠ y ->
    lookup Γ x out ->
    lookup (list.cons (prod.mk y out_y) Γ) x out
