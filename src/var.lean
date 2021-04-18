-- any infinite set would work
def var: Type := string

inductive cx (t: Type): Type
| nil: cx
| cons: cx -> var -> t -> cx

inductive lookup (t: Type): cx t -> var -> t -> Prop
| hd (Γ: cx t) (x: var) (out: t): lookup (cx.cons Γ x out) x out
| tl (Γ: cx t) (x: var) (out: t) (y: var) (out_y: t):
    x ≠ y ->
    lookup Γ x out ->
    lookup (cx.cons Γ y out_y) x out
