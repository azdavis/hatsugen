import syntax

inductive cx: Type
| nil: cx
| cons: cx -> var -> typ -> cx

inductive lookup: cx -> var -> typ -> Prop
| hd (Γ: cx) (x: var) (τ: typ): lookup (cx.cons Γ x τ) x τ
| tl (Γ: cx) (x: var) (y: var) (τ: typ) (τ': typ):
    x ≠ y ->
    lookup Γ x τ ->
    lookup (cx.cons Γ y τ') x τ

inductive has_typ: cx -> exp -> typ -> Prop
| int (Γ: cx) (n: ℤ): has_typ Γ (exp.int n) typ.int
| true (Γ: cx): has_typ Γ exp.true typ.bool
| false (Γ: cx): has_typ Γ exp.false typ.bool
| if_
    (Γ: cx)
    (e1: exp) (e2: exp) (e3: exp) (τ: typ):
    has_typ Γ e1 typ.bool ->
    has_typ Γ e2 τ ->
    has_typ Γ e3 τ ->
    has_typ Γ (exp.if_ e1 e2 e3) τ
