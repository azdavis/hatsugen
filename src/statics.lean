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

inductive val_typ: cx -> val -> typ -> Prop
| int (Γ: cx) (n: ℤ): val_typ Γ (val.int n) typ.int
| true (Γ: cx): val_typ Γ val.true typ.bool
| false (Γ: cx): val_typ Γ val.false typ.bool

inductive exp_typ: cx -> exp -> typ -> Prop
| pure
    (Γ: cx) (v: val) (τ: typ):
    val_typ Γ v τ ->
    exp_typ Γ (exp.pure v) τ
| if_
    (Γ: cx)
    (e1: exp) (e2: exp) (e3: exp) (τ: typ):
    exp_typ Γ e1 typ.bool ->
    exp_typ Γ e2 τ ->
    exp_typ Γ e3 τ ->
    exp_typ Γ (exp.if_ e1 e2 e3) τ
