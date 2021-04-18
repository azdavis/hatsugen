import syntax

inductive val_typ: cx typ -> val -> typ -> Prop
| int (Γ: cx typ) (n: ℤ): val_typ Γ (val.int n) typ.int
| true (Γ: cx typ): val_typ Γ val.true typ.bool
| false (Γ: cx typ): val_typ Γ val.false typ.bool

inductive exp_typ: cx typ -> exp -> typ -> Prop
| pure
    (Γ: cx typ) (v: val) (τ: typ):
    val_typ Γ v τ ->
    exp_typ Γ (exp.pure v) τ
| if_
    (Γ: cx typ)
    (e1: exp) (e2: exp) (e3: exp) (τ: typ):
    exp_typ Γ e1 typ.bool ->
    exp_typ Γ e2 τ ->
    exp_typ Γ e3 τ ->
    exp_typ Γ (exp.if_ e1 e2 e3) τ
