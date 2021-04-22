import defs.syntax

inductive has_typ: cx typ -> exp -> typ -> Prop
| int (Γ: cx typ) (n: ℤ): has_typ Γ (exp.int n) typ.int
| true (Γ: cx typ): has_typ Γ exp.true typ.bool
| false (Γ: cx typ): has_typ Γ exp.false typ.bool
| if_
    (Γ: cx typ)
    (e1 e2 e3: exp) (τ: typ):
    has_typ Γ e1 typ.bool ->
    has_typ Γ e2 τ ->
    has_typ Γ e3 τ ->
    has_typ Γ (exp.if_ e1 e2 e3) τ
