import defs.syntax

-- Γ ⊢ e : τ
inductive has_typ: cx typ -> exp -> typ -> Prop
| int {Γ: cx typ} {n: ℤ}: has_typ Γ (exp.int n) typ.int
| true {Γ: cx typ}: has_typ Γ exp.true typ.bool
| false {Γ: cx typ}: has_typ Γ exp.false typ.bool
| if_
    {Γ: cx typ}
    {e1 e2 e3: exp} {τ: typ}:
    has_typ Γ e1 typ.bool ->
    has_typ Γ e2 τ ->
    has_typ Γ e3 τ ->
    has_typ Γ (exp.if_ e1 e2 e3) τ
| var
    {Γ: cx typ} {x: var} {τ: typ}:
    cx.lookup Γ x = some τ ->
    has_typ Γ (exp.var x) τ
| fn
    {Γ: cx typ} {x: var} {τ1 τ2: typ} {e: exp}:
    has_typ (cx.insert Γ x τ1) e τ2 ->
    has_typ Γ (exp.fn x τ1 e) (typ.arrow τ1 τ2)
| app
    {Γ: cx typ} {e1 e2: exp} {τ1 τ2: typ}:
    has_typ Γ e1 (typ.arrow τ1 τ2) ->
    has_typ Γ e2 τ1 ->
    has_typ Γ (exp.app e1 e2) τ2
