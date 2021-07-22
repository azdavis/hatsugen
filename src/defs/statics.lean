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
    cx.lookup Γ x τ ->
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
| unit {Γ: cx typ}: has_typ Γ exp.unit typ.unit
| pair
    {Γ: cx typ} {e1 e2: exp} {τ1 τ2: typ}:
    has_typ Γ e1 τ1 ->
    has_typ Γ e2 τ2 ->
    has_typ Γ (exp.pair e1 e2) (typ.pair τ1 τ2)
| pair_left
    {Γ: cx typ} {e: exp} {τ1 τ2: typ}:
    has_typ Γ e (typ.pair τ1 τ2) ->
    has_typ Γ (exp.pair_left e) τ1
| pair_right
    {Γ: cx typ} {e: exp} {τ1 τ2: typ}:
    has_typ Γ e (typ.pair τ1 τ2) ->
    has_typ Γ (exp.pair_right e) τ2
| either_left
    {Γ: cx typ} {e: exp} {τ1 τ2: typ}:
    has_typ Γ e τ1 ->
    has_typ Γ (exp.either_left τ2 e) (typ.either τ1 τ2)
| either_right
    {Γ: cx typ} {e: exp} {τ1 τ2: typ}:
    has_typ Γ e τ2 ->
    has_typ Γ (exp.either_right τ1 e) (typ.either τ1 τ2)
| case_never
    {Γ: cx typ} {e: exp} {τ: typ}:
    has_typ Γ e typ.never ->
    has_typ Γ (exp.case_never τ e) τ
| case
    {Γ: cx typ} {eh e1 e2: exp} {x1 x2: var} {τ1 τ2 τ: typ}:
    has_typ Γ eh (typ.either τ1 τ2) ->
    has_typ (cx.insert Γ x1 τ1) e1 τ ->
    has_typ (cx.insert Γ x2 τ2) e2 τ ->
    has_typ Γ (exp.case eh x1 e1 x2 e2) τ
