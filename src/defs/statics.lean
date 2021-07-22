import defs.syntax

structure env :=
  (exps: cx typ)

def env.insert_exp (Γ: env) (x: var) (τ: typ): env :=
  {exps := cx.insert Γ.exps x τ, ..Γ}

def env.lookup_exp (Γ: env) (x: var) (τ: typ): Prop :=
  cx.lookup Γ.exps x τ

-- Γ ⊢ e : τ
inductive has_typ: env -> exp -> typ -> Prop
| int {Γ: env} {n: ℤ}: has_typ Γ (exp.int n) typ.int
| true {Γ: env}: has_typ Γ exp.true typ.bool
| false {Γ: env}: has_typ Γ exp.false typ.bool
| if_
    {Γ: env}
    {e1 e2 e3: exp} {τ: typ}:
    has_typ Γ e1 typ.bool ->
    has_typ Γ e2 τ ->
    has_typ Γ e3 τ ->
    has_typ Γ (exp.if_ e1 e2 e3) τ
| var
    {Γ: env} {x: var} {τ: typ}:
    env.lookup_exp Γ x τ ->
    has_typ Γ (exp.var x) τ
| fn
    {Γ: env} {x: var} {τ1 τ2: typ} {e: exp}:
    has_typ (env.insert_exp Γ x τ1) e τ2 ->
    has_typ Γ (exp.fn x τ1 e) (typ.arrow τ1 τ2)
| app
    {Γ: env} {e1 e2: exp} {τ1 τ2: typ}:
    has_typ Γ e1 (typ.arrow τ1 τ2) ->
    has_typ Γ e2 τ1 ->
    has_typ Γ (exp.app e1 e2) τ2
| unit {Γ: env}: has_typ Γ exp.unit typ.unit
| pair
    {Γ: env} {e1 e2: exp} {τ1 τ2: typ}:
    has_typ Γ e1 τ1 ->
    has_typ Γ e2 τ2 ->
    has_typ Γ (exp.pair e1 e2) (typ.pair τ1 τ2)
| pair_left
    {Γ: env} {e: exp} {τ1 τ2: typ}:
    has_typ Γ e (typ.pair τ1 τ2) ->
    has_typ Γ (exp.pair_left e) τ1
| pair_right
    {Γ: env} {e: exp} {τ1 τ2: typ}:
    has_typ Γ e (typ.pair τ1 τ2) ->
    has_typ Γ (exp.pair_right e) τ2
| either_left
    {Γ: env} {e: exp} {τ1 τ2: typ}:
    has_typ Γ e τ1 ->
    has_typ Γ (exp.either_left τ2 e) (typ.either τ1 τ2)
| either_right
    {Γ: env} {e: exp} {τ1 τ2: typ}:
    has_typ Γ e τ2 ->
    has_typ Γ (exp.either_right τ1 e) (typ.either τ1 τ2)
| case_never
    {Γ: env} {e: exp} {τ: typ}:
    has_typ Γ e typ.never ->
    has_typ Γ (exp.case_never τ e) τ
| case
    {Γ: env} {eh e1 e2: exp} {x1 x2: var} {τ1 τ2 τ: typ}:
    has_typ Γ eh (typ.either τ1 τ2) ->
    has_typ (env.insert_exp Γ x1 τ1) e1 τ ->
    has_typ (env.insert_exp Γ x2 τ2) e2 τ ->
    has_typ Γ (exp.case eh x1 e1 x2 e2) τ
