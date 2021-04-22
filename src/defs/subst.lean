import defs.syntax
import defs.fv

inductive subst: cx exp -> exp -> exp -> Prop
| int (Δ: cx exp) (n: ℤ): subst Δ (exp.int n) (exp.int n)
| true (Δ: cx exp): subst Δ exp.true exp.true
| false (Δ: cx exp): subst Δ exp.false exp.false
| if_
    (Δ: cx exp)
    (e1 e1' e2 e2' e3 e3': exp):
    subst Δ e1 e1' ->
    subst Δ e2 e2' ->
    subst Δ e3 e3' ->
    subst Δ (exp.if_ e1 e2 e3) (exp.if_ e1' e2' e3')
| var_same
    (Δ: cx exp) (x: var) (e': exp):
    lookup Δ x e' ->
    subst Δ (exp.var x) e'
| var_diff
    (Δ: cx exp) (x: var):
    (∀ p ∈ Δ, prod.fst p ≠ x) ->
    subst Δ (exp.var x) (exp.var x)
| fn
    (Δ: cx exp) (x x': var) (τ: typ) (e e': exp):
    (∀ a ∈ list.cons e (list.map prod.snd Δ), x' ∉ fv a) ->
    subst (list.cons (prod.mk x (exp.var x')) Δ) e e' ->
    subst Δ (exp.fn x τ e) (exp.fn x' τ e')
| app
    (Δ: cx exp)
    (e1 e1' e2 e2': exp):
    subst Δ e1 e1' ->
    subst Δ e2 e2' ->
    subst Δ (exp.app e1 e2) (exp.app e1' e2')
