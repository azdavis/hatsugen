-- any type with infinite values would work
@[reducible]
def var: Type := ℕ

@[reducible]
def cx (t: Type) := list (prod var t)

@[reducible]
def vars {t: Type} (Γ: cx t): list var := list.map prod.fst Γ

inductive lookup {t: Type}: cx t -> var -> t -> Prop
| hd (Γ: cx t) (x: var) (out: t): lookup ((x, out) :: Γ) x out
| tl (Γ: cx t) (x: var) (out: t) (y: var) (out_y: t):
    x ≠ y ->
    lookup Γ x out ->
    lookup ((y, out_y) :: Γ) x out
