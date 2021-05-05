import util.list.filter

-- variables. any type with infinite values would work
def var: Type := ℕ

structure cx_elem (t: Type): Type :=
  (x: var)
  (v: t)

def ne_var {t: Type} (a: cx_elem t) (b: cx_elem t): Prop :=
  a.x ≠ b.x

structure cx (t: Type): Type :=
  (entries: list (cx_elem t))
  (nodupkeys: pairwise ne_var entries)

def cx.empty {t: Type}: cx t := cx.mk [] (pairwise.nil ne_var)

def cx.lookup {t: Type} (Γ: cx t) (x: var): option t :=
begin
  cases Γ,
  induction Γ_entries,
  exact none,
  exact (if x = Γ_entries_hd.x then
    some Γ_entries_hd.v
  else
    -- avoid weird 'can only eliminate into Prop' error when trying to use cases
    Γ_entries_ih (pairwise_inversion Γ_nodupkeys)
  ),
end

@[reducible]
def cx.insert {t: Type} (x: var) (v: t) (Γ: cx t): cx t :=
begin
  cases Γ,
  let p: cx_elem t -> Prop := fun a, x ≠ a.x,
  let entries' := cx_elem.mk x v :: list.filter p Γ_entries,
  let f := fun a, fun b, (filter_spec p Γ_entries a b).right,
  let nodupkeys' := @pairwise.cons
    (cx_elem t) ne_var (cx_elem.mk x v) (list.filter p Γ_entries) f
    (filter_pairwise p Γ_nodupkeys),
  exact cx.mk entries' nodupkeys',
end

instance cx_has_insert {t: Type}: has_insert (prod var t) (cx t) :=
  has_insert.mk (fun a, fun Γ, begin
    cases a,
    exact cx.insert a_fst a_snd Γ
  end)
