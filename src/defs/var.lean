import util.list

-- variables. any type with infinite values would work
@[reducible]
def var: Type := ℕ

@[reducible]
def ne_fst {t: Type} (a: prod var t) (b: prod var t): Prop :=
  a.fst ≠ b.fst

structure cx (t: Type): Type :=
  (entries: list (prod var t))
  (nodupkeys: pairwise ne_fst entries)

@[reducible]
def cx.empty {t: Type}: cx t := cx.mk [] (pairwise.nil ne_fst)

@[reducible]
def cx.lookup {t: Type} (Γ: cx t) (x: var): option t :=
begin
  cases Γ,
  induction Γ_entries,
  exact none,
  cases Γ_entries_hd,
  exact (if x = Γ_entries_hd_fst then
    some Γ_entries_hd_snd
  else
    -- avoid weird 'can only eliminate into Prop' error when trying to use cases
    Γ_entries_ih (pairwise_inversion Γ_nodupkeys)
  ),
end

@[reducible]
def cx.insert {t: Type} (x: var) (v: t) (Γ: cx t): cx t :=
begin
  cases Γ,
  let p: prod var t -> Prop := fun a, x ≠ a.fst,
  let entries' := (x, v) :: list.filter p Γ_entries,
  let f := fun a, fun b, (filter_spec p Γ_entries a b).right,
  let nodupkeys' := @pairwise.cons
    (prod var t) ne_fst (x, v) (list.filter p Γ_entries) f
    (filter_pairwise p Γ_nodupkeys),
  exact cx.mk entries' nodupkeys',
end

instance cx_has_insert {t: Type}: has_insert (prod var t) (cx t) :=
  has_insert.mk (fun a, fun Γ, begin
    cases a,
    exact cx.insert a_fst a_snd Γ
  end)
