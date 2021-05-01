import util.list

-- any type with infinite values would work
@[reducible]
def var: Type := ℕ

@[reducible]
def ne_cx_entry {t: Type} (a: prod var t) (b: prod var t): Prop :=
  a.fst ≠ b.fst

structure cx (t: Type): Type :=
  (entries: list (prod var t))
  (nodupkeys: pairwise ne_cx_entry entries)

def cx.insert {t: Type} (x: var) (v: t) (Γ: cx t): cx t :=
begin
  cases Γ,
  let p := ne_cx_entry (x, v),
  let entries' := (x, v) :: list.filter p Γ_entries,
  let spec := filter_spec p Γ_entries,
  let spec' := fun a, fun b, (spec a b).right,
  let nodupkeys' := @pairwise.cons
    (prod var t) ne_cx_entry (x, v) (list.filter p Γ_entries) spec'
    (filter_pairwise p Γ_nodupkeys),
  exact cx.mk entries' nodupkeys',
end

instance cx_has_insert {t: Type}: has_insert (prod var t) (cx t) :=
  has_insert.mk (fun a, fun Γ, begin
    cases a,
    exact cx.insert a_fst a_snd Γ
  end)

def cx.lookup {t: Type} (Γ: cx t) (x: var): option t :=
begin
  cases Γ,
  induction Γ_entries,
  exact none,
  cases Γ_entries_hd,
  exact (if x = Γ_entries_hd_fst then
    some Γ_entries_hd_snd
  else
    Γ_entries_ih (pairwise_inversion Γ_nodupkeys)
  ),
end
