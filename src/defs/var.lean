import util.list.filter
import util.list.sort

-- variables. any type with infinite values and a well-behaved ≤ would work
@[reducible]
def var: Type := ℕ

structure cx_elem (t: Type): Type :=
  (x: var)
  (v: t)

def ne_var {t: Type} (a: cx_elem t) (b: cx_elem t): Prop :=
  a.x ≠ b.x

def le_var {t: Type} (a: cx_elem t) (b: cx_elem t): Prop :=
  a.x ≤ b.x

def lt_var {t: Type} (a: cx_elem t) (b: cx_elem t): Prop :=
  a.x < b.x

instance {t: Type} [has_le t]: has_le (cx_elem t) :=
  has_le.mk le_var

instance {t: Type}: has_lt (cx_elem t) := has_lt.mk lt_var

instance {t: Type}: is_symm (cx_elem t) ne_var := is_symm.mk
begin
  intros a b ab,
  simp [ne_var] at *,
  exact ne.symm ab,
end

instance huh {t: Type} [has_le t]: @decidable_rel (cx_elem t) (≤) :=
begin
  intros a b,
  exact nat.decidable_le a.x b.x,
end

instance {t: Type} [has_le t]: is_trans (cx_elem t) (≤) := is_trans.mk
begin
  intros a b c ha hb,
  simp [has_le.le] at *,
  simp [le_var] at *,
  exact is_trans.trans a.x b.x c.x ha hb,
end

instance {t: Type} [has_le t]: is_total (cx_elem t) (≤) := is_total.mk
begin
  intros a b,
  exact linear_order.le_total a.x b.x,
end

structure cx (t: Type) [has_le t]: Type :=
  (entries: list (cx_elem t))
  (nodupkeys: pairwise ne_var entries)
  (sorted: sorted entries)

def cx.empty {t: Type} [has_le t]: cx t :=
  cx.mk [] (pairwise.nil ne_var) (pairwise.nil (≤))

def cx.lookup {t: Type} [has_le t] (Γ: cx t) (x: var): option t :=
begin
  cases Γ,
  induction Γ_entries,
  exact none,
  exact (if x = Γ_entries_hd.x then
    some Γ_entries_hd.v
  else
    -- avoid weird 'can only eliminate into Prop' error when trying to use cases
    Γ_entries_ih
      (pairwise_inversion Γ_nodupkeys)
      (pairwise_inversion Γ_sorted)
  ),
end

@[reducible]
def cx.insert {t: Type} [has_le t] (x: var) (v: t) (Γ: cx t): cx t :=
begin
  cases Γ,
  let elem := cx_elem.mk x v,
  let p: cx_elem t -> Prop := fun a, x ≠ a.x,
  let entries' := insertion_sort (elem :: list.filter p Γ_entries),
  let f := fun (a: cx_elem t), fun (b: a ∈ list.filter p Γ_entries),
    (iff.elim_right filter_spec b).right,
  let nodupkeys' := insertion_sort_pairwise (@pairwise.cons
    (cx_elem t) ne_var elem (list.filter p Γ_entries) f
    (filter_pairwise p Γ_nodupkeys)),
  let sorted' := insertion_sort_spec (elem :: list.filter p Γ_entries),
  exact cx.mk entries' nodupkeys' sorted',
end

instance {t: Type} [has_le t]: has_insert (prod var t) (cx t) :=
  has_insert.mk begin
    intros a Γ,
    cases a,
    exact cx.insert a_fst a_snd Γ
  end
