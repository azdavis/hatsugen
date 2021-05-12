import util.list.filter
import util.list.sort

-- variables. any type with infinite values and a well-behaved ≤ would work
@[reducible]
def var: Type := ℕ

@[derive decidable_eq]
structure cx_elem (t: Type): Type :=
  (x: var)
  (v: t)

def ne_var {t: Type} (a: cx_elem t) (b: cx_elem t): Prop :=
  a.x ≠ b.x

instance {t: Type}: is_symm (cx_elem t) ne_var := is_symm.mk
begin
  intros a b ab,
  simp [ne_var] at *,
  exact ne.symm ab,
end

def cx_elem_lt {t: Type} [decidable_linear_order t] (a b: cx_elem t): Prop :=
  if a.x = b.x then a.v < b.v else a.x < b.x

def cx_elem_le {t: Type} [decidable_linear_order t] (a b: cx_elem t): Prop :=
  (a = b) ∨ (cx_elem_lt a b)

instance cx_elem_decidable_linear_order {t: Type} [decidable_linear_order t]:
decidable_linear_order (cx_elem t) :=
decidable_linear_order.mk
cx_elem_le
cx_elem_lt
begin
  intro a,
  simp,
  simp [cx_elem_le],
end
begin
  intros a b c ab bc,
  sorry,
end
begin
  intros a b,
  sorry,
end
begin
  intros a b ab ba,
  sorry,
end
begin
  intros a b,
  sorry,
end
begin
  intros a b,
  sorry,
end
(cx_elem.decidable_eq t)
begin
  intros a b,
  sorry,
end

structure cx (t: Type) [decidable_linear_order t]: Type :=
  (entries: list (cx_elem t))
  (nodupkeys: pairwise ne_var entries)
  (sorted: sorted entries)

def cx.empty {t: Type} [decidable_linear_order t]: cx t :=
  cx.mk [] (pairwise.nil ne_var) (pairwise.nil (≤))

def cx.lookup {t: Type} [decidable_linear_order t] (Γ: cx t) (x: var): option t :=
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
def cx.insert {t: Type} [decidable_linear_order t] (x: var) (v: t) (Γ: cx t): cx t :=
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

instance {t: Type} [decidable_linear_order t]: has_insert (prod var t) (cx t) :=
  has_insert.mk begin
    intros a Γ,
    cases a,
    exact cx.insert a_fst a_snd Γ
  end
