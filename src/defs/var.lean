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
  if a.x = b.x then a.v ≤ b.v else a.x ≤ b.x

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
  simp at *,
  simp [cx_elem_le] at *,
  by_cases a.x = b.x,
  simp [h] at ab,
  by_cases h_1: b.x = c.x,
  simp [h_1] at bc,
  rw h_1 at h,
  simp [h],
  exact le_trans ab bc,
  simp [h_1] at bc,
  rw symm h at h_1 bc,
  simp [h_1],
  exact bc,
  simp [h] at ab,
  by_cases h_1: b.x = c.x,
  simp [h_1] at bc,
  rw h_1 at h ab,
  simp [h],
  exact ab,
  simp [h_1] at bc,
  let ab' := lt_of_le_of_ne ab h,
  let bc' := lt_of_le_of_ne bc h_1,
  let ac := lt_trans ab' bc',
  simp [ne_of_lt ac],
  exact le_trans ab bc,
end
begin
  intros a b,
  simp,
  simp [cx_elem_lt],
  simp [cx_elem_le],
  split,
  intro ab,
  by_cases a.x = b.x,
  simp [h] at ab ⊢,
  exact iff.elim_left lt_iff_le_not_le ab,
  simp [h] at ab ⊢,
  let h' := fun x, h (symm x),
  simp [h'],
  exact iff.elim_left lt_iff_le_not_le ab,
  intro ab,
  by_cases a.x = b.x,
  simp [h] at ab ⊢,
  exact iff.elim_right lt_iff_le_not_le ab,
  simp [h] at ab ⊢,
  let h' := fun x, h (symm x),
  simp [h'] at ab,
  exact iff.elim_right lt_iff_le_not_le ab,
end
begin
  intros a b ab ba,
  simp [(≤)] at ab ba,
  simp [cx_elem_le] at ab ba,
  cases a,
  cases b,
  simp at ab ba ⊢,
  by_cases a_x = b_x,
  simp [h] at ab ba,
  let eq_v := le_antisymm ab ba,
  split,
  exact h,
  exact eq_v,
  simp [h] at ab,
  let h' := fun x, h (symm x),
  simp [h'] at ba,
  exfalso,
  exact h (le_antisymm ab ba),
end
begin
  intros a b,
  simp [(≤)],
  simp [preorder.le],
  simp [cx_elem_le],
  by_cases a.x = b.x,
  simp [h],
  exact le_total a.v b.v,
  simp [h],
  let h' := fun x, h (symm x),
  simp [h'],
  exact le_total a.x b.x,
end
begin
  intros a b,
  simp [(≤)],
  simp [preorder.le],
  simp [partial_order.le],
  simp [cx_elem_le],
  by_cases a.x = b.x,
  simp [h],
  exact decidable_linear_order.decidable_le t a.v b.v,
  simp [h],
  exact nat.decidable_le a.x b.x,
end
(cx_elem.decidable_eq t)
begin
  intros a b,
  simp [(<)],
  simp [preorder.lt],
  simp [partial_order.lt],
  simp [cx_elem_lt],
  by_cases a.x = b.x,
  simp [h],
  exact decidable_linear_order.decidable_lt t a.v b.v,
  simp [h],
  exact nat.decidable_lt a.x b.x,
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
