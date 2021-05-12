import util.list.pairwise
import util.list.nil

def ord_insert
  {t: Type}
  [has_le t]
  [@decidable_rel t has_le.le]
  (x: t)
: list t -> list t
| [] := [x]
| (y :: ys) := if x ≤ y then x :: y :: ys else y :: ord_insert ys

def insertion_sort
  {t: Type}
  [has_le t]
  [@decidable_rel t has_le.le]
: list t -> list t
| [] := []
| (x :: xs) := ord_insert x (insertion_sort xs)

def sorted {t: Type} [has_le t]: list t -> Prop := pairwise (≤)

theorem ord_insert_mem {t: Type} {xs: list t} {x y: t}
  [has_le t] [@decidable_rel t has_le.le]:
  x ∈ ord_insert y xs ↔
  x = y ∨ x ∈ xs :=
begin
  split,
  intro in_ins,
  induction xs,
  simp [ord_insert] at in_ins,
  left,
  exact in_ins,
  simp [ord_insert] at in_ins,
  cases decidable.em (y ≤ xs_hd),
  simp [h] at in_ins,
  exact in_ins,
  simp [h] at in_ins,
  cases in_ins,
  right,
  simp,
  left,
  exact in_ins,
  cases xs_ih in_ins,
  left,
  exact h_1,
  right,
  simp,
  right,
  exact h_1,
  intro h,
  induction xs,
  simp [ord_insert],
  cases h,
  exact h,
  exfalso,
  exact list.not_mem_nil x h,
  simp [ord_insert],
  cases decidable.em (y ≤ xs_hd),
  simp [h_1],
  exact h,
  simp [h_1],
  cases h,
  right,
  exact xs_ih (or.inl h),
  cases h,
  left,
  exact h,
  right,
  exact xs_ih (or.inr h),
end

theorem ord_insert_spec
  {t: Type}
  [has_le t]
  [@decidable_rel t has_le.le]
  [is_trans t has_le.le]
  [is_total t has_le.le]
  (x: t) (xs: list t):
  sorted xs -> sorted (ord_insert x xs) :=
begin
  intro h,
  induction h,
  simp [ord_insert],
  exact pairwise.cons (list.ball_nil (fun y, x ≤ y)) (pairwise.nil (≤)),
  simp [ord_insert],
  cases decidable.em (x ≤ h_x),
  simp [h],
  let a: sorted (h_x :: h_xs) := pairwise.cons h_a h_a_1,
  let b: ∀ (a: t), a ∈ h_x :: h_xs -> x ≤ a := fun a, fun b,
    or.elim b
    (fun b, begin rw b, exact h end)
    (fun b, trans h (h_a a b)),
  exact pairwise.cons b a,
  simp [h],
  let b: ∀ (a: t), a ∈ ord_insert x h_xs -> h_x ≤ a := fun a, fun b,
  begin
    cases iff.elim_left ord_insert_mem b,
    rw h_1,
    cases is_total.total (≤) x h_x,
    exfalso,
    exact h h_2,
    exact h_2,
    exact h_a a h_1,
  end,
  exact pairwise.cons b h_ih,
end

theorem ord_insert_pred {t: Type} {p: t -> Prop} {xs: list t} {x: t}
  [has_le t] [@decidable_rel t has_le.le]:
  (∀ (y ∈ xs), p y) ->
  p x ->
  (∀ (y ∈ ord_insert x xs), p y) :=
begin
  intros in_xs r_xx y in_insert,
  induction xs,
  simp [ord_insert] at in_insert,
  rw in_insert,
  exact r_xx,
  simp [ord_insert] at in_insert,
  cases decidable.em (x ≤ xs_hd),
  simp [h] at in_insert,
  cases in_insert,
  rw in_insert,
  exact r_xx,
  cases in_insert,
  rw in_insert,
  exact in_xs xs_hd (or.inl rfl),
  exact in_xs y (or.inr in_insert),
  simp [h] at in_insert,
  cases in_insert,
  rw in_insert,
  exact in_xs xs_hd (or.inl rfl),
  let in_xs' := fun y, fun h, in_xs y (or.inr h),
  exact xs_ih in_xs' in_insert,
end

theorem ord_insert_pairwise {t: Type} {r: t -> t -> Prop} {xs: list t} {x: t}
  [is_symm t r] [has_le t] [@decidable_rel t has_le.le]:
  (∀ (y ∈ xs), r x y) ->
  pairwise r xs ->
  pairwise r (ord_insert x xs) :=
begin
  intros in_xs pw_xs,
  induction pw_xs,
  simp [ord_insert],
  exact pairwise.cons (list.ball_nil (fun y, r x y)) (pairwise.nil r),
  simp [ord_insert],
  cases decidable.em (x ≤ pw_xs_x),
  simp [h],
  let a := pairwise.cons pw_xs_a pw_xs_a_1,
  exact pairwise.cons in_xs a,
  simp [h],
  let in_xs' := fun y, fun h, in_xs y (or.inr h),
  let a := pw_xs_ih in_xs',
  let b := in_xs pw_xs_x (or.inl rfl),
  let c := ord_insert_pred pw_xs_a (symm b),
  exact pairwise.cons c a,
end

theorem insertion_sort_spec
  {t: Type}
  [has_le t]
  [@decidable_rel t has_le.le]
  [is_trans t has_le.le]
  [is_total t has_le.le]
  (xs: list t):
  sorted (insertion_sort xs) :=
begin
  induction xs,
  simp [insertion_sort],
  exact pairwise.nil (≤),
  simp [insertion_sort],
  exact ord_insert_spec xs_hd (insertion_sort xs_tl) xs_ih,
end

theorem insertion_sort_pred {t: Type} {p: t -> Prop} {xs: list t}
  [has_le t] [@decidable_rel t has_le.le]:
  (∀ (y ∈ xs), p y) ->
  (∀ (y ∈ insertion_sort xs), p y) :=
begin
  intros in_xs y in_sort,
  induction xs,
  simp [insertion_sort] at in_sort,
  exfalso,
  exact in_sort,
  simp [insertion_sort] at in_sort,
  cases iff.elim_left ord_insert_mem in_sort,
  rw h,
  exact in_xs xs_hd (or.inl rfl),
  let in_xs' := fun y, fun h, in_xs y (or.inr h),
  exact xs_ih in_xs' h,
end

theorem insertion_sort_pairwise {t: Type} {r: t -> t -> Prop} {xs: list t}
  [is_symm t r] [has_le t] [@decidable_rel t has_le.le]:
  pairwise r xs ->
  pairwise r (insertion_sort xs) :=
begin
  intro h,
  induction h,
  simp [insertion_sort],
  exact pairwise.nil r,
  simp [insertion_sort],
  let a := insertion_sort_pred h_a,
  simp at a,
  exact ord_insert_pairwise a h_ih,
end

theorem insertion_sort_mem {t: Type} {xs: list t} {x: t}
  [has_le t] [@decidable_rel t has_le.le]:
  x ∈ xs ↔ x ∈ insertion_sort xs :=
begin
  split,
  intro x_in,
  induction xs,
  exfalso,
  exact list.not_mem_nil x x_in,
  simp [insertion_sort],
  cases x_in,
  exact iff.elim_right ord_insert_mem (or.inl x_in),
  exact iff.elim_right ord_insert_mem (or.inr (xs_ih x_in)),
  intro x_in,
  induction xs,
  simp [insertion_sort] at x_in,
  exfalso,
  exact x_in,
  simp [insertion_sort] at x_in,
  cases iff.elim_left ord_insert_mem x_in,
  left,
  exact h,
  right,
  exact xs_ih h,
end

theorem sorted_ne_eq {t: Type} {xs ys: list t} [decidable_linear_order t]:
  (∀ (x: t), x ∈ xs ↔ x ∈ ys) ->
  pairwise ne xs ->
  pairwise ne ys ->
  sorted xs ->
  sorted ys ->
  xs = ys :=
begin
  intros x_in p_xs p_ys s_xs s_ys,
  induction xs generalizing ys,
  exact symm (iff.elim_left nothing_mem_nil (fun x xi,
    list.not_mem_nil x (iff.elim_right (x_in x) xi))),
  cases ys,
  exfalso,
  exact list.not_mem_nil xs_hd (iff.elim_left (x_in xs_hd) (or.inl rfl)),
  cases p_xs,
  cases p_ys,
  cases s_xs,
  cases s_ys,
  cases iff.elim_left (x_in xs_hd) (or.inl rfl),
  let x_in': ∀ (x: t), x ∈ xs_tl ↔ x ∈ ys_tl := begin
    intro x,
    split,
    intro xi,
    cases iff.elim_left (x_in x) (or.inr xi),
    rw symm h_1 at h,
    exfalso,
    exact p_xs_a x xi h,
    exact h_1,
    intro xi,
    cases iff.elim_right (x_in x) (or.inr xi),
    rw symm h_1 at h,
    exfalso,
    exact p_ys_a x xi (symm h),
    exact h_1,
  end,
  let a := xs_ih p_xs_a_1 s_xs_a_1 x_in' p_ys_a_1 s_ys_a_1,
  rw h,
  rw a,
  cases iff.elim_right (x_in ys_hd) (or.inl rfl),
  exfalso,
  exact p_ys_a xs_hd h h_1,
  let a := s_ys_a xs_hd h,
  let b := s_xs_a ys_hd h_1,
  exfalso,
  exact p_ys_a xs_hd h (le_antisymm a b),
end
