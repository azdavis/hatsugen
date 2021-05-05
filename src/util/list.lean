inductive pairwise {t: Type} (r: t -> t -> Prop): list t → Prop
| nil: pairwise []
| cons {x: t} {xs: list t}: (∀ y ∈ xs, r x y) -> pairwise xs -> pairwise (x :: xs)

theorem pairwise_inversion {t: Type} {r: t -> t -> Prop} {x: t} {xs: list t}:
  pairwise r (x :: xs) -> pairwise r xs :=
begin
  intro h,
  cases h,
  exact h_a_1,
end

theorem append_nil_both
  {t: Type} (xs ys: list t): xs ++ ys = [] ↔ xs = [] ∧ ys = [] :=
begin
  split,
  intro h,
  induction xs,
  induction ys,
  split,
  refl,
  refl,
  split,
  refl,
  cases h,
  cases h,
  intro h,
  cases h,
  rw h_left,
  rw h_right,
  simp [list.append],
end

theorem filter_spec {t: Type} (p: t -> Prop) (xs: list t)
  [decidable_pred p]:
  ∀ x ∈ list.filter p xs, (x ∈ xs) ∧ (p x) :=
begin
  intros x h,
  induction xs,
  simp [list.filter] at h,
  exfalso,
  exact h,
  simp [list.filter] at h,
  cases decidable.em (p xs_hd),
  simp [h_1] at h,
  cases h,
  rw h,
  split,
  simp,
  exact h_1,
  cases xs_ih h,
  split,
  simp,
  right,
  exact left,
  exact right,
  simp [h_1] at h,
  cases xs_ih h,
  split,
  simp,
  right,
  exact left,
  exact right,
end

theorem filter_pairwise {t: Type} {r: t -> t -> Prop} {xs: list t}
  (p: t -> Prop)
  [decidable_pred p]:
  pairwise r xs ->
  pairwise r (list.filter p xs) :=
begin
  intro h,
  induction h,
  simp [list.filter],
  exact pairwise.nil r,
  simp [list.filter],
  cases decidable.em (p h_x),
  simp [h],
  let f: ∀ (y: t), y ∈ list.filter p h_xs -> r h_x y := fun a, fun b,
    h_a a (filter_spec p h_xs a b).left,
  exact pairwise.cons f h_ih,
  simp [h],
  exact h_ih,
end

theorem filter_idempotent {t: Type} (p: t -> Prop) (xs: list t)
  [decidable_pred p]:
  list.filter p (list.filter p xs) = list.filter p xs :=
begin
  induction xs,
  simp [list.filter],
  simp [list.filter],
  cases decidable.em (p xs_hd),
  simp [h],
  exact xs_ih,
  simp [h],
  exact xs_ih,
end

theorem filter_comm {t: Type} (p p': t -> Prop) (xs: list t)
  [decidable_pred p]
  [decidable_pred p']:
  list.filter p (list.filter p' xs) = list.filter p' (list.filter p xs) :=
begin
  induction xs,
  simp [list.filter],
  simp [list.filter],
  cases decidable.em (p xs_hd),
  cases decidable.em (p' xs_hd),
  simp [h, h_1],
  exact xs_ih,
  simp [h, h_1],
  exact xs_ih,
  cases decidable.em (p' xs_hd),
  simp [h, h_1],
  exact xs_ih,
  simp [h, h_1],
  exact xs_ih,
end

theorem not_filter {t: Type} {p: t -> Prop} {xs: list t} {x: t}
  [decidable_pred p]
  [decidable_eq t]:
  x ∉ list.filter p xs ->
  p x ->
  x ∉ xs :=
begin
  intros x_notin px,
  induction xs,
  exact list.not_mem_nil x,
  simp [list.filter] at x_notin,
  cases decidable.em (x = xs_hd),
  rw h at x_notin px,
  simp [px] at x_notin,
  exfalso,
  exact x_notin,
  simp,
  intro a,
  cases a,
  exact h a,
  cases decidable.em (p xs_hd),
  simp [h_1] at x_notin,
  let b := fun a, x_notin (or.inr a),
  exact xs_ih b a,
  simp [h_1] at x_notin,
  exact xs_ih x_notin a,
end

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

theorem ord_insert_mem
  {t: Type}
  [has_le t]
  [@decidable_rel t has_le.le]
  [is_trans t has_le.le]
  [is_total t has_le.le]
  {x: t} {xs: list t}:
  ∀ (y ∈ ord_insert x xs), y = x ∨ y ∈ xs :=
begin
  intros y h,
  induction xs,
  simp [ord_insert] at h,
  exact or.inl h,
  simp [ord_insert] at h,
  cases decidable.em (x ≤ xs_hd),
  simp [h_1] at h,
  exact h,
  simp [h_1] at h,
  cases h,
  right,
  simp,
  exact or.inl h,
  cases xs_ih h,
  exact or.inl h_2,
  right,
  simp,
  exact or.inr h_2,
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
    cases ord_insert_mem a b,
    rw h_1,
    cases is_total.total (≤) x h_x,
    exfalso,
    exact h h_2,
    exact h_2,
    exact h_a a h_1,
  end,
  exact pairwise.cons b h_ih,
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
