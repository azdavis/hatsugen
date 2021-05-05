import util.list.pairwise

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
