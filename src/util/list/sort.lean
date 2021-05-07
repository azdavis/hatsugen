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

theorem insert_mem {t: Type} {xs: list t} {x y: t}
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

theorem ord_insert_mem
  {t: Type}
  [has_le t]
  [@decidable_rel t has_le.le]
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
  cases iff.elim_left insert_mem in_sort,
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
