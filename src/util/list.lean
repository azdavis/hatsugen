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
