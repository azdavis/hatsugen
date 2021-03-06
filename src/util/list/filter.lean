import util.list.pairwise

theorem filter_spec {t: Type} {p: t -> Prop} {xs: list t} {x: t}
  [decidable_pred p]:
  (x ∈ xs) ∧ (p x) ↔ x ∈ list.filter p xs :=
begin
  split,
  intro h,
  induction xs,
  exfalso,
  exact list.not_mem_nil x h.left,
  simp [list.filter],
  by_cases h_1: p xs_hd,
  simp [h_1],
  cases h.left,
  left,
  exact h_2,
  right,
  exact xs_ih (and.intro h_2 h.right),
  simp [h_1],
  cases h.left,
  rw h_2 at h,
  exfalso,
  exact h_1 h.right,
  exact xs_ih (and.intro h_2 h.right),  intro h,
  induction xs,
  simp [list.filter] at h,
  exfalso,
  exact h,
  simp [list.filter] at h,
  by_cases h_1: p xs_hd,
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
  by_cases p h_x,
  simp [h],
  let f: ∀ (y: t), y ∈ list.filter p h_xs -> r h_x y := fun a, fun b,
    h_a a (iff.elim_right filter_spec b).left,
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
  by_cases p xs_hd,
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
  by_cases p xs_hd,
  by_cases h_1: p' xs_hd,
  simp [h, h_1],
  exact xs_ih,
  simp [h, h_1],
  exact xs_ih,
  by_cases h_1: p' xs_hd,
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
  by_cases x = xs_hd,
  rw h at x_notin px,
  simp [px] at x_notin,
  exfalso,
  exact x_notin,
  simp,
  intro a,
  cases a,
  exact h a,
  by_cases h_1: p xs_hd,
  simp [h_1] at x_notin,
  let b := fun a, x_notin (or.inr a),
  exact xs_ih b a,
  simp [h_1] at x_notin,
  exact xs_ih x_notin a,
end
