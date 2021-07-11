theorem append_nil_both
  {t: Type} {xs ys: list t}: xs ++ ys = [] ↔ xs = [] ∧ ys = [] :=
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
