theorem nothing_mem_nil {t: Type} {xs: list t}: (∀ (x: t), x ∉ xs) ↔ xs = [] :=
begin
  split,
  intro h,
  induction xs,
  refl,
  exfalso,
  exact h xs_hd (or.inl rfl),
  intro h,
  rw h,
  exact list.not_mem_nil,
end
