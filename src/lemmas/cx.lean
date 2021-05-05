import defs.var

theorem lookup_insert {t: Type} (Γ: cx t) (x: var) (v: t):
  cx.lookup (cx.insert x v Γ) x = some v :=
begin
  cases Γ,
  cases Γ_entries,
  simp [cx.insert],
  simp [insertion_sort],
  simp [ord_insert],
  simp [cx.lookup],
  sorry,
end

theorem useless_insert_ne {t: Type} (Γ: cx t) (x y: var) (v: t):
  x ≠ y ->
  cx.lookup (cx.insert y v Γ) x =
  cx.lookup Γ x :=
begin
  intro h,
  cases Γ,
  induction Γ_entries,
  simp [cx.insert],
  simp [insertion_sort],
  simp [ord_insert],
  simp [cx.lookup],
  simp [h],
  cases Γ_nodupkeys,
  cases Γ_entries_hd,
  cases decidable.em (x = Γ_entries_hd_x),
  rw h_1,
  simp [cx.lookup],
  simp [h],
  sorry,
  sorry,
end

theorem useless_insert_twice {t: Type} (Γ: cx t) (x: var) (v v': t):
  cx.insert x v (cx.insert x v' Γ) = cx.insert x v Γ :=
begin
  sorry
end

theorem insert_comm {t: Type} (Γ: cx t) (x y: var) (vx vy: t):
  cx.insert x vx (cx.insert y vy Γ) =
  cx.insert y vy (cx.insert x vx Γ) :=
begin
  sorry
end
