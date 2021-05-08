import defs.var

theorem lookup_mem_entries {t: Type} (Γ: cx t) (x: var) (v: t):
  cx_elem.mk x v ∈ Γ.entries ->
  cx.lookup Γ x = some v :=
begin
  cases Γ,
  intro h,
  simp at h,
  induction Γ_entries,
  exfalso,
  exact list.not_mem_nil (cx_elem.mk x v) h,
  cases h,
  cases Γ_entries_hd,
  simp [cx.lookup],
  cases cx_elem.mk.inj h,
  simp [left],
  exact symm right,
  cases Γ_nodupkeys,
  let a := Γ_nodupkeys_a (cx_elem.mk x v) h,
  simp [ne_var] at a,
  let a' := fun x, a (symm x),
  simp [cx.lookup],
  simp [a'],
  exact Γ_entries_ih Γ_nodupkeys_a_1 h,
end

theorem lookup_insert {t: Type} (Γ: cx t) (x: var) (v: t):
  cx.lookup (cx.insert x v Γ) x = some v :=
begin
  cases Γ,
  induction Γ_entries,
  simp [cx.insert],
  simp [insertion_sort],
  simp [ord_insert],
  simp [cx.lookup],
  cases Γ_nodupkeys,
  simp [cx.insert],
  /-
  cases decidable.em (x = Γ_entries_hd.x),
  simp [h],
  let a := Γ_entries_ih Γ_nodupkeys_a_1,
   -/
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
