import defs.statics
import defs.dynamics
import defs.fv
import util.list

theorem has_typ_unique {Γ: cx typ} {e: exp} {τ τ': typ}:
  has_typ Γ e τ ->
  has_typ Γ e τ' ->
  τ = τ' :=
begin
  intros h1 h2,
  induction h1 generalizing τ',
  cases h2,
  refl,
  cases h2,
  refl,
  cases h2,
  refl,
  cases h2,
  exact h1_ih_a_1 h2_a_1,
  cases h2,
  rw h1_a at h2_a,
  exact option.some.inj h2_a,
  cases h2,
  rw h1_ih h2_a,
  cases h2,
  exact (typ.arrow.inj (h1_ih_a h2_a)).right,
end

theorem lookup_insert {t: Type} (Γ: cx t) (x: var) (v: t):
  cx.lookup (cx.insert x v Γ) x = some v :=
begin
  cases Γ,
  cases Γ_entries,
  simp [cx.insert],
  simp [cx.lookup],
  simp [cx.lookup],
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
  simp [cx.lookup],
  simp [h],
  cases Γ_nodupkeys,
  -- let hm := Γ_entries_ih Γ_nodupkeys_a_1,
  cases Γ_entries_hd,
  cases classical.em (x = Γ_entries_hd_fst),
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

theorem subst_preservation
  {Γ Γ': cx typ}
  {e ex e': exp}
  {x: var}
  {τ τx: typ}
  (Γ'_is: Γ' = cx.insert x τx Γ)
  (no_fv: fv ex = [])
  (et: has_typ Γ' e τ)
  (ext: has_typ Γ ex τx)
  (sub: subst ex x e no_fv = e')
  : has_typ Γ e' τ :=
begin
  rw symm sub,
  induction et generalizing e' Γ,
  exact has_typ.int,
  exact has_typ.true,
  exact has_typ.false,
  let a := et_ih_a Γ'_is ext rfl,
  let b := et_ih_a_1 Γ'_is ext rfl,
  let c := et_ih_a_2 Γ'_is ext rfl,
  exact has_typ.if_ a b c,
  rw Γ'_is at et_a,
  cases classical.em (x = et_x),
  rw h at et_a ⊢,
  rw lookup_insert Γ et_x τx at et_a,
  rw option.some.inj et_a at ext,
  simp [subst],
  exact ext,
  simp [subst, h],
  let h' := fun a, h (symm a),
  rw useless_insert_ne Γ et_x x τx h' at et_a,
  exact has_typ.var et_a,
  cases classical.em (x = et_x),
  rw h,
  simp [subst],
  rw Γ'_is at et_a,
  rw h at et_a,
  rw useless_insert_twice Γ et_x et_τ1 τx at et_a,
  exact has_typ.fn et_a,
  simp [subst],
  simp [h],
  sorry,
  let a := et_ih_a Γ'_is ext rfl,
  let b := et_ih_a_1 Γ'_is ext rfl,
  exact has_typ.app a b,
end
