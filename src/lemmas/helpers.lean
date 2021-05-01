import defs.dynamics
import defs.fv
import defs.statics
import lemmas.cx
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
