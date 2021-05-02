import defs.dynamics
import defs.fv
import defs.statics
import lemmas.cx
import util.list

theorem subst_preservation
  {Γ Γ': cx typ}
  {e ex: exp}
  {x: var}
  {τ τx: typ}
  (Γ'_is: Γ' = cx.insert x τx Γ)
  (fv_ex: fv ex = [])
  (et: has_typ Γ' e τ)
  (ext: has_typ Γ ex τx)
  : has_typ Γ (subst ex x e fv_ex) τ :=
begin
  induction et,
  exact has_typ.int,
  exact has_typ.true,
  exact has_typ.false,
  let a := et_ih_a Γ'_is,
  let b := et_ih_a_1 Γ'_is,
  let c := et_ih_a_2 Γ'_is,
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
  let a := et_ih_a Γ'_is,
  let b := et_ih_a_1 Γ'_is,
  exact has_typ.app a b,
end
