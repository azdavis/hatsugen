import defs.dynamics
import defs.fv
import defs.statics
import lemmas.cx
import lemmas.fv
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
  : has_typ Γ (subst ex x fv_ex e) τ :=
begin
  induction et generalizing Γ,
  exact has_typ.int,
  exact has_typ.true,
  exact has_typ.false,
  let a := et_ih_a Γ'_is ext,
  let b := et_ih_a_1 Γ'_is ext,
  let c := et_ih_a_2 Γ'_is ext,
  exact has_typ.if_ a b c,
  rw Γ'_is at et_a,
  cases decidable.em (x = et_x),
  rw h at et_a ⊢,
  rw lookup_insert Γ et_x τx at et_a,
  rw option.some.inj et_a at ext,
  simp [subst],
  exact ext,
  simp [subst, h],
  let h' := fun a, h (symm a),
  rw useless_insert_ne Γ et_x x τx h' at et_a,
  exact has_typ.var et_a,
  cases decidable.em (x = et_x),
  rw h,
  simp [subst],
  rw Γ'_is at et_a,
  rw h at et_a,
  rw useless_insert_twice Γ et_x et_τ1 τx at et_a,
  exact has_typ.fn et_a,
  simp [subst],
  simp [h],
  sorry,
  let a := et_ih_a Γ'_is ext,
  let b := et_ih_a_1 Γ'_is ext,
  exact has_typ.app a b,
end

theorem if_subst (ex: exp) (x: var) (fv_ex: fv ex = []) (e1 e2 e3: exp):
  subst ex x fv_ex (exp.if_ e1 e2 e3) =
    exp.if_
    (subst ex x fv_ex e1)
    (subst ex x fv_ex e2)
    (subst ex x fv_ex e3)
  := by simp [subst]

theorem app_subst (ex: exp) (x: var) (fv_ex: fv ex = []) (e1 e2: exp):
  subst ex x fv_ex (exp.app e1 e2) =
    exp.app
    (subst ex x fv_ex e1)
    (subst ex x fv_ex e2)
  := by simp [subst]

theorem subst_fv (ex: exp) (x: var) (fv_ex: fv ex = []) (e: exp):
  fv (subst ex x fv_ex e) = list.filter (ne x) (fv e) :=
begin
  let s := subst ex x fv_ex,
  induction e,
  simp [subst],
  simp [subst],
  simp [subst],
  rw if_subst ex x fv_ex e_a e_a_1 e_a_2,
  rw if_fv (s e_a) (s e_a_1) (s e_a_2),
  rw e_ih_a,
  rw e_ih_a_1,
  rw e_ih_a_2,
  rw symm (list.filter_append (fv e_a_1) (fv e_a_2)),
  rw symm (list.filter_append (fv e_a) (fv e_a_1 ++ fv e_a_2)),
  simp [subst],
  cases decidable.em (x = e),
  rw h,
  simp [list.filter, subst],
  exact fv_ex,
  simp [h],
  sorry,
  rw app_subst ex x fv_ex e_a e_a_1,
  rw app_fv (s e_a) (s e_a_1),
  rw e_ih_a,
  rw e_ih_a_1,
  rw symm (list.filter_append (fv e_a) (fv e_a_1)),
end
