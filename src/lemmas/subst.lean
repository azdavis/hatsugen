import defs.dynamics
import defs.fv
import defs.statics
import lemmas.cx
import lemmas.fv
import util.list

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

theorem fn_subst (ex: exp) (x: var) (fv_ex: fv ex = [])
  (y: var) (τ: typ) (e: exp):
  subst ex x fv_ex (exp.fn y τ e) =
  exp.fn y τ (if x = y then e else subst ex x fv_ex e) :=
begin
  simp [subst],
  -- super weird... at this point the lhs and rhs are equal so we should be
  -- done by refl but it doesn't work. but this does...?
  cases decidable.em (x = y),
  simp [h],
  simp [h],
end

theorem weakening {Γ: cx typ} {e: exp} {τ: typ} (x: var) (τx: typ):
  x ∉ fv e ->
  has_typ Γ e τ ->
  has_typ (cx.insert x τx Γ) e τ :=
begin
  intros fv_e et,
  induction et,
  exact has_typ.int,
  exact has_typ.true,
  exact has_typ.false,
  rw if_fv at fv_e,
  simp [list.append] at fv_e,
  let t_e1 := et_ih_a (fun a, fv_e (or.inl a)),
  let t_e2 := et_ih_a_1 (fun a, fv_e (or.inr (or.inl a))),
  let t_e3 := et_ih_a_2 (fun a, fv_e (or.inr (or.inr a))),
  exact has_typ.if_ t_e1 t_e2 t_e3,
  sorry,
  sorry,
  rw app_fv at fv_e,
  simp [list.append] at fv_e,
  let t_e1 := et_ih_a (fun a, fv_e (or.inl a)),
  let t_e2 := et_ih_a_1 (fun a, fv_e (or.inr a)),
  exact has_typ.app t_e1 t_e2,
end

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
  rw fn_subst,
  simp [h],
  rw Γ'_is at et_a,
  rw h at et_a,
  rw useless_insert_twice Γ et_x et_τ1 τx at et_a,
  exact has_typ.fn et_a,
  rw fn_subst,
  simp [h],
  rw Γ'_is at et_ih,
  let notin_fv_ex := list.not_mem_nil et_x,
  rw symm fv_ex at notin_fv_ex,
  let ext' := weakening et_x et_τ1 notin_fv_ex ext,
  let a := et_ih (insert_comm Γ et_x x et_τ1 τx) ext',
  exact has_typ.fn a,
  let a := et_ih_a Γ'_is ext,
  let b := et_ih_a_1 Γ'_is ext,
  exact has_typ.app a b,
end

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
  rw fn_subst,
  rw fn_fv,
  rw fn_fv,
  cases decidable.em (x = e_a),
  -- can't just `simp [h]` or else weird stuff happens with mismatched types
  rw h,
  simp,
  exact symm (filter_idempotent (ne e_a) (fv e_a_2)),
  simp [h],
  simp [e_ih],
  exact filter_comm (ne e_a) (ne x) (fv e_a_2),
  rw app_subst ex x fv_ex e_a e_a_1,
  rw app_fv (s e_a) (s e_a_1),
  rw e_ih_a,
  rw e_ih_a_1,
  rw symm (list.filter_append (fv e_a) (fv e_a_1)),
end
