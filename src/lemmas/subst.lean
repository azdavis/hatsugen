import defs.dynamics
import defs.fv
import defs.statics
import lemmas.cx
import lemmas.fv

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
  by_cases x = y,
  simp [h],
  simp [h],
end

theorem pair_subst (ex: exp) (x: var) (fv_ex: fv ex = []) (e1 e2: exp):
  subst ex x fv_ex (exp.pair e1 e2) =
    exp.pair
    (subst ex x fv_ex e1)
    (subst ex x fv_ex e2)
  := by simp [subst]

theorem pair_left_subst (ex: exp) (x: var) (fv_ex: fv ex = []) (e: exp):
  subst ex x fv_ex (exp.pair_left e) = exp.pair_left (subst ex x fv_ex e)
  := by simp [subst]

theorem pair_right_subst (ex: exp) (x: var) (fv_ex: fv ex = []) (e: exp):
  subst ex x fv_ex (exp.pair_right e) = exp.pair_right (subst ex x fv_ex e)
  := by simp [subst]

theorem either_left_subst {τ: typ} (ex: exp) (x: var) (fv_ex: fv ex = []) (e: exp):
  subst ex x fv_ex (exp.either_left τ e) = exp.either_left τ (subst ex x fv_ex e)
  := by simp [subst]

theorem either_right_subst {τ: typ} (ex: exp) (x: var) (fv_ex: fv ex = []) (e: exp):
  subst ex x fv_ex (exp.either_right τ e) = exp.either_right τ (subst ex x fv_ex e)
  := by simp [subst]

theorem case_never_subst {τ: typ} (ex: exp) (x: var) (fv_ex: fv ex = []) (e: exp):
  subst ex x fv_ex (exp.case_never τ e) = exp.case_never τ (subst ex x fv_ex e)
  := by simp [subst]

theorem case_subst (ex: exp) (x: var) (fv_ex: fv ex = [])
  (eh e1 e2: exp) (x1 x2: var):
  subst ex x fv_ex (exp.case eh x1 e1 x2 e2) =
  exp.case
    (subst ex x fv_ex eh)
    x1 (if x = x1 then e1 else subst ex x fv_ex e1)
    x2 (if x = x2 then e2 else subst ex x fv_ex e2)
   :=
begin
  simp [subst],
  -- same as in fn_subst...?
  by_cases h1: x = x1,
  simp [h1],
  by_cases h2: x1 = x2,
  simp [h2],
  simp [h2],
  simp [h1],
  by_cases h2: x = x2,
  simp [h2],
  simp [h2],
end

theorem weakening_var_helper {Γ: env} {x x': var} {τ1 τ2 τ: typ} {e: exp}:
  has_typ (env.insert_exp Γ x' τ1) e τ2 ->
  (x ∉ fv e -> has_typ (env.insert_exp (env.insert_exp Γ x' τ1) x τ) e τ2) ->
  x ∉ list.filter (ne x') (fv e) ->
  has_typ (env.insert_exp (env.insert_exp Γ x τ) x' τ1) e τ2 :=
begin
  intros et ih fv_e,
  by_cases x = x',
  let a := useless_insert_twice Γ.exps x τ1 τ,
  rw symm h at et ⊢,
  simp [env.insert_exp] at et,
  rw symm a at et,
  exact et,
  let b := ih (not_filter fv_e (fun a, h (symm a))),
  simp [env.insert_exp] at b,
  rw insert_comm Γ.exps x x' τ τ1 h at b,
  exact b,
end

theorem weakening {Γ: env} {e: exp} {τ: typ} (x: var) (τx: typ):
  x ∉ fv e ->
  has_typ Γ e τ ->
  has_typ (env.insert_exp Γ x τx) e τ :=
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
  simp [fv] at fv_e,
  let var_ne := fun a, fv_e (symm a),
  exact has_typ.var (iff.elim_right (useless_insert_ne var_ne) et_a),
  rw fn_fv at fv_e,
  exact has_typ.fn (weakening_var_helper et_a et_ih fv_e),
  rw app_fv at fv_e,
  simp [list.append] at fv_e,
  let t_e1 := et_ih_a (fun a, fv_e (or.inl a)),
  let t_e2 := et_ih_a_1 (fun a, fv_e (or.inr a)),
  exact has_typ.app t_e1 t_e2,
  exact has_typ.unit,
  rw pair_fv at fv_e,
  simp [list.append] at fv_e,
  let t_e1 := et_ih_a (fun a, fv_e (or.inl a)),
  let t_e2 := et_ih_a_1 (fun a, fv_e (or.inr a)),
  exact has_typ.pair t_e1 t_e2,
  rw pair_left_fv at fv_e,
  exact has_typ.pair_left (et_ih fv_e),
  rw pair_right_fv at fv_e,
  exact has_typ.pair_right (et_ih fv_e),
  rw either_left_fv at fv_e,
  exact has_typ.either_left (et_ih fv_e),
  rw either_right_fv at fv_e,
  exact has_typ.either_right (et_ih fv_e),
  rw case_never_fv at fv_e,
  exact has_typ.case_never (et_ih fv_e),
  rw case_fv at fv_e,
  simp [list.append] at fv_e,
  let t_eh := et_ih_a (fun a, fv_e (or.inl a)),
  let fv_et_e1 := fun a, fv_e (or.inr (or.inl a)),
  let t_e1 := weakening_var_helper et_a_1 et_ih_a_1 fv_et_e1,
  let fv_et_e2 := fun a, fv_e (or.inr (or.inr a)),
  let t_e2 := weakening_var_helper et_a_2 et_ih_a_2 fv_et_e2,
  exact has_typ.case t_eh t_e1 t_e2,
end

theorem subst_preservation_var_helper
  {Γ Γ': env} {x x': var} {τ1 τ2 τx: typ}
  {ex e: exp} (fv_ex: fv ex = []):
  Γ' = env.insert_exp Γ x τx ->
  has_typ (env.insert_exp Γ' x' τ1) e τ2 ->
  has_typ Γ ex τx ->
  (∀ {Γ : env},
    env.insert_exp Γ' x' τ1 = env.insert_exp Γ x τx →
    has_typ Γ ex τx → has_typ Γ (subst ex x fv_ex e) τ2) ->
  has_typ (env.insert_exp Γ x' τ1) (ite (x = x') e (subst ex x fv_ex e)) τ2 :=
begin
  intros Γ'_is et ext ih,
  by_cases x = x',
  simp [h],
  rw Γ'_is at et,
  rw h at et,
  simp [env.insert_exp] at et,
  rw useless_insert_twice Γ.exps x' τ1 τx at et,
  exact et,
  simp [h],
  rw Γ'_is at ih,
  let notin_fv_ex := list.not_mem_nil x',
  rw symm fv_ex at notin_fv_ex,
  let ext' := weakening x' τ1 notin_fv_ex ext,
  simp [env.insert_exp] at ih,
  let a := insert_comm Γ.exps x' x τ1 τx (fun a, h (symm a)),
  exact @ih (env.insert_exp Γ x' τ1) a ext',
end

theorem subst_preservation
  {Γ Γ': env}
  {e ex: exp}
  {x: var}
  {τ τx: typ}
  (Γ'_is: Γ' = env.insert_exp Γ x τx)
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
  by_cases x = et_x,
  rw h at et_a ⊢,
  rw lookup_uniq (lookup_insert Γ.exps et_x τx) et_a at ext,
  simp [subst],
  exact ext,
  simp [subst, h],
  let h' := fun a, h (symm a),
  let hm := iff.elim_left (useless_insert_ne h') et_a,
  exact has_typ.var hm,
  rw fn_subst,
  let a := subst_preservation_var_helper fv_ex Γ'_is et_a ext @et_ih,
  exact has_typ.fn a,
  let a := et_ih_a Γ'_is ext,
  let b := et_ih_a_1 Γ'_is ext,
  exact has_typ.app a b,
  exact has_typ.unit,
  let a := et_ih_a Γ'_is ext,
  let b := et_ih_a_1 Γ'_is ext,
  exact has_typ.pair a b,
  exact has_typ.pair_left (et_ih Γ'_is ext),
  exact has_typ.pair_right (et_ih Γ'_is ext),
  exact has_typ.either_left (et_ih Γ'_is ext),
  exact has_typ.either_right (et_ih Γ'_is ext),
  exact has_typ.case_never (et_ih Γ'_is ext),
  rw case_subst,
  let t_e1 := subst_preservation_var_helper fv_ex Γ'_is et_a_1 ext @et_ih_a_1,
  let t_e2 := subst_preservation_var_helper fv_ex Γ'_is et_a_2 ext @et_ih_a_2,
  exact has_typ.case (et_ih_a Γ'_is ext) t_e1 t_e2,
end

theorem subst_fv_var_helper {x x': var} {ex e: exp} (fv_ex: fv ex = []):
  fv (subst ex x fv_ex e) = list.filter (ne x) (fv e) ->
  list.filter (ne x') (fv (ite (x = x') e (subst ex x fv_ex e))) =
  list.filter (ne x) (list.filter (ne x') (fv e)) :=
begin
  intro ih,
  by_cases x = x',
  -- can't just `simp [h]` or else weird stuff happens with mismatched types
  rw h,
  simp,
  exact symm (filter_idempotent (ne x') (fv e)),
  simp [h],
  simp [ih],
  exact filter_comm (ne x') (ne x) (fv e),
end

theorem subst_fv (ex: exp) (x: var) (fv_ex: fv ex = []) (e: exp):
  fv (subst ex x fv_ex e) = list.filter (ne x) (fv e) :=
begin
  let s := subst ex x fv_ex,
  induction e,
  simp [subst, fv],
  simp [subst, fv],
  simp [subst, fv],
  rw if_subst ex x fv_ex e_a e_a_1 e_a_2,
  rw if_fv (s e_a) (s e_a_1) (s e_a_2),
  rw e_ih_a,
  rw e_ih_a_1,
  rw e_ih_a_2,
  rw symm (list.filter_append (fv e_a_1) (fv e_a_2)),
  rw symm (list.filter_append (fv e_a) (fv e_a_1 ++ fv e_a_2)),
  simp [subst, fv],
  by_cases x = e,
  rw h,
  simp [subst, var_fv],
  exact fv_ex,
  simp [fv, subst, h],
  simp [fn_subst, fn_fv],
  exact subst_fv_var_helper fv_ex e_ih,
  rw app_subst ex x fv_ex e_a e_a_1,
  rw app_fv (s e_a) (s e_a_1),
  rw e_ih_a,
  rw e_ih_a_1,
  rw symm (list.filter_append (fv e_a) (fv e_a_1)),
  rw symm (app_fv e_a e_a_1),
  simp [subst, fv],
  simp [pair_subst],
  simp [pair_fv],
  rw e_ih_a,
  rw e_ih_a_1,
  simp [pair_left_subst, pair_left_fv],
  rw e_ih,
  simp [pair_right_subst, pair_right_fv],
  rw e_ih,
  simp [either_left_subst, either_left_fv],
  rw e_ih,
  simp [either_right_subst, either_right_fv],
  rw e_ih,
  simp [case_never_subst, case_never_fv],
  rw e_ih,
  simp [case_subst, case_fv],
  rw e_ih_a,
  rw subst_fv_var_helper fv_ex e_ih_a_1,
  rw subst_fv_var_helper fv_ex e_ih_a_2,
end
