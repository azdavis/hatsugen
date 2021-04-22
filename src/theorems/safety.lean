import util.sets
import lemmas.helpers
import lemmas.canonical_forms
import lemmas.inversion

theorem progress
  {Γ: cx typ}
  {e: exp}
  {τ: typ}
  (no_fv: fv e = ∅)
  (et: has_typ Γ e τ)
  : val e ∨ (∃ (e': exp), steps e e') :=
begin
  induction et,
  left,
  exact val.int et_n,
  left,
  exact val.true,
  left,
  exact val.false,
  right,
  let s_if := if_fv_subset et_e1 et_e2 et_e3,
  let fv_e := fv (exp.if_ et_e1 et_e2 et_e3),
  let sub_e := iff.elim_right (subset_empty_iff fv_e) no_fv,
  let sub_e1 := subset_trans s_if.left sub_e,
  let emp_e1 := iff.elim_left (subset_empty_iff (fv et_e1)) sub_e1,
  cases et_ih_a emp_e1,
  cases bool_canonical_forms h et_a,
  rw h_1,
  existsi et_e2,
  exact steps.if_true et_e2 et_e3,
  rw h_1,
  existsi et_e3,
  exact steps.if_false et_e2 et_e3,
  cases h,
  existsi exp.if_ h_w et_e2 et_e3,
  exact steps.if_e1 et_e1 h_w et_e2 et_e3 h_h,
end

theorem preservation
  {Γ: cx typ}
  {e e': exp}
  {τ: typ}
  (no_fv: fv e = ∅)
  (et: has_typ Γ e τ)
  (st: steps e e')
  : has_typ Γ e' τ ∧ fv e' = ∅ :=
begin
  induction st generalizing Γ τ,
  let inv := inversion_if et,
  let emp := iff.elim_left (if_fv_empty st_e1 st_e2 st_e3) no_fv,
  let e1'_ih := st_ih emp.left inv.left,
  split,
  exact has_typ.if_ Γ st_e1' st_e2 st_e3 τ e1'_ih.left inv.right.left inv.right.right,
  exact iff.elim_right (if_fv_empty st_e1' st_e2 st_e3) (and.intro e1'_ih.right emp.right),
  let inv := inversion_if et,
  let emp := iff.elim_left (if_fv_empty exp.true st_e2 st_e3) no_fv,
  exact and.intro inv.right.left emp.right.left,
  let inv := inversion_if et,
  let emp := iff.elim_left (if_fv_empty exp.false st_e2 st_e3) no_fv,
  exact and.intro inv.right.right emp.right.right,
end
