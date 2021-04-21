import util.sets
import lemmas.helpers
import lemmas.canonical_forms
import lemmas.inversion

theorem progress
  (Γ: cx typ)
  (e: exp)
  (Γ_ok: fv e ⊆ vars Γ)
  (τ: typ)
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
  let s_if := subset_if et_e1 et_e2 et_e3,
  let fv_e := fv (exp.if_ et_e1 et_e2 et_e3),
  let sub_e1 := subset_trans (fv et_e1) fv_e (vars et_Γ) s_if.left Γ_ok,
  cases et_ih_a sub_e1,
  cases bool_canonical_forms et_Γ et_e1 h et_a,
  rewrite h_1,
  existsi et_e2,
  exact steps.if_true et_e2 et_e3,
  rewrite h_1,
  existsi et_e3,
  exact steps.if_false et_e2 et_e3,
  cases h,
  existsi exp.if_ h_w et_e2 et_e3,
  exact steps.if_e1 et_e1 h_w et_e2 et_e3 h_h,
end

theorem preservation
  (Γ: cx typ)
  (e: exp)
  (Γ_ok: fv e ⊆ vars Γ)
  (e': exp) (τ: typ)
  (et: has_typ Γ e τ)
  (st: steps e e')
  : has_typ Γ e' τ ∧ fv e' ⊆ vars Γ :=
begin
  induction st generalizing Γ τ,
  let inv := inversion_if Γ st_e1 st_e2 st_e3 τ et,
  let sub := subset_if st_e1 st_e2 st_e3,
  let fv_e := fv (exp.if_ st_e1 st_e2 st_e3),
  let sub_e1 := subset_trans (fv st_e1) fv_e (vars Γ) sub.left Γ_ok,
  let sub_e2 := subset_trans (fv st_e2) fv_e (vars Γ) sub.right.left Γ_ok,
  let sub_e3 := subset_trans (fv st_e3) fv_e (vars Γ) sub.right.right Γ_ok,
  let e1_ih := st_ih Γ typ.bool sub_e1 inv.left,
  split,
  exact has_typ.if_ Γ st_e1' st_e2 st_e3 τ e1_ih.left inv.right.left inv.right.right,
  let sub_e1_e2 := subset_union_subset (fv st_e1') (fv st_e2) (vars Γ) e1_ih.right sub_e2,
  exact subset_union_subset (fv st_e1' ∪ fv st_e2) (fv st_e3) (vars Γ) sub_e1_e2 sub_e3,
  let inv := inversion_if Γ exp.true st_e2 st_e3 τ et,
  split,
  exact inv.right.left,
  let sub := subset_if exp.true st_e2 st_e3,
  exact subset_trans (fv st_e2) (fv (exp.if_ exp.true st_e2 st_e3)) (vars Γ) sub.right.left Γ_ok,
  let inv := inversion_if Γ exp.false st_e2 st_e3 τ et,
  split,
  exact inv.right.right,
  let sub := subset_if exp.false st_e2 st_e3,
  exact subset_trans (fv st_e3) (fv (exp.if_ exp.true st_e2 st_e3)) (vars Γ) sub.right.right Γ_ok,
end
