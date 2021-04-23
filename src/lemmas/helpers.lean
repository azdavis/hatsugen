import defs.statics
import defs.dynamics
import defs.fv
import util.sets

theorem if_fv_subset (e1 e2 e3: exp):
  fv e1 ⊆ fv (exp.if_ e1 e2 e3) ∧
  fv e2 ⊆ fv (exp.if_ e1 e2 e3) ∧
  fv e3 ⊆ fv (exp.if_ e1 e2 e3) :=
begin
  simp [fv],
  split,
  intros _ a,
  left,
  left,
  exact a,
  split,
  intros _ b,
  left,
  right,
  exact b,
  intros _ c,
  right,
  exact c,
end

theorem if_fv_empty
  (e1 e2 e3: exp)
  : fv (exp.if_ e1 e2 e3) = ∅ ↔ (fv e1 = ∅ ∧ fv e2 = ∅ ∧ fv e3 = ∅) :=
begin
  let fv_e := fv (exp.if_ e1 e2 e3),
  split,
  intro h,
  let sub := if_fv_subset e1 e2 e3,
  let hm := eq_subset h,
  let f := fun (a: exp) (b: fv a ⊆ fv_e),
    iff.elim_left (subset_empty_iff (fv a)) (subset_trans b hm),
  split,
  exact f e1 sub.left,
  split,
  exact f e2 sub.right.left,
  exact f e3 sub.right.right,
  intro h,
  let f := fun (a: exp) (b: fv a = ∅),
    iff.elim_right (subset_empty_iff (fv a)) b,
  let e1e2 := subset_union_subset (f e1 h.left) (f e2 h.right.left),
  let all := subset_union_subset e1e2 (f e3 h.right.right),
  exact iff.elim_left (subset_empty_iff fv_e) all,
end

theorem app_fv_subset (e1 e2: exp):
  fv e1 ⊆ fv (exp.app e1 e2) ∧
  fv e2 ⊆ fv (exp.app e1 e2) :=
begin
  simp [fv],
  split,
  intros _ a,
  left,
  exact a,
  intros _ b,
  right,
  exact b,
end

theorem app_fv_empty
  (e1 e2: exp)
  : fv (exp.app e1 e2) = ∅ ↔ (fv e1 = ∅ ∧ fv e2 = ∅) :=
begin
  let fv_e := fv (exp.app e1 e2),
  split,
  intro h,
  let sub := app_fv_subset e1 e2,
  let hm := eq_subset h,
  let f := fun (a: exp) (b: fv a ⊆ fv_e),
    iff.elim_left (subset_empty_iff (fv a)) (subset_trans b hm),
  split,
  exact f e1 sub.left,
  exact f e2 sub.right,
  intro h,
  let f := fun (a: exp) (b: fv a = ∅),
    iff.elim_right (subset_empty_iff (fv a)) b,
  let all := subset_union_subset (f e1 h.left) (f e2 h.right),
  exact iff.elim_left (subset_empty_iff fv_e) all,
end

theorem lookup_same
  {Γ: cx typ} {x: var} {τ τ': typ}
  (h1: lookup Γ x τ)
  (h2: lookup Γ x τ')
  : τ = τ' :=
begin
  induction h1,
  cases h2,
  refl,
  contradiction,
  cases h2,
  contradiction,
  exact h1_ih h2_a_1,
end

theorem fresh (xs: list var): ∃ (x: var), ∀ (y ∈ xs), y < x :=
begin
  induction xs,
  existsi 0,
  intros y h,
  let notin := list.not_mem_nil y,
  contradiction,
  cases xs_ih,
  cases lt_trichotomy xs_hd xs_ih_w,
  existsi xs_ih_w,
  intros y h,
  cases h,
  rw h_1,
  exact h,
  exact xs_ih_h y h_1,
  existsi nat.succ xs_hd,
  intros y h,
  cases h,
  rw h_1,
  exact nat.lt_succ_of_le (nat.less_than_or_equal.refl xs_hd),
  let y_lt_w := xs_ih_h y h_1,
  cases h,
  rw h,
  exact nat.lt_succ_of_le (le_not_le_of_lt y_lt_w).left,
  exact nat.lt_succ_of_le (le_of_lt (lt_trans y_lt_w h)),
end

theorem lookup_or_not {t: Type} (Δ: cx t) (x: var):
  (∃ (a: t), lookup Δ x a) ∨ x ∉ vars Δ :=
begin
  induction Δ,
  right,
  simp [vars],
  exact mem_empty_eq x,
  cases Δ_hd,
  cases classical.em (x = Δ_hd_fst),
  left,
  existsi Δ_hd_snd,
  rw h,
  exact lookup.hd Δ_tl Δ_hd_fst Δ_hd_snd,
  cases Δ_ih,
  cases Δ_ih,
  left,
  existsi Δ_ih_w,
  exact lookup.tl Δ_tl x Δ_ih_w Δ_hd_fst Δ_hd_snd h Δ_ih_h,
  right,
  simp [vars],
  intro h,
  cases h,
  contradiction,
  contradiction,
end
