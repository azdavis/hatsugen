import defs.statics
import defs.dynamics
import defs.fv
import util.list

theorem if_fv_empty
  (e1 e2 e3: exp)
  : fv (exp.if_ e1 e2 e3) = [] ↔ (fv e1 = [] ∧ fv e2 = [] ∧ fv e3 = []) :=
begin
  split,
  intro h,
  simp [fv] at h,
  let ap := iff.elim_left (append_nil_both (fv e1) (fv e2 ++ fv e3)) h,
  split,
  exact ap.left,
  exact iff.elim_left (append_nil_both (fv e2) (fv e3)) ap.right,
  intro h,
  cases h,
  cases h_right,
  simp [fv] at *,
  rw h_left,
  rw h_right_left,
  rw h_right_right,
  simp [list.append],
end

theorem app_fv_empty
  (e1 e2: exp)
  : fv (exp.app e1 e2) = [] ↔ (fv e1 = [] ∧ fv e2 = []) :=
begin
  split,
  intro h,
  simp [fv],
  exact iff.elim_left (append_nil_both (fv e1) (fv e2)) h,
  intro h,
  cases h,
  simp [fv] at *,
  rw h_left,
  rw h_right,
  simp [list.append],
end

theorem fresh' (xs: list var): ∃ (x: var), ∀ (y ∈ xs), y < x :=
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

theorem fresh (xs: list var): ∃ (x: var), x ∉ xs :=
begin
  cases fresh' xs,
  existsi w,
  intro h1,
  let b1 := h w h1,
  let b2 := lt_irrefl w,
  contradiction,
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
  cases classical.em (x = et_x),
  rw h,
  simp [subst],
  sorry,
  sorry,
  sorry,
  sorry,
end
