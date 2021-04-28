import defs.statics
import defs.dynamics
import defs.fv

theorem append_nil_both
  {t: Type} (xs ys: list t): xs ++ ys = [] ↔ xs = [] ∧ ys = [] :=
begin
  split,
  intro h,
  induction xs,
  induction ys,
  split,
  refl,
  refl,
  split,
  refl,
  cases h,
  cases h,
  intro h,
  cases h,
  rw h_left,
  rw h_right,
  simp [list.append],
end

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

theorem lookup_or_not {t: Type} (Δ: cx t) (x: var):
  (∃ (a: t), lookup Δ x a) ∨ x ∉ vars Δ :=
begin
  induction Δ,
  right,
  simp [vars],
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
