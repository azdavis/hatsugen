import defs.statics
import defs.dynamics
import defs.fv
import util.sets

theorem subset_if (e1 e2 e3: exp):
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

theorem lookup_same
  (Γ: cx typ) (x: var) (τ: typ) (τ': typ)
  (l1: lookup Γ x τ)
  (l2: lookup Γ x τ')
  : τ = τ' :=
begin
  induction l1,
  cases l2,
  refl,
  contradiction,
  cases l2,
  contradiction,
  exact l1_ih l2_a_1,
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
