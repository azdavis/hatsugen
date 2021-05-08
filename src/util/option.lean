theorem option_em {t: Type} (x: option t): x = none ∨ ∃ (v: t), x = some v :=
begin
  cases x,
  left,
  refl,
  right,
  existsi x,
  refl,
end

theorem option_not_both {t: Type} (x: option t): ¬ (x = none ∧ ∃ (v: t), x = some v) :=
begin
  intro h,
  cases h,
  cases h_right,
  rw h_left at h_right_h,
  contradiction,
end

theorem not_some_is_none {t: Type} {x: option t}: (∀ (v: t), x ≠ some v) -> x = none :=
begin
  intro h,
  cases option_em x,
  exact h_1,
  cases h_1,
  exfalso,
  exact h h_1_w h_1_h,
end
