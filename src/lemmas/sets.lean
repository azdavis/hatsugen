theorem subset_trans
  {t: Type}
  (a b c: set t)
  (ab: a ⊆ b) (bc: b ⊆ c): a ⊆ c
:=
begin
  intros _ h,
  exact bc (ab h)
end

theorem subset_union_subset
  {t: Type}
  (a b c: set t)
  (ac: a ⊆ c) (bc: b ⊆ c): (a ∪ b) ⊆ c
:=
begin
  intros _ h,
  cases h,
  exact ac h,
  exact bc h,
end
