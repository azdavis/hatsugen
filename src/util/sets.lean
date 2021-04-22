theorem set_ext {t: Type} {a b: set t} (h: ∀ x, x ∈ a ↔ x ∈ b): a = b :=
  funext (fun x, propext (h x))

theorem set_antisymm {t: Type} {a b: set t} (h1: a ⊆ b) (h2: b ⊆ a): a = b :=
  set_ext (fun x, iff.intro (fun y, h1 y) (fun z, h2 z))

theorem subset_trans
  {t: Type}
  {a b c: set t}
  (ab: a ⊆ b) (bc: b ⊆ c)
  : a ⊆ c
:=
begin
  intros _ h,
  exact bc (ab h)
end

theorem subset_union_subset
  {t: Type}
  {a b c: set t}
  (ac: a ⊆ c) (bc: b ⊆ c)
  : (a ∪ b) ⊆ c
:=
begin
  intros _ h,
  cases h,
  exact ac h,
  exact bc h,
end

theorem eq_subset {t: Type} {a b: set t} (pf: a = b): a ⊆ b :=
begin
  rw pf,
  intros _ b,
  exact b,
end

theorem mem_empty_eq {t: Type} (x: t): x ∉ (∅ : set t) := id

theorem empty_subset {t: Type} (a: set t): ∅ ⊆ a :=
begin
  intros x,
  let bad := mem_empty_eq x,
  contradiction,
end

theorem subset_empty_iff {t: Type} (s: set t): s ⊆ ∅ ↔ s = ∅ :=
begin
  split,
  intro h,
  let x := empty_subset s,
  exact set_antisymm h x,
  intro h,
  rw h,
  exact empty_subset ∅,
end
