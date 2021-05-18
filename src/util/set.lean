theorem mem_singleton_iff {t: Type} {a b: t}:
  a ∈ ({b} : set t) ↔ a = b :=
begin
  split,
  intro h,
  cases h,
  exact h,
  exfalso,
  exact h,
  intro h,
  rw h,
  simp [singleton],
  simp [has_insert.insert],
  simp [set.insert],
  simp [has_emptyc.emptyc],
  simp [has_mem.mem],
  simp [set.mem],
  simp [set_of],
end

theorem mem_pred {t: Type} {s: set t} {p: t -> Prop} {x: t}:
  x ∈ { y ∈ s | p y} ->
  x ∈ s :=
begin
  intro h,
  cases h,
  exact h_left,
end

theorem set_ext {t: Type} {a b: set t}: (∀ x, x ∈ a ↔ x ∈ b) -> a = b :=
begin
  intro h,
  exact funext (fun x, propext (h x)),
end

theorem pred_distr_union {t: Type} {a b: set t} {p: t -> Prop}:
  { x ∈ (a ∪ b) | p x } = { x ∈ a | p x } ∪ { x ∈ b | p x } :=
set_ext begin
  intro x,
  split,
  intro h,
  cases h,
  cases h_left,
  left,
  split,
  exact h_left,
  simp,
  exact h_right,
  right,
  split,
  exact h_left,
  simp,
  exact h_right,
  intro h,
  cases h,
  cases h,
  split,
  left,
  exact h_left,
  simp,
  exact h_right,
  cases h,
  split,
  right,
  exact h_left,
  simp,
  exact h_right,
end

theorem singleton_not_pred {t: Type} {x: t} {p: t -> Prop} (npx: ¬ (p x)):
  { y ∈ {x} | p y } = (∅: set t) :=
set_ext begin
  intro y,
  split,
  intro h,
  cases h,
  let hm := iff.elim_left mem_singleton_iff h_left,
  rw hm at h_right,
  exfalso,
  exact npx h_right,
  intro h,
  exfalso,
  exact h,
end

theorem union_emp {t: Type} {a: set t}: ∅ ∪ a = a :=
set_ext begin
  intro x,
  split,
  intro h,
  cases h,
  exfalso,
  exact h,
  exact h,
  intro h,
  right,
  exact h,
end

theorem double_pred {t: Type} {s: set t} {p: t -> Prop}:
  { x ∈ { y ∈ s | p y } | p x } = { x ∈ s | p x } :=
set_ext begin
  intro x,
  split,
  intro h,
  cases h,
  cases h_left,
  split,
  exact h_left_left,
  simp,
  exact h_right,
  intro h,
  cases h,
  split,
  split,
  exact h_left,
  simp,
  exact h_right,
  simp,
  exact h_right,
end
