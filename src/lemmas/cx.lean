import defs.var
import util.option

theorem lookup_uniq {t: Type} {Γ: cx t} {x: var} {v v': t}:
  cx.lookup Γ x v ->
  cx.lookup Γ x v' ->
  v = v' :=
begin
  sorry,
end

theorem lookup_mem_entries {t: Type} {Γ: cx t} {x: var} {v: t}:
  cx_elem.mk x v ∈ Γ.entries ↔
  cx.lookup Γ x v :=
begin
  sorry,
end

theorem lookup_mem_entries_ne {t: Type}
  {Γ: cx t} {x y: var} {vx vy: t}:
  x ≠ y ->
  (cx_elem.mk x vx ∈ Γ.entries ↔
  cx_elem.mk x vx ∈ (cx.insert Γ y vy).entries) :=
begin
  sorry,
end

theorem lookup_insert {t: Type} (Γ: cx t) (x: var) (v: t):
  cx.lookup (cx.insert Γ x v) x v :=
begin
  sorry,
end

theorem useless_insert_ne {t: Type} (Γ: cx t) (x y: var) (v: t):
  x ≠ y ->
  cx.lookup (cx.insert Γ y v) x =
  cx.lookup Γ x :=
begin
  sorry,
end

theorem ne_var_ne {t: Type} (a b: cx_elem t): ne_var a b -> a ≠ b :=
begin
  intro h,
  simp [ne_var] at h,
  intro bad,
  rw bad at h,
  exact h rfl,
end

theorem entries_same_eq {t: Type} {Γ Γ': cx t}:
  Γ.entries = Γ'.entries -> Γ = Γ' :=
begin
  cases Γ,
  cases Γ',
  simp,
  intro h,
  exact h,
end

theorem lookup_same_mem_entries_one {t: Type} {Γ Γ': cx t}:
  (∀ (x: var), cx.lookup Γ x = cx.lookup Γ' x) ->
  (∀ (e: cx_elem t), e ∈ Γ.entries -> e ∈ Γ'.entries) :=
begin
  sorry,
end

theorem lookup_same_mem_entries {t: Type} {Γ Γ': cx t}:
  (∀ (x: var), cx.lookup Γ x = cx.lookup Γ' x) ->
  (∀ (e: cx_elem t), e ∈ Γ.entries ↔ e ∈ Γ'.entries) :=
begin
  intros h e,
  split,
  exact lookup_same_mem_entries_one h e,
  let h' := fun x, symm (h x),
  exact lookup_same_mem_entries_one h' e,
end

theorem lookup_same_eq_entries {t: Type} {Γ Γ': cx t}:
  (∀ (x: var), cx.lookup Γ x = cx.lookup Γ' x) -> Γ.entries = Γ'.entries :=
begin
  sorry,
end

theorem lookup_same {t: Type} {Γ Γ': cx t}:
  (∀ (x: var), cx.lookup Γ x = cx.lookup Γ' x) -> Γ = Γ' :=
begin
  intro h,
  exact entries_same_eq (lookup_same_eq_entries h),
end

theorem useless_insert_twice {t: Type}
  (Γ: cx t) (x: var) (v v': t):
  cx.insert (cx.insert Γ x v') x v = cx.insert Γ x v :=
lookup_same begin
  sorry,
end

theorem insert_comm {t: Type}
  (Γ: cx t) (x y: var) (vx vy: t) (h: x ≠ y):
  cx.insert (cx.insert Γ y vy) x vx =
  cx.insert (cx.insert Γ x vx) y vy :=
lookup_same begin
  sorry,
end
