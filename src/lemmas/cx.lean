import defs.var
import util.option
import util.set

theorem lookup_uniq {t: Type} [decidable_eq t] {Γ: cx t} {x: var} {v v': t}:
  cx.lookup Γ x v ->
  cx.lookup Γ x v' ->
  v = v' :=
begin
  simp [cx.lookup],
  intros la lb,
  by_cases v = v',
  exact h,
  let a := cx_elem.mk x v,
  let b := cx_elem.mk x v',
  let a_ne_b: cx_elem.mk x v ≠ cx_elem.mk x v' := begin
    intro h1,
    simp at h1,
    exact h h1,
  end,
  let hm := Γ.nodupkeys a b la lb a_ne_b,
  simp [ne_var] at hm,
  exfalso,
  exact hm,
end

theorem lookup_insert {t: Type} (Γ: cx t) (x: var) (v: t):
  cx.lookup (cx.insert Γ x v) x v :=
begin
  simp [cx.insert],
  simp [cx.lookup],
  left,
  exact iff.elim_right mem_singleton_iff rfl,
end

theorem useless_insert_ne {t: Type} {Γ: cx t} {x y: var} {vy v: t}:
  x ≠ y ->
  (cx.lookup (cx.insert Γ y vy) x v ↔ cx.lookup Γ x v) :=
begin
  intro h_ne,
  simp [cx.insert],
  simp [cx.lookup],
  split,
  intro h,
  cases h,
  cases iff.elim_left mem_singleton_iff h,
  exfalso,
  exact h_ne rfl,
  exact mem_pred h,
  intro h,
  right,
  split,
  exact h,
  simp,
  exact h_ne,
end

theorem entries_same {t: Type} {Γ Γ': cx t}:
  Γ.entries = Γ'.entries -> Γ = Γ' :=
begin
  cases Γ,
  cases Γ',
  simp,
  intro h,
  exact h,
end

theorem useless_insert_twice {t: Type}
  (Γ: cx t) (x: var) (v v': t):
  cx.insert (cx.insert Γ x v') x v = cx.insert Γ x v :=
begin
  simp [cx.insert],
  rw pred_distr_union,
  let hm: (cx_elem.mk x v').x = x := by simp,
  let hm': ¬ ¬ (cx_elem.mk x v').x = x := fun f, f hm,
  rw @singleton_not_pred (cx_elem t) (cx_elem.mk x v') (fun e, e.x ≠ x) hm',
  rw union_emp,
  rw double_pred,
end

theorem insert_comm' {t: Type}
  {Γ: cx t} {x y: var} {vx vy: t} {a: cx_elem t}:
  x ≠ y ->
  a ∈ (cx.insert (cx.insert Γ y vy) x vx).entries ->
  a ∈ (cx.insert (cx.insert Γ x vx) y vy).entries :=
begin
  intro h_ne,
  simp [cx.insert],
  intro h,
  cases h,
  right,
  split,
  left,
  exact h,
  rw iff.elim_left mem_singleton_iff h,
  simp,
  exact h_ne,
  cases h,
  cases h_left,
  left,
  exact h_left,
  right,
  split,
  right,
  split,
  exact mem_pred h_left,
  simp,
  exact h_right,
  simp,
  cases h_left,
  exact h_left_right,
end

theorem insert_comm {t: Type}
  (Γ: cx t) (x y: var) (vx vy: t) (h: x ≠ y):
  cx.insert (cx.insert Γ y vy) x vx =
  cx.insert (cx.insert Γ x vx) y vy :=
entries_same (set_ext begin
  intro a,
  split,
  exact insert_comm' h,
  let h' := fun x, h (symm x),
  exact insert_comm' h',
end)
