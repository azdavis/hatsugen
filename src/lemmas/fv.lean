import defs.syntax
import defs.fv
import util.list.append

theorem var_fv (x: var):
  fv (exp.var x) = [x]
  := by simp [fv]

theorem if_fv (e1 e2 e3: exp):
  fv (exp.if_ e1 e2 e3) = fv e1 ++ (fv e2 ++ fv e3)
  := by simp [fv]

theorem app_fv (e1 e2: exp):
  fv (exp.app e1 e2) = fv e1 ++ fv e2
  := by simp [fv]

theorem fn_fv (x: var) (τ: typ) (e: exp):
  fv (exp.fn x τ e) = list.filter (ne x) (fv e)
  := by simp [fv]

theorem prod_fv (e1 e2: exp):
  fv (exp.prod e1 e2) = fv e1 ++ fv e2
  := by simp [fv]

theorem prod_left_fv (e: exp):
  fv (exp.prod_left e) = fv e
  := by simp [fv]

theorem prod_right_fv (e: exp):
  fv (exp.prod_right e) = fv e
  := by simp [fv]

theorem if_fv_empty
  (e1 e2 e3: exp)
  : fv (exp.if_ e1 e2 e3) = [] ↔ (fv e1 = [] ∧ fv e2 = [] ∧ fv e3 = []) :=
begin
  split,
  intro h,
  rw if_fv e1 e2 e3 at h,
  let ap := iff.elim_left append_nil_both h,
  split,
  exact ap.left,
  exact iff.elim_left append_nil_both ap.right,
  intro h,
  cases h,
  cases h_right,
  rw if_fv e1 e2 e3 at *,
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
  rw app_fv e1 e2 at h,
  exact iff.elim_left append_nil_both h,
  intro h,
  cases h,
  rw app_fv e1 e2 at *,
  rw h_left,
  rw h_right,
  simp [list.append],
end

theorem prod_fv_empty
  (e1 e2: exp)
  : fv (exp.prod e1 e2) = [] ↔ (fv e1 = [] ∧ fv e2 = []) :=
begin
  split,
  intro h,
  rw prod_fv e1 e2 at h,
  exact iff.elim_left append_nil_both h,
  intro h,
  cases h,
  rw prod_fv e1 e2 at *,
  rw h_left,
  rw h_right,
  simp [list.append],
end
