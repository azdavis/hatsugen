import defs.syntax
import defs.fv

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
