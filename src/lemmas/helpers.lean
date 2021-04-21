import defs.statics
import defs.dynamics
import defs.fv

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
