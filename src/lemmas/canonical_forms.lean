import defs.dynamics
import defs.statics

theorem bool_canonical_forms
  {Γ: cx typ} {e: exp} (value: val e)
  (et: has_typ Γ e typ.bool)
  : e = exp.true ∨ e = exp.false :=
begin
  cases et,
  left,
  refl,
  right,
  refl,
  cases value,
  cases value,
  cases value,
end

theorem arrow_canonical_forms
  {Γ: cx typ} {e: exp} {τ1 τ2: typ} (value: val e)
  (et: has_typ Γ e (typ.arrow τ1 τ2))
  : ∃ (x: var) (e': exp), e = exp.fn x τ1 e' :=
begin
  cases et,
  cases value,
  cases value,
  existsi [et_x, et_e],
  refl,
  cases value,
end
