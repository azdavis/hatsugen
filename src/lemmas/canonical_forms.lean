import defs.dynamics
import defs.statics

theorem bool_canonical_forms
  (Γ: cx typ) (e: exp) (value: val e)
  (et: has_typ Γ e typ.bool)
  : e = exp.true ∨ e = exp.false :=
begin
  cases et,
  left,
  refl,
  right,
  refl,
  cases value,
end
