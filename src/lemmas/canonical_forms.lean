import defs.dynamics
import defs.statics

theorem bool_canonical_forms
  {Γ: env} {e: exp} (value: val e)
  (et: has_typ Γ e typ.bool)
  : e = exp.true ∨ e = exp.false :=
begin
  cases et,
  left,
  refl,
  right,
  refl,
  repeat {cases value},
end

theorem arrow_canonical_forms
  {Γ: env} {e: exp} {τ1 τ2: typ} (value: val e)
  (et: has_typ Γ e (typ.arrow τ1 τ2))
  : ∃ (x: var) (e': exp), e = exp.fn x τ1 e' :=
begin
  cases et,
  cases value,
  cases value,
  existsi [et_x, et_e],
  refl,
  repeat {cases value},
end

theorem pair_canonical_forms
  {Γ: env} {e: exp} {τ1 τ2: typ} (value: val e)
  (et: has_typ Γ e (typ.pair τ1 τ2))
  : ∃ (e1 e2: exp), e = exp.pair e1 e2 :=
begin
  cases et,
  repeat {cases value},
  existsi [et_e1, et_e2],
  refl,
  repeat {cases value},
end

theorem never_canonical_forms
  {Γ: env} {e: exp} (value: val e)
  (et: has_typ Γ e typ.never)
  : false :=
begin
  cases et,
  repeat {cases value},
end

theorem either_canonical_forms
  {Γ: env} {e: exp} {τ1 τ2: typ} (value: val e)
  (et: has_typ Γ e (typ.either τ1 τ2))
  : ∃ (e': exp), (e = exp.either_left τ2 e') ∨ (e = exp.either_right τ1 e') :=
begin
  cases et,
  repeat {cases value},
  existsi et_e,
  left,
  refl,
  existsi et_e,
  right,
  refl,
end
