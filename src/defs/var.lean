import util.list.filter
import util.list.sort

-- variables. any type with infinite values and a well-behaved ≤ would work
@[reducible]
def var: Type := ℕ

@[derive decidable_eq]
structure cx_elem (t: Type): Type :=
  (x: var)
  (v: t)

def ne_var {t: Type} (a b: cx_elem t): Prop :=
  a.x ≠ b.x

structure cx (t: Type): Type :=
  (entries: set (cx_elem t))
  (nodupkeys:
    ∀ (e e' ∈ entries),
    e ≠ e' ->
    ne_var e e'
  )

def cx.empty {t: Type}: cx t :=
  cx.mk ∅ begin
    intros a b a_in,
    exfalso,
    exact a_in,
  end

def cx.lookup {t: Type} (Γ: cx t) (x: var) (v: t): Prop :=
  (cx_elem.mk x v ∈ Γ.entries)

def cx.insert {t: Type} (Γ: cx t) (x: var) (v: t): cx t :=
cx.mk ({cx_elem.mk x v} ∪ { e ∈ Γ.entries | cx_elem.x e ≠ x }) begin
  intros e e' e_in e'_in e_ne,
  cases e_in,
  cases e_in,
  cases e'_in,
  cases e'_in,
  rw symm e'_in at e_in,
  exfalso,
  exact e_ne e_in,
  exfalso,
  exact e'_in,
  cases e'_in,
  simp [ne_var],
  rw e_in,
  simp,
  let h := fun hm, e'_in_right (symm hm),
  exact h,
  exfalso,
  exact e_in,
  cases e_in,
  cases e'_in,
  cases e'_in,
  simp [ne_var],
  rw e'_in,
  simp,
  exact e_in_right,
  exfalso,
  exact e'_in,
  cases e'_in,
  exact Γ.nodupkeys e e' e_in_left e'_in_left e_ne,
end

instance {t: Type}: is_symm (cx_elem t) ne_var := is_symm.mk
begin
  intros a b ab,
  simp [ne_var] at *,
  exact ne.symm ab,
end
