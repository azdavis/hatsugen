inductive pairwise {t: Type} (r: t -> t -> Prop): list t → Prop
| nil: pairwise []
| cons {x: t} {xs: list t}: (∀ y ∈ xs, r x y) -> pairwise xs -> pairwise (x :: xs)

theorem pairwise_inversion {t: Type} {r: t -> t -> Prop} {x: t} {xs: list t}:
  pairwise r (x :: xs) -> pairwise r xs :=
begin
  intro h,
  cases h,
  exact h_a_1,
end
