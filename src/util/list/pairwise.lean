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

theorem pairwise_implies {t: Type} {r r': t -> t -> Prop} {xs: list t}:
  (∀ (x y: t), r x y -> r' x y) ->
  pairwise r xs ->
  pairwise r' xs :=
begin
  intros h p_r,
  induction xs,
  exact pairwise.nil r',
  cases p_r,
  let a := fun y y_in, h xs_hd y (p_r_a y y_in),
  let b := xs_ih p_r_a_1,
  exact pairwise.cons a b,
end
