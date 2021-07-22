import defs.syntax
import defs.fv

-- substitution
def subst (ex: exp) (x: var) (_: fv ex = []) (e: exp): exp :=
  exp.rec_on e
  -- int
  exp.int
  -- true
  exp.true
  -- false
  exp.false
  -- if_
  (fun _ _ _, exp.if_)
  -- var
  (fun y, if x = y then ex else exp.var y)
  -- fn
  (fun y τ e e', exp.fn y τ (if x = y then e else e'))
  -- app
  (fun _ _, exp.app)
  -- unit
  exp.unit
  -- pair
  (fun _ _, exp.pair)
  -- pair_left
  (fun _, exp.pair_left)
  -- pair_right
  (fun _, exp.pair_right)
  -- either_left
  (fun τ _, exp.either_left τ)
  -- either_right
  (fun τ _, exp.either_right τ)
  -- case_never
  (fun τ _, exp.case_never τ)
  -- case
  (fun eh x1 e1 x2 e2 eh' e1' e2',
    exp.case eh'
      x1 (if x = x1 then e1 else e1')
      x2 (if x = x2 then e2 else e2')
  )
