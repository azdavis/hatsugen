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
  -- prod
  (fun _ _, exp.prod)
  -- prod_left
  (fun _, exp.prod_left)
  -- prod_right
  (fun _, exp.prod_right)
