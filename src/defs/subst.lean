import defs.syntax
import defs.fv

def subst (ex: exp) (x: var) (e: exp) (_: fv ex = []): exp :=
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
  (fun y, if y = x then ex else exp.var y)
  -- fn
  (fun y τ e e', exp.fn y τ (if x = y then e else e'))
  -- app
  (fun _ _, exp.app)
