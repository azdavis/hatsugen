import defs.syntax
import defs.var

-- free variables
def fv (e: exp): list var :=
  exp.rec_on e
  -- int
  (fun _, [])
  -- true
  []
  -- false
  []
  -- if_
  (fun _ _ _ s1 s2 s3, s1 ++ (s2 ++ s3))
  -- var
  (fun x, [x])
  -- fn
  (fun x _ _, list.filter (ne x))
  -- app
  (fun _ _ s1 s2, s1 ++ s2)
  -- unit
  []
  -- prod
  (fun _ _ s1 s2, s1 ++ s2)
  -- prod_left
  (fun _ s, s)
  -- prod_right
  (fun _ s, s)
