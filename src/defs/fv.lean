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
  -- pair
  (fun _ _ s1 s2, s1 ++ s2)
  -- pair_left
  (fun _, id)
  -- pair_right
  (fun _, id)
  -- either_left
  (fun _ _, id)
  -- either_right
  (fun _ _, id)
  -- case_never
  (fun _ _, id)
  -- case
  (fun _ x1 _ x2 _ sh s1 s2,
    sh ++ (list.filter (ne x1) s1) ++ (list.filter (ne x2) s2))
