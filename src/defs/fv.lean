import defs.syntax
import defs.var

@[reducible]
def fv (e: exp): set var :=
  exp.rec_on e
  -- int
  (fun _, ∅)
  -- true
  ∅
  -- false
  ∅
  -- if_
  (fun _ _ _ s1 s2 s3, s1 ∪ s2 ∪ s3)