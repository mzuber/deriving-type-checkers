let succ = \x. x+1
in let twice = \f.\x. (f (f x))
   in ((twice succ) 0)
