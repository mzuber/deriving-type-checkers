let double = \f.\x. (f (f x))
in ((double (\x. (and x) true)) true, (double (\x. x+1)) 0)
