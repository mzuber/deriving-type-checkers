let double = \f.\x. (f (f x))
in let succ = \x. x + 1
   in let foo = \x. true
      in (double succ, double foo)