letrec fact = \x. if x==0 then 1 else x * (fact(x - 1))
in fact 4
