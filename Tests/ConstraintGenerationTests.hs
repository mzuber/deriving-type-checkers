----------------------------------------------------------------------
-- |
-- Module      :  Tests.ConstraintGenerationTests
-- Copyright   :  (c) 2010-2011, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
--
-- Constraint generation tests for the type checker library.
----------------------------------------------------------------------
module Tests.ConstraintGenerationTests ( runMiniMLInstTests
                                       , runFJInstTests
                                       ) where

import TypeCheckLib.ConstraintGeneration
import TypeCheckLib.AbstractSyntax
import TypeCheckLib.AbstractSyntax.Term
import TypeCheckLib.Type
import TypeCheckLib.Rule

import Examples.TypeSystems.MiniML
import Examples.TypeSystems.FJ
import qualified Examples.Parser.FJ as FJ
import qualified Examples.Parser.MiniML as ML

import qualified Data.Sequence
import Prelude hiding (abs, div, and, or, const)

import Test.HUnit


-- ###################################################################
--       Tests for rule instantiation and constraint generation                      
-- ###################################################################


instRules [] = []
instRules (j:js) = case j of
                     Sep r -> r : (instRules js)
                     _     -> instRules js


dbg = True


------------------------------- MiniML -------------------------------

rules = [ true, false, const, add, sub, mul, div, eqi, -- base types
          abs, fix, app, cond, pair, letpoly, letrec, varpoly ]

testMiniML file = do ast <- ML.parseFromFile file
                     let j  = J empty ast (mkTV "T" :: Ty)
                         cs = evalTypeCheckM (genCs rules j dbg)
                     putStr (show cs)

-- (λ x.x) 5
test1 = putStrLn $ show (evalTypeCheckM $ genCs rules j dbg)
    where
      t = K App 2 [K Abs 2 [Var (Ide "x"), Var (Ide "x")], Const 5] 
      j = J empty t (mkTV "T" :: Ty)

-- (λ x. if x == 0 then 0 else 1) 5
test2  = putStrLn $ show (evalTypeCheckM $ genCs rules j dbg)
    where
      c = K IfThenElse 3 [K App 2 [K App 2 [Var (Ide "=="),
                                            Var (Ide "x")],
                                   Const 0],
                          Const 0,
                          Const 1]
      t = K App 2 [K Abs 2 [Var (Ide "x"), c], Const 5] 
      j = J empty t (mkTV "T" :: Ty)

-- let x = 5 in let y = 2 in (y,x)
test3 = putStrLn $ show (evalTypeCheckM $ genCs rules j dbg)
    where
      t = K Let 3 [Var (Ide "x"),
                   Const 5,
                   K Let 3 [Var (Ide "y"),
                            Const 2,
                            K Tuple 2 [Var (Ide "x"),
                                       Var (Ide "y")]]]
      j = J empty t (mkTV "T" :: Ty)

-- letrec fact = λ x. if x==0 then 1 else fact(x-1) in fact 4
testLetRec = putStr $ show (evalTypeCheckM $ genCs rules j dbg)
    where
      decr = K App 2 [K App 2 [Var (Ide "-"), Var (Ide "x")], Const 1]
      iF   = K IfThenElse 3 [ K App 2 [K App 2 [Var (Ide "=="),
                                                Var (Ide "x")],
                                       Const 0],
                              Const 1,
                              K App 2 [Var (Ide "fact"), decr] ]
      fact = K Abs 2 [Var (Ide "x"), iF] 
      rec  = K LetRec 3 [Var (Ide "fact"),
                         fact,
                         K App 2 [Var (Ide "fact"), Const 4]]
      j    = J empty rec (mkTV "T" :: Ty)

-- {double : a -> a,
--  foo : int -> int,
--  bar : bool -> bool} ⊢ (double foo, double bar) : T
testPoly1 = putStr $ show (evalTypeCheckM $ genCs rules j dbg)
    where
      ctx = fromList [ (Var (Ide "double"), TS [mkTV "a"] (mkTV "a" ->: mkTV "a")),
                       (Var (Ide "foo"), mkT "int" ->: mkT "int"),
                       (Var (Ide "bar"), mkT "bool" ->: mkT "bool") ]
      j   = J ctx (K Tuple 2 [K App 2 [Var (Ide "double"), Var (Ide "foo")],
                              K App 2 [Var (Ide "double"), Var (Ide "bar")]]) (mkTV "T" :: Ty)

-- {double : a -> a} ⊢ double + : T
testPoly2 = putStr $ show (evalTypeCheckM $ genCs rules j dbg)
    where
      ctx = singleton (Var (Ide "double")) (TS [mkTV "a"] (mkTV "a" ->: mkTV "a"))
      j   = J ctx (K App 2 [Var (Ide "double"), Var (Ide "+")]) (mkTV "T" :: Ty)

-- let id = λ x. x in id
testPoly3 = putStr $ show (evalTypeCheckM $ genCs rules j dbg)
    where
      j = J empty (K Let 3 [Var (Ide "id"),
                            K Abs 2 [Var (Ide "x"),
                                     Var (Ide "x")],
                            Var (Ide "id")]
                  ) (mkTV "T" :: Ty)

-- 5 + true
testBase = putStr $ show (evalTypeCheckM $ genCs rules j dbg)
    where
      j = J empty (K App 2 [K App 2 [Var (Ide "+"), Const 5],
                            Var (Ide "true")]
                  ) (mkTV "T" :: Ty)

-- x
testVar = putStr $ show (evalTypeCheckM $ genCs rules j dbg)
    where
      j = J empty (Var (Ide "x")) (mkTV "T" :: Ty)
            


-- MiniML typing rules:
-- 0 - true       5 - mul          10 - app             15 - varpoly
-- 1 - false      6 - div          11 - cond
-- 2 - int        7 - eqi          12 - pair
-- 3 - add        8 - abs          13 - letpoly
-- 4 - sub        9 - fix          14 - letrec


instML1 = mkTestCaseML "Tests/Programs/MiniML/pairs.ml"
                       "Rule instantiation for pairs.ml"
                       [13,2,13,2,12,15,15]

instML2 = mkTestCaseML "Tests/Programs/MiniML/abs.ml"
                       "Rule instantiation for abs.ml"
                       [10,8,15,2]

instML3 = mkTestCaseML "Tests/Programs/MiniML/fact.ml"
                       "Rule instantiation for fact.ml"
                       [14,13,9,8,8,11,10,10,7,15,2,2,10,
                        10,5,15,10,15,10,10,4,15,2,10,15,2]

instML4 = mkTestCaseML "Tests/Programs/MiniML/cond.ml"
                       "Rule instantiation for cond.ml"
                       [10,8,11,0,2,2,2]


instMLTests = TestList [ TestLabel "MiniML instantiation test 1" instML1,
                         TestLabel "MiniML instantiation test 2" instML2,
                         TestLabel "MiniML instantiation test 3" instML3,
                         TestLabel "MiniML instantiation test 4" instML4 ]

runMiniMLInstTests = runTestTT instMLTests




------------------------- FeatherweightJava --------------------------

-- | FeatherweightJava typing rules.
fj :: [FJ.FJClass] -> [Rule]
fj prg = [ field prg, new prg, invoke prg, cast prg,
           method prg, constructor prg, fjclass prg, var ]


-- | Interactive test function for FJ programs.
testFJ fileName = do ast <- FJ.parseFromFile fileName
                     let cs = map (genC ast) ast
                     putStrLn $ unlines (map pprint (concat cs))
    where
      genC ast c = evalTypeCheckM $
                   genCs (fj ast) (J empty c (mkTV "T" :: Ty)) dbg

-- | Interactive test function for FJ Expressions.
testFJExpr fileName e = do ast <- FJ.parseFromFile fileName
                           let j  = J empty e (mkTV "T" :: Ty)
                               cs = evalTypeCheckM $ genCs (fj ast) j dbg
                           putStrLn $ unlines (map pprint cs)


-- | Constructor call:
--   new Pair (new Object, new Object)
test5 = testFJExpr "Tests/Programs/FJ/Pair.java" e
    where
      e = FJ.New (mkT "Pair") (seqFromList [o,o])
      o = FJ.New (mkT "Object") emptySeq

-- | Method invocation with arguments:
--   new Pair (new Object, new Object).setfst(new Object)
test6 = testFJExpr "Tests/Programs/FJ/Pair.java" e
    where
      e = FJ.Invoke p s
      p = FJ.New (mkT "Pair") (seqFromList [o,o])
      s = FJ.Meth (Ide "setfst") (seqFromList [o])
      o = FJ.New (mkT "Object") emptySeq
      
-- | Field access:
--   new Pair (new Object, new Object).snd
test7 = testFJExpr "Tests/Programs/FJ/Pair.java" e
    where
      e = FJ.Invoke p (FJ.Var (Ide "snd"))
      p = FJ.New (mkT "Pair") (seqFromList [o,o])
      o = FJ.New (mkT "Object") emptySeq

-- | Method declaration:
--   Pair setfst(Object newfst) {
--       return new Pair(newfst, this.snd);
--   }
test8 = testFJExpr "Tests/Programs/FJ/Pair.java" m
    where
      m      = FJ.M (mkT "Pair") (Ide "setfst") params (FJ.Return p)
      newfst = FJ.Var (Ide "newfst")
      snd    = FJ.Invoke (FJ.Var (Ide "this")) (FJ.Var (Ide "snd"))
      p      = FJ.New (mkT "Pair") (seqFromList [newfst,snd])
      params = ObjSeq (Data.Sequence.singleton (mkT "Object", newfst))



-- | Constructor declaration:
--   Pair(Object fst, Object snd) {
--       super();
--       this.fst = fst;
--       this.snd = snd;
--   }
test09 = testFJExpr "Tests/Programs/FJ/Pair.java" c
    where
      c       = FJ.C (mkT "Pair") params super assigns
      this    = FJ.Var (Ide "this")
      fst     = FJ.Var (Ide "fst")
      snd     = FJ.Var (Ide "snd")
      params  = seqFromList [(mkT "Object", fst), (mkT "Object", snd)]
      super   = FJ.Meth (Ide "super") emptySeq
      assigns = seqFromList [ FJ.Assign (FJ.Invoke this fst) fst,
                              FJ.Assign (FJ.Invoke this snd) snd ]


-- | Class declaration (Pair):
test10 = do ast <- FJ.parseFromFile "Tests/Programs/FJ/Pair.java"
            let j  = J empty (head ast) (mkTV "T" :: Ty)
                cs = evalTypeCheckM $ genCs (fj ast) j dbg
            putStrLn $ unlines (map pprint cs)


-- | Class declaration with multiple methods.
test11 = do ast <- FJ.parseFromFile "Tests/Programs/FJ/MultipleMethods.java"
            let j  = J empty (head ast) (mkTV "T" :: Ty)
                cs = evalTypeCheckM $ genCs (fj ast) j dbg
            putStrLn $ unlines (map pprint cs)


-- FJ typing rules:
-- 0 - field      4 - method         
-- 1 - new        5 - constructor
-- 2 - invoke     6 - fjclass
-- 3 - cast       7 - var


instFJ1 = TestCase $ do ast <- FJ.parseFromFile "Tests/Programs/FJ/FieldAccess.java"
                        mkAssert "Rule instantiation for FieldAccess.java"
                                 [6,5,4,0,7] (head ast) (fj ast)

instFJ2 = TestCase $ do ast <- FJ.parseFromFile "Tests/Programs/FJ/MethInvk.java"
                        let [c1,c2] = ast
                        mkAssert "Rule instantiation for MethInvk.java class 1"
                                 [6,5,4,2,7] c1 (fj ast)
                        mkAssert "Rule instantiation for MethInvk.java class 2"
                                 [6,5,4,0,7] c2 (fj ast)

instFJ3 = TestCase $ do ast <- FJ.parseFromFile "Tests/Programs/FJ/Cast.java"
                        let [c1,c2,c3] = ast
                        mkAssert "Rule instantiation for Cast.java: class Cast"
                                 [6,5,4,3,0,7,4,3,0,7] c1 (fj ast)
                        mkAssert "Rule instantiation for Cast.java: class A"
                                 [6,5,4,0,7] c2 (fj ast)
                        mkAssert "Rule instantiation for Cast.java: class B"
                                 [6,5,4,0,7] c3 (fj ast)

instFJ4 = TestCase $ do ast <- FJ.parseFromFile "Tests/Programs/FJ/Pair.java"
                        mkAssert "Rule instantiation for Pair.java"
                                 [6,5,4,1,7,0,7] (head ast) (fj ast)

instFJ5 = TestCase $ do ast <- FJ.parseFromFile "Tests/Programs/FJ/Pair2.java"
                        mkAssert "Rule instantiation for Pair2.java"
                                 [6, 5, 4,1,7,0,7, 4,1,0,7,7, 4,0,7, 4,0,7]
                                 (head ast) (fj ast)

instFJTests = TestList [ TestLabel "Instantiation test 1" instFJ1,
                         TestLabel "Instantiation test 2" instFJ2,
                         TestLabel "Instantiation test 3" instFJ3,
                         TestLabel "Instantiation test 4" instFJ4,
                         TestLabel "Instantiation test 5" instFJ5 ]

runFJInstTests = runTestTT instFJTests



-- ###################################################################
--                          Auxiliary Functions
-- ###################################################################

mkTestCaseML file descr res =
    TestCase $ do ast <- ML.parseFromFile file
                  assertEqual descr res
                     (instRules (evalTypeCheckM $ genCs rules
                                 (J empty ast (mkTV "T" :: Ty)) dbg
                                )
                     )


mkAssert descr res c rs =
    assertEqual descr res
                (instRules (evalTypeCheckM $
                            genCs rs (J empty c (mkTV "T" :: Ty)) dbg
                           )
                )