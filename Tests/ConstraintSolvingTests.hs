----------------------------------------------------------------------
-- |
-- Module      :  Tests.ConstraintSolvingTests
-- Copyright   :  (c) 2010-2011, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
--
-- Constraint solving tests for the type checker library.
----------------------------------------------------------------------
module Tests.ConstraintSolvingTests ( runMiniMLTests,
                                      runFJTests,
                                      runAllTests ) where

import TypeCheckLib.ConstraintGeneration (genCs)
import TypeCheckLib.ConstraintSolving
import TypeCheckLib.AbstractSyntax
import TypeCheckLib.AbstractSyntax.Term
import TypeCheckLib.Type
import TypeCheckLib.Rule
import TypeCheckLib.Substitution hiding (empty, app, singleton, fromList)
import TypeCheckLib.Combinators hiding (and, or)

import qualified Examples.Parser.MiniML as ML
import qualified Examples.Parser.FJ as FJ
import Examples.TypeSystems.MiniML
import Examples.TypeSystems.FJ
import Examples.Printer.MiniML
import Examples.Printer.FJ

import Prelude hiding (abs, div, and, or, (**), const)

import Test.HUnit


-- ###################################################################
--                   MiniML constraint solving tests                                  
-- ###################################################################

dbg = False

miniMLRules = [true, false, const, add, sub, mul, div, eqi, and, or,
               abs,fix,app,cond,pair,letpoly,letrec,varpoly]

testMiniML file =
    do ast <- ML.parseFromFile file
       let tv = mkTV "T" :: Ty
           res = solveCs (evalTypeCheckM $
                          genCs miniMLRules (J empty ast tv) dbg)
       case res of
         Success o -> putStrLn ("Success: " ++ show (apply o tv))
         Failure j -> putStrLn ("Failure: " ++ show j)
         _         -> putStrLn (show res)


-- (λ x.x) 5
testAbs = solveCs (evalTypeCheckM $ genCs miniMLRules j dbg)
          where
            t     = K App 2 [K Abs 2 [Var (Ide "x"),
                                      Var (Ide "x")],
                             Const 5] 
            j     = J empty t (mkTV "T" :: Ty)

-- (λ x. if x == 0 then 0 else 1) 5
testIf = solveCs (evalTypeCheckM $ genCs miniMLRules j dbg)
         where
           iF = K IfThenElse 3 [K App 2 [K App 2 [Var (Ide "=="),
                                                  Var (Ide "x")],
                                         Const 0],
                                Const 0,
                                Const 1] 
           t  = K App 2 [K Abs 2 [Var (Ide "x"), iF], Const 5] 
           j  = J empty t (mkTV "T" :: Ty)

-- let x = 5 in let y = 2 in (y,x)
testTuple = solveCs (evalTypeCheckM $ genCs miniMLRules j dbg)
            where
              t  = K Let 3 [Var (Ide "x"), Const 5,
                            K Let 3 [Var (Ide "y"),
                                     Const 2,
                                     K Tuple 2 [Var (Ide "x"),
                                                Var (Ide "y")]]]
              j  = J empty t (mkTV "T" :: Ty)

-- letrec fact = λ x. if x==0 then 1 else fact(x-1) in fact 4
testLetRec = solveCs (evalTypeCheckM $ genCs miniMLRules j dbg)
             where
               decr = K App 2 [K App 2 [Var (Ide "-"),
                                        Var (Ide "x")],
                               Const 1]
               iF   = K IfThenElse 3 [K App 2 [K App 2 [Var (Ide "=="),
                                                        Var (Ide "x")],
                                               Const 0],
                                      Const 1,
                                      K App 2 [Var (Ide "fact"), decr]]
               fact = K Abs 2 [Var (Ide "x"), iF] 
               rec  = K LetRec 3 [Var (Ide "fact"),
                                  fact,
                                  K App 2 [Var (Ide "fact"), Const 4]]
               j    = J empty rec (mkTV "T" :: Ty)

-- {double : a -> a,  }
-- {foo : int -> int, } ⊢ (double foo, double bar) : T
-- {bar : bool -> bool}
testPoly1 = solveCs (evalTypeCheckM $ genCs miniMLRules j dbg)
    where
      ctx = fromList [ (Var (Ide "double"),
                        TS [mkTV "a"] (mkTV "a" ->: mkTV "a")),
                       (Var (Ide "foo"), mkT "int" ->: mkT "int"),
                       (Var (Ide "bar"), mkT "bool" ->: mkT "bool") ]
      j   = J ctx (K Tuple 2 [K App 2 [Var (Ide "double"),
                                       Var (Ide "foo")],
                              K App 2 [Var (Ide "double"),
                                       Var (Ide "bar")]]) (mkTV "T" :: Ty)

-- {double : a -> a} ⊢ double + : T
testPoly2 = solveCs (evalTypeCheckM $ genCs miniMLRules j dbg)
    where
      ctx = singleton (Var (Ide "double"))
                      (TS [mkTV "a"] (mkTV "a" ->: mkTV "a"))
      j   = J ctx (K App 2 [Var (Ide "double"),
                            Var (Ide "+")]) (mkTV "T" :: Ty)

-- 5 + true
testBase = solveCs (evalTypeCheckM $ genCs miniMLRules j dbg)
    where
      j = J empty (K App 2 [K App 2 [Var (Ide "+"),
                                     Const 5],
                            Var (Ide "true")]) (mkTV "T" :: Ty)

-- x
testVar = solveCs (evalTypeCheckM $ genCs miniMLRules j dbg)
    where
      j = J empty (Var (Ide "x")) (mkTV "T" :: Ty)

-- 1 + 1
testAdd = solveCs (evalTypeCheckM $ genCs miniMLRules j dbg)
    where
      j = J empty (K App 2 [K App 2 [Var (Ide "+"),
                                     Const 1],
                            Const 1]) (mkTV "T" :: Ty)



miniML1 = TestCase (assertEqual "Constraint solving for lambda abstraction"
                                (mkT "int" ) (let Success o = testAbs
                                              in o .@. (mkTV "T" :: Ty)))

miniML2 = TestCase (assertEqual "Constraint solving for conditionals"
                                (mkT "int" ) (let Success o = testIf
                                              in o .@. (mkTV "T" :: Ty)))

miniML3 = TestCase (assertEqual "Constraint solving for pairs"
                                (mkT "int" ** mkT "int") (let Success o = testTuple
                                                          in o .@. (mkTV "T" :: Ty)))

miniML4 = TestCase (assertEqual "Constraint solving for recursive let"
                                 (mkT "int") (let Success o = testLetRec
                                              in o .@. (mkTV "T" :: Ty)))

miniML5 = TestCase (do ast <- ML.parseFromFile "Tests/Programs/MiniML/pairs.ml"
                       let t         = mkTV "T"
                           Success o = solveCs (evalTypeCheckM $
                                                genCs miniMLRules (J empty ast t) dbg)
                       assertEqual "Constraint solving for pairs"
                                   (mkT "int" ** mkT "int") (o .@. t))

miniML6 = TestCase (do ast <- ML.parseFromFile "Tests/Programs/MiniML/fact.ml"
                       let t         = mkTV "T"
                           Success o = solveCs (evalTypeCheckM $
                                                genCs miniMLRules (J empty ast t) dbg)
                       assertEqual "Constraint solving for fac" (mkT "int") (o .@. t))

miniML7 = TestCase (do ast <- ML.parseFromFile "Tests/Programs/MiniML/twice.ml"
                       let t         = mkTV "T"
                           Success o = solveCs (evalTypeCheckM $
                                                genCs miniMLRules (J empty ast t) dbg)
                       assertEqual "Constraint solving for monomorphic let"
                                   (mkT "int") (o .@. t))

miniML8 = TestCase (do ast <- ML.parseFromFile "Tests/Programs/MiniML/poly.ml"
                       let t         = mkTV "T"
                           Success o = solveCs (evalTypeCheckM $
                                                genCs miniMLRules (J empty ast t) dbg)
                       assertEqual "Constraint solving for polymorphic let"
                                   (mkT "bool" ** mkT "int") (o .@. t))


miniMLTests = TestList [ TestLabel "MiniML constraint solving test 1" miniML1, 
                         TestLabel "MiniML constraint solving test 2" miniML2,
                         TestLabel "MiniML constraint solving test 3" miniML3,
                         TestLabel "MiniML constraint solving test 4" miniML4,
                         TestLabel "MiniML constraint solving test 5" miniML5,
                         TestLabel "MiniML constraint solving test 6" miniML6,
                         TestLabel "MiniML constraint solving test 7" miniML7,
                         TestLabel "MiniML constraint solving test 8" miniML8 ]

runMiniMLTests = runTestTT miniMLTests




-- ###################################################################
--                      FJ constraint solving tests
-- ###################################################################

-- | FeatherweightJava typing rules.
fjRules prg = [ field prg, new prg, invoke prg, cast prg,
                method prg, constructor prg, fjclass prg, var ]
                         

-- | Interactive constraint solving test function.
testFJ fileName = do ast <- FJ.parseFromFile fileName
                     let rs = map (solveFJ ast) ast
                     putStr (unlines rs)


-- | Generate and solve constraints for a given class based on a given
-- program.
solveFJ prog c = let tv = mkTV "T" :: Ty
                     rs = solveCs (evalTypeCheckM $
                                   genCs (fjRules prog) (J empty c tv) dbg)
                 in case rs of
                      Success o -> pprint (apply o tv)
                      Failure j -> "Failure"
                      _         -> show rs

----------------------------------------------------------------------

-- | Constructor call:
--   new Pair (new Object, new Object)
testNew = do ast <- FJ.parseFromFile "Tests/Programs/FJ/Pair.java"
             putStrLn (solveFJ ast e)
    where
      e = FJ.New (mkT "Pair") (seqFromList [o,o])
      o = FJ.New (mkT "Object") emptySeq


-- | Method invocation with arguments:
--   new Pair (new Object, new Object).setfst(new Object)
testInvoke = do ast <- FJ.parseFromFile "Tests/Programs/FJ/Pair.java"
                putStrLn (solveFJ ast e)
    where
      e = FJ.Invoke p s
      p = FJ.New (mkT "Pair") (seqFromList [o,o])
      s = FJ.Meth (Ide "setfst") (seqFromList [o])
      o = FJ.New (mkT "Object") emptySeq


-- | Field access:
--   new Pair (new Object, new Object).snd
testField = do ast <- FJ.parseFromFile "Tests/Programs/FJ/Pair.java"
               putStrLn (solveFJ ast e)
    where
      e = FJ.Invoke p (FJ.Var (Ide "snd"))
      p = FJ.New (mkT "Pair") (seqFromList [o,o])
      o = FJ.New (mkT "Object") emptySeq


-- | Method declaration:
--   Pair setfst(Object newfst) {
--       return new Pair(newfst, this.snd);
--   }
testMethod = do ast <- FJ.parseFromFile "Tests/Programs/FJ/Pair.java"
                let rs = solveCs (evalTypeCheckM $
                                  genCs (fjRules ast) (J empty m okInPair) dbg)
                case rs of
                  Success _ -> putStrLn $ "Success"
                  Failure j -> putStrLn $ "Failure: " ++ pprint j
                  _         -> putStrLn $ show rs
    where
      m        = FJ.M (mkT "Pair") (Ide "setfst") params (FJ.Return p)
      newfst   = FJ.Var (Ide "newfst")
      snd      = FJ.Invoke (FJ.Var (Ide "this")) (FJ.Var (Ide "snd"))
      p        = FJ.New (mkT "Pair") (seqFromList [newfst,snd])
      params   = seqFromList [(mkT "Object", newfst)]
      okInPair = OkIn (mkT "Pair")


-- | Constructor declaration:
--   Pair(Object fst, Object snd) {
--       super();
--       this.fst = fst;
--       this.snd = snd;
--   }
testConstr = do ast <- FJ.parseFromFile "Tests/Programs/FJ/Pair.java"
                putStrLn (solveFJ ast c)
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
testClass = do ast <- FJ.parseFromFile "Tests/Programs/FJ/Pair.java"
               let c = head ast
               putStrLn (solveFJ ast c)



fj1 = TestCase (do [c] <- FJ.parseFromFile "Tests/Programs/FJ/FieldAccess.java"
                   assertEqual "Field access" "Ok" (solveFJ [c] c)
               )

fj2 = TestCase (do ast <- FJ.parseFromFile "Tests/Programs/FJ/MethInvk.java"
                   let [c1,c2] = ast
                   assertEqual "Method invocation" "Ok" (solveFJ ast c1)
                   assertEqual "Method invocation" "Ok" (solveFJ ast c2)
               )

fj3 = TestCase (do ast <- FJ.parseFromFile "Tests/Programs/FJ/MethInvk2.java"
                   let [c1,c2] = ast
                   assertEqual "Method invocation" "Ok" (solveFJ ast c1)
                   assertEqual "Method invocation" "Ok" (solveFJ ast c2)
               )

fj4 = TestCase (do ast <- FJ.parseFromFile "Tests/Programs/FJ/Cast.java"
                   let [c1,c2,c3] = ast
                   assertEqual "Cast" "Ok" (solveFJ ast c1)
                   assertEqual "Cast" "Ok" (solveFJ ast c2)
                   assertEqual "Cast" "Ok" (solveFJ ast c3)
               )

fj5 = TestCase (do ast <- FJ.parseFromFile "Tests/Programs/FJ/MutuallyRec.java"
                   let [c1,c2] = ast
                   assertEqual "Mutually recursive classes" "Ok" (solveFJ ast c1)
                   assertEqual "Mutually recursive classes" "Ok" (solveFJ ast c2)
               )

fj6 = TestCase (do [c] <- FJ.parseFromFile "Tests/Programs/FJ/MultipleMethods.java"
                   assertEqual "Multiple methods" "Ok" (solveFJ [c] c)
               )

fj7 = TestCase (do [c] <- FJ.parseFromFile "Tests/Programs/FJ/ObjectCreation.java"
                   assertEqual "Object creation" "Ok" (solveFJ [c] c)
               )

fj8 = TestCase (do [c] <- FJ.parseFromFile "Tests/Programs/FJ/Pair.java"
                   assertEqual "Pair" "Ok" (solveFJ [c] c)
               )

fj9 = TestCase (do [c] <- FJ.parseFromFile "Tests/Programs/FJ/Pair2.java"
                   assertEqual "Pair2" "Ok" (solveFJ [c] c)
               )

fj10 = TestCase (do ast <- FJ.parseFromFile "Tests/Programs/FJ/Subtyping.java"
                    let [c1,c2,c3,c4] = ast
                    assertEqual "Subtyping" "Ok" (solveFJ ast c1)
                    assertEqual "Subtyping" "Ok" (solveFJ ast c2)
                    assertEqual "Subtyping" "Ok" (solveFJ ast c3)
                    assertEqual "Subtyping" "Ok" (solveFJ ast c4)
                )

fj11 = TestCase (do ast <- FJ.parseFromFile "Tests/Programs/FJ/SubtypWithOverride.java"
                    let [c1,c2] = ast
                    assertEqual "Overriding" "Ok" (solveFJ ast c1)
                    assertEqual "Overriding" "Ok" (solveFJ ast c2)
                )

fj12 = TestCase (do ast <- FJ.parseFromFile "Tests/Programs/FJ/WrongPrograms/WrongCast.java"
                    let [c1,c2,c3] = ast
                    assertEqual "Wrong cast" "Failure" (solveFJ ast c1)
                    assertEqual "Wrong cast" "Ok" (solveFJ ast c2)
                    assertEqual "Wrong cast" "Ok" (solveFJ ast c3)
               )

fj13 = TestCase (do ast <- FJ.parseFromFile "Tests/Programs/FJ/WrongPrograms/WrongConstructor.java"
                    let [c] = ast
                    assertEqual "Wrong constructor" "Failure" (solveFJ ast c)
               )

fj14 = TestCase (do ast <- FJ.parseFromFile "Tests/Programs/FJ/WrongPrograms/WrongFieldAccess.java"
                    let [c] = ast
                    assertEqual "Wrong field access" "Failure" (solveFJ ast c)
               )

fj15 = TestCase (do ast <- FJ.parseFromFile "Tests/Programs/FJ/WrongPrograms/WrongMethodInvokation.java"
                    let [c1,c2] = ast
                    assertEqual "Wrong method invocation" "Failure" (solveFJ ast c1)
                    assertEqual "Wrong method invocation" "Ok" (solveFJ ast c2)
               )

fj16 = TestCase (do ast <- FJ.parseFromFile "Tests/Programs/FJ/WrongPrograms/WrongMethodType.java"
                    let [c] = ast
                    assertEqual "Wrong method type" "Failure" (solveFJ ast c)
               )

fj17 = TestCase (do ast <- FJ.parseFromFile "Tests/Programs/FJ/WrongPrograms/WrongObjectCreation.java"
                    let [c] = ast
                    assertEqual "Wrong object creation" "Failure" (solveFJ ast c)
               )

fj18 = TestCase (do ast <- FJ.parseFromFile "Tests/Programs/FJ/WrongPrograms/WrongOverride.java"
                    let [c1,c2,c3] = ast
                    assertEqual "Wrong override" "Ok" (solveFJ ast c1)
                    assertEqual "Wrong override" "Failure" (solveFJ ast c2)
                    assertEqual "Wrong override" "Ok" (solveFJ ast c3)
               )


fjTests = TestList [ TestLabel "Constraint solving test 1" fj1,
                     TestLabel "Constraint solving test 2" fj2,
                     TestLabel "Constraint solving test 3" fj3,
                     TestLabel "Constraint solving test 4" fj4,
                     TestLabel "Constraint solving test 5" fj5,
                     TestLabel "Constraint solving test 6" fj6,
                     TestLabel "Constraint solving test 7" fj7,
                     TestLabel "Constraint solving test 8" fj8,
                     TestLabel "Constraint solving test 9" fj9,
                     TestLabel "Constraint solving test 10" fj10,
                     TestLabel "Constraint solving test 11" fj11,
                     TestLabel "Constraint solving test 12" fj12,
                     TestLabel "Constraint solving test 13" fj13,
                     TestLabel "Constraint solving test 14" fj14,
                     TestLabel "Constraint solving test 15" fj15,
                     TestLabel "Constraint solving test 16" fj16,
                     TestLabel "Constraint solving test 17" fj17,
                     TestLabel "Constraint solving test 18" fj18 ]


runFJTests = runTestTT fjTests


----------------------------------------------------------------------

-- | Run all tests.
runAllTests = runTestTT allTests
    where
      allTests = miniMLTests $++ fjTests
      (TestList x) $++ (TestList y) = TestList (x ++ y)
