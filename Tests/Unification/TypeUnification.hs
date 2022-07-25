----------------------------------------------------------------------
-- |
-- Module      :  Tests.Unification.TypeUnification
-- Copyright   :  (c) 2010-2011, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
--
-- Tests for unifying and applying substitutions to types.
----------------------------------------------------------------------
module Tests.Unification.TypeUnification ( -- * Unification tests
                                           runUnifyTyTests,
                                           -- * Tests for the
                                           --   application of
                                           --   substitutions
                                           runApplyTyTests ) where

import TypeCheckLib.AbstractSyntax
import TypeCheckLib.Type
import TypeCheckLib.Unification
import TypeCheckLib.Substitution
import TypeCheckLib.Combinators

import Test.HUnit


-- ###################################################################
--                   Tests for unification of types
-- ###################################################################

-------------------------------- types -------------------------------
t1  = mkT "Int"
t2  = mkT "Bool"
mt1 = MT "T1"
mt2 = MT "T2"

uT1 = TestCase ( assertEqual "unify Int Bool"
                             (False, empty)
                             (unify t1 t2) )
uT2 = TestCase ( assertEqual "unify Int T"
                             (True, singleton mt1 t1)
                             (unify mt1 t1) )
uT3 = TestCase ( assertEqual "unify T Bool"
                             (True, singleton mt1 t2)
                             (unify t2 mt1) )

uTTests = TestList [ TestLabel "Unify types test1" uT1,
                     TestLabel "Unify types test2" uT2,
                     TestLabel "Unify types test3" uT3 ]

runUnifyTTests = runTestTT uTTests


------------------------------ type vars -----------------------------
tv1 = mkTV "a"
tv2 = mkTV "b"

uTV1 = TestCase ( assertEqual "unify a b"
                              (True, singleton tv1 tv2)
                              (unify tv1 tv2) )
uTV2 = TestCase ( assertEqual "unify b a"
                              (True, singleton tv2 tv1)
                              (unify tv2 tv1) )
uTV3 = TestCase ( assertEqual "unify a Int"
                              (True, singleton tv1 t1)
                              (unify tv1 t1) )
uTV4 = TestCase ( assertEqual "unify Bool b"
                              (True, singleton tv2 t2)
                              (unify t2 tv2) )
uTV5 = TestCase ( assertEqual "unify a T"
                              (True, singleton mt1 tv1)
                              (unify tv1 mt1) )

uTVTests = TestList [ TestLabel "Unify type vars test1" uTV1,
                      TestLabel "Unify type vars test2" uTV2,
                      TestLabel "Unify type vars test3" uTV3,
                      TestLabel "Unify type vars test4" uTV4,
                      TestLabel "Unify type vars test5" uTV5 ]

runUnifyTVTests = runTestTT uTVTests


--------------------------- function types ---------------------------
ft1 = TF tv1 tv2  -- a -> b
ft2 = TF mt1 mt2  -- T1 -> T2
ft3 = TF t1 t2    -- Int -> Bool
o1 = insert mt2 tv2 (singleton mt1 tv1)
o2 = insert mt2 t2 (singleton mt1 t1)
o3 = insert tv2 t2 (singleton tv1 t1)
o4 = singleton mt1 ft3

uFT1 = TestCase ( assertEqual "unify (a -> b) (T1 -> T2)"
                              (True, o1)      (unify ft1 ft2) )
uFT2 = TestCase ( assertEqual "unify (T1 -> T2) (Int -> Bool)"
                              (True, o2)      (unify ft2 ft3) )
uFT3 = TestCase ( assertEqual "unify (Int -> Bool) (a -> b)"
                              (True, o3)      (unify ft3 ft1) )
uFT4 = TestCase ( assertEqual "unify (Int -> Bool) T1"
                              (True, o4)      (unify ft3 mt1) )
uFT5 = TestCase ( assertEqual "unify (Int -> Bool) Int"
                              (False, empty)  (unify ft3 t1)  )
uFT6 = TestCase ( assertEqual "unify a (a -> b)"
                              (False, empty)  (unify tv1 ft1) )

uFTTests = TestList [ TestLabel "Unify function types test1" uFT1,
                      TestLabel "Unify function types test2" uFT2,
                      TestLabel "Unify function types test3" uFT3,
                      TestLabel "Unify function types test4" uFT4,
                      TestLabel "Unify function types test5" uFT5,
                      TestLabel "Unify function types test5" uFT6 ]

runUnifyFTTests = runTestTT uFTTests


----------------------------- tuple types ----------------------------
tt1 = TT [tv1, tv2]  -- a ** b
tt2 = TT [mt1, mt2]  -- T1 ** T2
tt3 = TT [t1, t2]    -- Int ** Bool
tt4 = TT [tv1, tv1]  -- a ** a
tt5 = TT [tv1, t1]   -- a ** Int
o5 = singleton mt1 tt3
o6 = singleton tv2 t1
o7 = singleton tv1 t1
o8 = singleton tv1 tv2

uTT1 = TestCase ( assertEqual "unify (a ** b) (T1 ** T2)"
                              (True, o1)     (unify tt1 tt2) )
uTT2 = TestCase ( assertEqual "unify (T1 ** T2) (Int ** Bool)"
                              (True, o2)     (unify tt2 tt3) )
uTT3 = TestCase ( assertEqual "unify (Int ** Bool) (a ** b)"
                              (True, o3)     (unify tt3 tt1) )
uTT4 = TestCase ( assertEqual "unify (Int ** Bool) T1"
                              (True, o5)     (unify tt3 mt1) )
uTT5 = TestCase ( assertEqual "unify (Int ** Bool) Int"
                              (False, empty) (unify tt3 t1)  )
uTT6 = TestCase ( assertEqual "unify a (a ** b)"
                              (False, empty) (unify tv1 tt1) )
uTT7 = TestCase ( assertEqual "unify (a ** a) (a ** b)"
                              (True, o8)     (unify tt4 tt1) )
uTT8 = TestCase ( assertEqual "unify (a ** Int) (a ** b)"
                              (True, o6)     (unify tt5 tt1) )
uTT9 = TestCase ( assertEqual "unify (a ** a) (a ** Int)"
                              (True, o7)     (unify tt4 tt5) )

uTTTests = TestList [ TestLabel "Unify tuple types test1" uTT1,
                      TestLabel "Unify tuple types test2" uTT2,
                      TestLabel "Unify tuple types test3" uTT3,
                      TestLabel "Unify tuple types test4" uTT4,
                      TestLabel "Unify tuple types test5" uTT5,
                      TestLabel "Unify tuple types test6" uTT6,
                      TestLabel "Unify tuple types test7" uTT7,
                      TestLabel "Unify tuple types test8" uTT8 ]

runUnifyTTTests = runTestTT uTTTests


------------------------- type constructors --------------------------
tc1 = TC (Ide "List") [tv1]       -- List[a]
tc2 = TC (Ide "List") [t1]        -- List[Int]
tc3 = TC (Ide "Map") [tv1, tv2]   -- Map[a,b]
tc4 = TC (Ide "Map") [t1,t2]      -- Map[Int,Bool]

uTC1 = TestCase ( assertEqual "unify List[a] List[Int]"
                              (True, singleton tv1 t1)
                              (unify tc1 tc2) )
uTC2 = TestCase ( assertEqual "unify List[a] Map[a,b]"
                              (False, empty)
                              (unify tc1 tc3) )
uTC3 = TestCase ( assertEqual "unify a List[a]"
                              (False, empty)
                              (unify tv1 tc1) )
uTC4 = TestCase ( assertEqual "unify a List[Int]"
                              (True, singleton tv1 tc2)
                              (unify tv1 tc2) )
uTC5 = TestCase ( assertEqual "unify List[a] T1"
                              (True, singleton mt1 tc1)
                              (unify tc1 mt1) )

uTCTests = TestList [ TestLabel "Unify type constructors test1" uTC1,
                      TestLabel "Unify type constructors test2" uTC2,
                      TestLabel "Unify type constructors test3" uTC3,
                      TestLabel "Unify type constructors test4" uTC4,
                      TestLabel "Unify type constructors test5" uTC5 ]

runUnifyTCTests = runTestTT uTCTests


---------------------------- type schemes ----------------------------
ts1 = TS [tv1, tv2] (tv1 ->: tv2)     -- ∀ a,b. a -> b
ts2 = TS [tv1] (t1 ->: tv1)           -- ∀ a. Int -> a


----------------------------- all tests ------------------------------
-- | Run all type unification tests.
runUnifyTyTests = runTestTT uTests
    where
      uTests = uTTests $++ uTVTests $++
               uFTTests $++ uTTTests $++ uTCTests
      (TestList xs) $++ (TestList ys) = TestList (xs ++ ys)



-- ###################################################################
--            Tests for application of substitutions to terms
-- ###################################################################

-------------------------------- types -------------------------------

aT1 = TestCase ( assertEqual "Apply {T1/Int} to T1"
                             t1  (singleton mt1 t1 .@. mt1) )
aT2 = TestCase ( assertEqual "Apply {T1/Int} to T2"
                             mt2 (singleton mt1 t1 .@. mt2) )
aT3 = TestCase ( assertEqual "Apply {T1/Int} to Bool"
                             t2  (singleton mt1 t1 .@. t2)  )

aTTests = TestList [ TestLabel "Apply substitutions to types test1" aT1,
                     TestLabel "Apply substitutions to types test2" aT2,
                     TestLabel "Apply substitutions to types test3" aT3 ]

runApplyTTests = runTestTT aTTests


------------------------------ type vars -----------------------------
aTV1 = TestCase ( assertEqual "Apply {a/Int} to a"
                              t1  (singleton tv1 t1 .@. tv1) )
aTV2 = TestCase ( assertEqual "Apply {a/Int} to b"
                              tv2 (singleton tv1 t1 .@. tv2) )
aTV3 = TestCase ( assertEqual "Apply {a/Int} to Bool"
                              t2  (singleton tv1 t1 .@. t2)  )

aTVTests =
    TestList [ TestLabel "Apply substitutions to tvars test1" aTV1,
               TestLabel "Apply substitutions to tvars test2" aTV2,
               TestLabel "Apply substitutions to tvars test3" aTV3 ]

runApplyTVTests = runTestTT aTVTests


--------------------------- function types ---------------------------
aFT1 = TestCase ( assertEqual "Apply {T1/a, T2/b} to T1 -> T2"
                              ft1      (o1 .@. ft2) )
aFT2 = TestCase ( assertEqual "Apply {T1/a, T2/b} to a -> b"
                              ft1      (o1 .@. ft1) )
aFT3 = TestCase ( assertEqual "Apply {a/Int, b/Bool} to a -> b"
                              ft3      (o3 .@. ft1) )
aFT4 = TestCase ( assertEqual "Apply {a/Int, b/Bool} to T1 -> T2"
                              ft2      (o3 .@. ft2) )

aFTTests =
    TestList [ TestLabel "Apply subst to function types test1" aFT1,
               TestLabel "Apply subst to function types test2" aFT2,
               TestLabel "Apply subst to function types test3" aFT3,
               TestLabel "Apply subst to function types test4" aFT4 ]

runApplyFTTests = runTestTT aFTTests


----------------------------- tuple types ----------------------------
aTT1 = TestCase ( assertEqual "Apply {T1/a, T2/b} to T1 ** T2"
                              tt1      (o1 .@. tt2) )
aTT2 = TestCase ( assertEqual "Apply {T1/a, T2/b} to a ** b"
                              tt1      (o1 .@. tt1) )
aTT3 = TestCase ( assertEqual "Apply {a/Int, b/Bool} to a ** b"
                              tt3      (o3 .@. tt1) )
aTT4 = TestCase ( assertEqual "Apply {a/Int, b/Bool} to T1 ** T2"
                              tt2      (o3 .@. tt2) )

aTTTests =
    TestList [ TestLabel "Apply subst to tuple types test1" aTT1,
               TestLabel "Apply subst to tuple types test2" aTT2,
               TestLabel "Apply subst to tuple types test3" aTT3,
               TestLabel "Apply subst to tuple types test4" aTT4 ]

runApplyTTTests = runTestTT aTTTests


------------------------- type constructors --------------------------
aTC1 = TestCase ( assertEqual "Apply {T1/a, T2/b} to List[a]"
                              tc1      (o1 .@. tc1) )
aTC2 = TestCase ( assertEqual "Apply {T1/a, T2/b} to Map[a,b]"
                              tc3      (o1 .@. tc3) )
aTC3 = TestCase ( assertEqual "Apply {a/Int, b/Bool} to List[Int]"
                              tc2      (o3 .@. tc2) )
aTC4 = TestCase ( assertEqual "Apply {a/Int, b/Bool} to Map[a,b]"
                              tc4      (o3 .@. tc3) )

aTCTests =
    TestList [ TestLabel "Apply subst to type constructor test1" aTC1,
               TestLabel "Apply subst to type constructor test2" aTC2,
               TestLabel "Apply subst to type constructor test3" aTC3,
               TestLabel "Apply subst to type constructor test4" aTC4 ]

runApplyTCTests = runTestTT aTCTests


---------------------------- type schemes ----------------------------
ts3 = TS [] (t1 ->: t2)               -- Int -> Bool

aTS1 = TestCase ( assertEqual "Apply {T1/a, T2/b} to ∀ a,b. a -> b"
                              ts1      (o1 .@. ts1) )
aTS2 = TestCase ( assertEqual "Apply {a/Int, b/Bool} to ∀ a,b. a -> b"
                              ts3      (o3 .@. ts1) )

aTSTests =
    TestList [ TestLabel "Apply subst to type scheme test1" aTS1,
               TestLabel "Apply subst to type scheme test2" aTS2 ]

runApplyTSTests = runTestTT aTSTests


----------------------------- all tests ------------------------------
-- | Run all application tests.
runApplyTyTests = runTestTT aTests
    where
      aTests = aTTests $++ aTVTests $++ aFTTests $++
               aTTTests $++ aTCTests $++ aTSTests
      (TestList xs) $++ (TestList ys) = TestList (xs ++ ys)
