----------------------------------------------------------------------
-- |
-- Module      :  Tests.TypeTests
-- Copyright   :  (c) 2010-2011, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
--
-- Tests for the library's default type implementation.
----------------------------------------------------------------------
module Tests.TypeTests where

import TypeCheckLib.Syntax hiding (empty)
import TypeCheckLib.TypeChecker

import Prelude hiding ((>=))
import qualified Data.Set as S
import Test.HUnit


-- ###################################################################
--        Tests for the library's default type implementation
-- ###################################################################

a = mkTV "a"  ;  b = mkTV "b"  ;  c = mkTV "c"  ;  d = mkTV "d"
mt   = MT "T"
int  = mkT "Int"
bool = mkT "Bool"
et   = mkT "Error"
mc   = MCtx "Gamma"
c1   = empty


--------------------- Generating type schemes ------------------------
t1 = int ->: int
t2 = c ->: d
t3 = a ->: b ->: c ->: d ->: bool
t4 = a ->: b ->: a
t5 = bool × a

g1 = TestCase (assertEqual "gen({},int -> int)"
                           t1                (maybe et id (gen c1 t1)))
g2 = TestCase (assertEqual "gen({},c -> d)"
                           (TS [c,d] t2)     (maybe t2 id (gen c1 t2)))
g3 = TestCase (assertEqual "gen({},a -> b -> c -> d -> bool)"
                           (TS [a,b,c,d] t3) (maybe t3 id (gen c1 t3)))
g4 = TestCase (assertEqual "gen({},a -> b -> a)"
                           (TS [a,b] t4)     (maybe t4 id (gen c1 t4)))
g5 = TestCase (assertEqual "gen({},a -> b -> a)"
                           (TS [a,b] t4)     (maybe t4 id (gen c1 t4)))
g6 = TestCase (assertEqual "gen({},bool ** a)"
                           (TS [a] t5)       (maybe t5 id (gen c1 t5)))
g7 = TestCase (assertEqual "gen(meta cxt, _)"
                           Nothing           (gen mc t1))
g8 = TestCase (assertEqual "gen({}, meta type)"
                           Nothing           (gen c1 mt))

gTests = TestList [ TestLabel "Type scheme generation tests" g1,
                    TestLabel "Type scheme generation tests" g2,
                    TestLabel "Type scheme generation tests" g3,
                    TestLabel "Type scheme generation tests" g4,
                    TestLabel "Type scheme generation tests" g5,
                    TestLabel "Type scheme generation tests" g6,
                    TestLabel "Type scheme generation tests" g7,
                    TestLabel "Type scheme generation tests" g8 ]

runGTests = runTestTT gTests


------------------ Generic instance of a type scheme -----------------
ts1 = TS [a,b] (a ->: b)
ts2 = TS [a] (a ->: b)
ts3 = TS [a] (a ->: int)
ts4 = TS [a] (a ->: a)

gI1 = TestCase ( assertEqual "∀ a,b. a -> b  >=  ∀ a. a -> a"
                            True  (maybe False fst (ts1 >= ts4)) )
gI2 = TestCase ( assertEqual "∀ a,b. a -> b  >=  ∀ a. a -> b"
                            True  (maybe False fst (ts1 >= ts2)) )
gI3 = TestCase ( assertEqual "∀ a,b. a -> b  >=  meta type"
                            Nothing (ts1 >= mt) )
gI4 = TestCase ( assertEqual "meta type  >=  ∀ a,b. a -> b"
                            Nothing (mt  >= ts1) )
gI5 = TestCase ( assertEqual "∀ a,b. a -> b  >=  ∀ a. a -> int"
                            True  (maybe False fst (ts1 >= ts3)) )
gI6 = TestCase ( assertEqual "∀ a,b. a -> b  >=  int -> int"
                            True  (maybe False fst (ts1 >= t1)) )
gI7 = TestCase ( assertEqual "∀ a,b. a -> b  >=  c -> d"
                            True  (maybe False fst (ts1 >= t2)) )

gITests = TestList [ TestLabel "Generic instance tests" gI1,
                     TestLabel "Generic instance tests" gI2,
                     TestLabel "Generic instance tests" gI3,
                     TestLabel "Generic instance tests" gI4,
                     TestLabel "Generic instance tests" gI5,
                     TestLabel "Generic instance tests" gI6,
                     TestLabel "Generic instance tests" gI7 ]

runGITests = runTestTT gITests


----------------------- Free and bound variables ---------------------
tc = TC (Ide "List") [a]

fv1 = TestCase ( assertEqual "Free vars of ∀ a,b. a -> b"
                             (S.empty :: S.Set Ty) (fv ts1))
fv2 = TestCase ( assertEqual "Free vars of ∀ a. a -> b"
                             (S.singleton b)       (fv ts2))
fv3 = TestCase ( assertEqual "Free vars of meta type"
                             (S.empty :: S.Set Ty) (fv mt) )
fv4 = TestCase ( assertEqual "Free vars of Int -> Int"
                             (S.empty :: S.Set Ty) (fv t1) )
fv5 = TestCase ( assertEqual "Free vars of c -> d"
                             (S.fromList [c,d])    (fv t2) )
fv6 = TestCase ( assertEqual "Free vars of bool ** a"
                             (S.singleton a)       (fv t5) )
fv7 = TestCase ( assertEqual "Free vars of List[a]"
                             (S.singleton a)       (fv tc) )

fvTests = TestList [ TestLabel "Free variables in types tests" fv1,
                     TestLabel "Free variables in types tests" fv2,
                     TestLabel "Free variables in types tests" fv3,
                     TestLabel "Free variables in types tests" fv4,
                     TestLabel "Free variables in types tests" fv5,
                     TestLabel "Free variables in types tests" fv6,
                     TestLabel "Free variables in types tests" fv7 ]

runFVTests = runTestTT fvTests


bv1 = TestCase ( assertEqual "Bound vars of ∀ a,b. a -> b"
                             (S.fromList [a,b])    (bv ts1) )
bv2 = TestCase ( assertEqual "Bound vars of ∀ a. a -> b"
                             (S.singleton a)       (bv ts2) )
bv3 = TestCase ( assertEqual "Bound vars of meta type"
                             (S.empty :: S.Set Ty) (bv mt) )
bv4 = TestCase ( assertEqual "Bound vars of Int -> Int"
                             (S.empty :: S.Set Ty) (bv t1) )
bv5 = TestCase ( assertEqual "Bound vars of c -> d"
                             (S.empty :: S.Set Ty) (bv t2) )
bv6 = TestCase ( assertEqual "Bound vars of bool ** a"
                             (S.empty :: S.Set Ty) (bv t5) )
bv7 = TestCase ( assertEqual "Bound vars of List[a]"
                             (S.empty :: S.Set Ty) (bv tc) )

bvTests = TestList [ TestLabel "Bound variables in types tests" bv1,
                     TestLabel "Bound variables in types tests" bv2,
                     TestLabel "Bound variables in types tests" bv3,
                     TestLabel "Bound variables in types tests" bv4,
                     TestLabel "Bound variables in types tests" bv5,
                     TestLabel "Bound variables in types tests" bv6,
                     TestLabel "Bound variables in types tests" bv7 ]

runBVTests = runTestTT bvTests


----------------------------------------------------------------------
-- | Run all type tests.
runAllTyTests = runTestTT allTests
    where
      allTests = gTests $++ gITests $++ fvTests $++ bvTests
      (TestList x) $++ (TestList y) = TestList (x ++ y)