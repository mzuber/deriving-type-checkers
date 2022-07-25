----------------------------------------------------------------------
-- |
-- Module      :  TypeCheckLib.Tests.Unification.DefUnification
-- Copyright   :  (c) 2010-2011, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
--
-- Tests for unifying definitions.
----------------------------------------------------------------------
module Tests.Unification.DefUnification where

import TypeCheckLib.Syntax hiding (mset, mseq)
import TypeCheckLib.AbstractSyntax.Term
import TypeCheckLib.AbstractSyntax.Def
import qualified Data.Set
import qualified Data.Sequence
import Test.HUnit


-- ###################################################################
--                   Tests for unification of defs
-- ###################################################################

---------------------------- definitions -----------------------------
d1  = Def (Ide "Object")  (Var (Ide "fst"))
d2  = Def (Ide "Object")  (Var (MIde "f"))
d3  = Def (Ide "Integer") (Var (Ide "fst"))
d4  = Def (Ide "Object")  (Var (Ide "snd"))
d5  = Def (MIde "C")      (Var (MIde "f"))
o1  = singleton (MIde "f") (Ide "fst")
o2  = singleton (MIde "C") (Ide "Object") .*. o1

uDef1 = TestCase ( assertEqual "unify (Def Var) (Def MVar)"
                               (True, o1)
                               (unify d1 d2) )
uDef2 = TestCase ( assertEqual "unify (Def MVar) (Def Var)"
                               (True, o1)
                               (unify d2 d1) )
uDef3 = TestCase ( assertEqual "unify Def (Meta Def)"
                               (True, o2)
                               (unify d5 d1) )
uDef4 = TestCase ( assertEqual "unify (Meta Def) Def"
                               (True, o2)
                               (unify d1 d5) )
uDef5 = TestCase ( assertEqual "unify Def Def"
                               (False, empty)
                               (unify d1 d3) )
uDef6 = TestCase ( assertEqual "unify Def Def"
                               (False, empty)
                               (unify d1 d4) )

uDefTests = TestList [ TestLabel "Unify defs test1" uDef1,
                       TestLabel "Unify defs test2" uDef2,
                       TestLabel "Unify defs test3" uDef3,
                       TestLabel "Unify defs test4" uDef4,
                       TestLabel "Unify defs test5" uDef5,
                       TestLabel "Unify defs test6" uDef6 ]

runUnifyDefTests = runTestTT uDefTests


----------------------------- sequences ------------------------------
mseq  = mSeq "I" (MDef "e")
oseq1 = DSeq (seqFromList [d1, d1, d1])
oseq2 = DSeq (seqFromList [d2, d2, d2])
oseq3 = DSeq (seqFromList [d1, d2])
o3    = insert (MetaISet "I") (ISet [1,2,3]) (insert (MDef "e3") d1
        (insert (MDef "e2") d1 (singleton (MDef "e1") d1)))

uSeq1 = TestCase ( assertEqual "unify meta and object level seq"
                               (True, o3)
                               (unify mseq  oseq1) )
uSeq2 = TestCase ( assertEqual "unify object level seqs"
                               (False, empty)
                               (unify oseq1 oseq3) )
uSeq3 = TestCase ( assertEqual "unify object level seqs"
                               (True, o1)
                               (unify oseq2 oseq1) )

uSeqTests = TestList [ TestLabel "Unify term seqs test1" uSeq1,
                       TestLabel "Unify term seqs test2" uSeq2,
                       TestLabel "Unify term seqs test3" uSeq3 ]

runUnifySeqTests = runTestTT uSeqTests


------------------------------- sets ---------------------------------
mset  = mSet "I" (MDef "e")
oset1 = DSet (setFromList [d1, d3, d4])
oset2 = DSet (setFromList [d2, d3, d4])
oset3 = DSet (setFromList [d1, d2])
o4    = insert (MetaISet "I") (ISet [1,2,3]) (insert (MDef "e3") d4
        (insert (MDef "e2") d1 (singleton (MDef "e1") d3)))

uSet1 = TestCase ( assertEqual "unify meta and object level set"
                               (True, o4)
                               (unify mset  oset1) )
uSet2 = TestCase ( assertEqual "unify object level sets"
                               (False, empty)
                               (unify oset1 oset3) )
uSet3 = TestCase ( assertEqual "unify object level sets"
                               (True, o1)
                               (unify oset2 oset1) )

uSetTests = TestList [ TestLabel "Unify term sets test1" uSet1,
                       TestLabel "Unify term sets test2" uSet2,
                       TestLabel "Unify term sets test3" uSet3
                     ]

runUnifySetTests = runTestTT uSetTests


----------------------------- meta def -------------------------------
md = MDef "d"

uMDef1 = TestCase ( assertEqual "unify MDef Def"
                                (True, singleton md d1)
                                (unify md d1) )
uMDef2 = TestCase ( assertEqual "unify DSeq MDef"
                                (True, singleton md oseq1)
                                (unify oseq1 md) )
uMDef3 = TestCase ( assertEqual "unify MDef DSeq"
                                (True, singleton md oset1)
                                (unify md oset1) )

uMDefTests = TestList [ TestLabel "unify meta def tes1" uMDef1,
                        TestLabel "unify meta def tes2" uMDef2,
                        TestLabel "unify meta def tes3" uMDef3 ]

runUnifyMDefTests = runTestTT uMDefTests


---------------------------- empty def -------------------------------
o5 = singleton md EmptyDef

uEDef1 = TestCase ( assertEqual "unify empty defs"
                                (True, empty)
                                (unify EmptyDef EmptyDef) )
uEDef2 = TestCase ( assertEqual "unify EDef MDef"
                                (True, o5)
                                (unify EmptyDef md) )
uEDef3 = TestCase ( assertEqual "unify Def EDef"
                                (False, empty)
                                (unify EmptyDef d1) )

uEDefTests = TestList [ TestLabel "unify empty def tes1" uEDef1,
                        TestLabel "unify empty def tes2" uEDef2,
                        TestLabel "unify empty def tes3" uEDef3 ]

runUnifyEmptyDefTests = runTestTT uEDefTests


---------------------- run all unification tests ---------------------
(TestList x) +++ (TestList y) = TestList (x ++ y)

runAllUnifyTests = runTestTT allUnifyTests
    where
      allUnifyTests = uDefTests +++ uSeqTests +++
                      uSetTests +++ uMDefTests +++ uEDefTests