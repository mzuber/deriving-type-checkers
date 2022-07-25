----------------------------------------------------------------------
-- |
-- Module      :  Tests.Unification.TermUnification
-- Copyright   :  (c) 2010-2011, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
--
-- Tests for unifying and applying substitutions to terms.
----------------------------------------------------------------------
module Tests.Unification.TermUnification ( runAllApplyTests,
                                           runAllUnifyTests ) where

import TypeCheckLib.Syntax hiding (mset, mseq)
import TypeCheckLib.AbstractSyntax.Term
import qualified Data.Set
import qualified Data.Sequence
import Test.HUnit


-- ###################################################################
--                    Tests for unification of terms
-- ###################################################################

------------------------------ variables -----------------------------
v  = Ide "foo"
v' = Ide "bar"
x  = MIde "x" :: Ide
x' = MIde "x'" :: Ide

uVar1 = TestCase ( assertEqual "unify foo x"
                               (True, singleton x v) 
                               (unify (Var v) (Var x)) )
uVar2 = TestCase ( assertEqual "unify x bar"
                               (True, singleton x v')
                               (unify (Var x) (Var v')) )
uVar3 = TestCase ( assertEqual "unify foo bar"
                               (False, empty)
                               (unify (Var v) (Var v')) )
uVar4 = TestCase ( assertEqual "unify x x'"
                               (True, singleton x x')
                               (unify (Var x) (Var x')) )
uVar5 = TestCase ( assertEqual "unify foo foo"
                               (True, empty)
                               (unify (Var v) (Var v)) )

uVarTests = TestList [ TestLabel "Unify vars test1" uVar1,
                       TestLabel "Unify vars test2" uVar2,
                       TestLabel "Unify vars test3" uVar3,
                       TestLabel "Unify vars test4" uVar4,
                       TestLabel "Unify vars test5" uVar5 ]

runUnifyVarTests = runTestTT uVarTests


------------------------------ constants -----------------------------
c  = Const 42
c' = Const 23
y  = MConst "y"
y' = MConst "y'"

uConst1 = TestCase ( assertEqual "unify 42 (MConst y)"
                                 (True, singleton y c)
                                 (unify c y) )
uConst2 = TestCase ( assertEqual "unify (MConst y) 23"
                                 (True, singleton y c')
                                 (unify y c') )
uConst3 = TestCase ( assertEqual "unify 42 23"
                                 (False, empty)
                                 (unify c c') )
uConst4 = TestCase ( assertEqual "unify 42 x"
                                 (False, empty)
                                 (unify c (Var x)) )
uConst5 = TestCase ( assertEqual "unify 42 42"
                                 (True,empty)
                                 (unify c c) )
uConst6 = TestCase ( assertEqual "unify MConst MConst"
                                 (True, singleton y' y)
                                 (unify y' y) )

uConstTests = TestList [ TestLabel "Unify consts test1" uConst1,
                         TestLabel "Unify consts test2" uConst2,
                         TestLabel "Unify consts test3" uConst3,
                         TestLabel "Unify consts test4" uConst4,
                         TestLabel "Unify consts test5" uConst5,
                         TestLabel "Unify consts test6" uConst6 ]

runUnifyConstTests = runTestTT uConstTests


----------------------------- characters -----------------------------
ch1 = Char 'c'
ch2 = Char 'd'
mc1 = MChar "x"
mc2 = MChar "y"

uChar1 = TestCase ( assertEqual "unify 'c' (MChar x)"
                                (True, singleton mc1 ch1)
                                (unify ch1 mc1) )
uChar2 = TestCase ( assertEqual "unify (MChar y) 'd'"
                                (True, singleton mc2 ch2)
                                (unify mc2 ch2) )
uChar3 = TestCase ( assertEqual "unify 'c' 'd'"
                                (False, empty)
                                (unify ch1 ch2) )
uChar4 = TestCase ( assertEqual "unify 'd' 'd'"
                                (True, empty)
                                (unify ch2 ch2) )
uChar5 = TestCase ( assertEqual "unify MChar MChar"
                                (True, singleton mc2 mc1)
                                (unify mc2 mc1) )

uCharTests = TestList [ TestLabel "Unify chars test1" uChar1,
                        TestLabel "Unify chars test2" uChar2,
                        TestLabel "Unify chars test3" uChar3,
                        TestLabel "Unify chars test4" uChar4,
                        TestLabel "Unify chars test5" uChar5 ]

runUnifyCharTests = runTestTT uCharTests


------------------------------ binder --------------------------------
b1 = Bind v y
b2 = Bind v' c
b3 = Bind v c
mb = Bind x y

uBind1 = TestCase ( assertEqual "unify (Bind foo y) (Bind bar 42)"
                                (False, empty)
                                (unify b1 b2) )
uBind2 = TestCase ( assertEqual "unify (Bind foo y) (Bind foo y)"
                                (True, empty)
                                (unify b1 b1) )
uBind3 = TestCase ( assertEqual "unify (Bind foo y) (Bind foo 42)"
                                (True, singleton y c)
                                (unify b1 b3) )
uBind4 = TestCase ( assertEqual "unify (Bind foo 42) (MBind x y)"
                                (True, insert y c (singleton x v))
                                (unify b3 mb) )

uBindTests = TestList [ TestLabel "Unify binder test1" uBind1,
                        TestLabel "Unify binder test2" uBind2,
                        TestLabel "Unify binder test3" uBind3,
                        TestLabel "Unify binder test4" uBind4 ]

runUnifyBindTests = runTestTT uBindTests


----------------------------- combiner -------------------------------
k1 = K App 3 [Var v, Var x, y]
k2 = K App 3 [Var v, Var (Ide "w"), Const 5]
k3 = K Abs 4 [Var v, Var (Ide "w"), Const 5, Const 5]
ks = insert y (Const 5) (singleton x (Ide "w"))

uK1 = TestCase ( assertEqual "Unify combiner with different tags"
                             (False, empty)
                             (unify k1 k3) )
uK2 = TestCase ( assertEqual "Unify combiner with unifiable term list"
                             (True, ks)
                             (unify k1 k2) )

uKTests = TestList [ TestLabel "Unify combiner test1" uK1,
                     TestLabel "Unify combiner test2" uK2 ]

runUnifyCombTests = runTestTT uKTests


----------------------------- sequences ------------------------------
mseq  = mSeq "I" (Var (MIde"e"))
oseq1 = TSeq (seqFromList [Var (Ide "x"), Var (Ide "y"), Var (Ide "z")])
oseq2 = TSeq (seqFromList [Var (Ide "x"), Var (Ide "y")])
oseq3 = TSeq (seqFromList [Var (MIde "e1"), Var (Ide "y")])
s1 = insert (MetaISet "I") (ISet [1,2,3]) (insert (MIde "e3")(Ide "z")
     (insert (MIde "e2") (Ide "y") (singleton (MIde "e1") (Ide "x"))))
s2 = insert (MetaISet "I") (ISet [1,2]) (insert (MIde "e2") (Ide "y")
     (insert (MIde "e1") (Ide "x") (singleton (MIde "m") (Ide "foo"))))
s3 = singleton (MIde "e1") (Ide "x")
kseq1 = K App 2 [Var (MIde "m") , mseq]
kseq2 = K App 3 [Var (Ide "foo"), Var (Ide "x"), Var (Ide "y")]

uSeq1 = TestCase ( assertEqual "unify meta and object level seq"
                               (True, s1)
                               (unify mseq  oseq1) )
uSeq2 = TestCase ( assertEqual "unify meta seq in combiner 1"
                               (True, s2)
                               (unify kseq2 kseq1) )
uSeq3 = TestCase ( assertEqual "unify meta seq in combiner 2"
                               (False, empty)
                               (unify kseq1 k1) )
uSeq4 = TestCase ( assertEqual "unify object level seqs"
                               (False, empty)
                               (unify oseq1 oseq2) )
uSeq5 = TestCase ( assertEqual "unify object level seqs"
                               (True, s3)
                               (unify oseq2 oseq3) )

uSeqTests = TestList [ TestLabel "Unify term seqs test1" uSeq1,
                       TestLabel "Unify term seqs test2" uSeq2,
                       TestLabel "Unify term seqs test3" uSeq3,
                       TestLabel "Unify term seqs test4" uSeq4,
                       TestLabel "Unify term seqs test4" uSeq5 ]

runUnifySeqTests = runTestTT uSeqTests


------------------------------- sets ---------------------------------
mset  = mSet "I" (Var (MIde "e"))
oset1 = TSet (setFromList [Var (Ide "x"), Var (Ide "y"), Var (Ide "z")])
oset2 = TSet (setFromList [Var (Ide "x"), Var (Ide "y")])
oset3 = TSet (setFromList [Var (MIde "e1"), Var (Ide "y")])
kset1 = K App 2 [Var (MIde "m"), mset]
kset2 = K App 3 [Var (Ide "foo"), Var (Ide "x"), Var (Ide "y")]

uSet1 = TestCase ( assertEqual "unify meta and object level set"
                               (True, s1)
                               (unify mset  oset1) )
uSet2 = TestCase ( assertEqual "unify meta set in combiner"
                               (True, s2)
                               (unify kset2 kset1) )
uSet3 = TestCase ( assertEqual "unify meta set in combiner"
                               (False, empty)
                               (unify kset1 k1) )
uSet4 = TestCase ( assertEqual "unify object level sets"
                               (False, empty)
                               (unify oset1 oset2) )
uSet5 = TestCase ( assertEqual "unify object level sets"
                               (True, s3)
                               (unify oset3 oset2) )

uSetTests = TestList [ TestLabel "Unify term sets test1" uSet1,
                       TestLabel "Unify term sets test2" uSet2,
                       TestLabel "Unify term sets test3" uSet3,
                       TestLabel "Unify term sets test4" uSet4,
                       TestLabel "Unify term sets test4" uSet5 ]

runUnifySetTests = runTestTT uSetTests


-------------------------- meta terms --------------------------------
mt  = MTerm "e"
mt2 = MTerm "f"

uMTerm1 = TestCase ( assertEqual "unify MTerm and Var"
                                 (True, singleton mt (Var v))
                                 (unify mt (Var v)) )
uMTerm2 = TestCase ( assertEqual "unify MTerm and Const"
                                 (True, singleton mt c)
                                 (unify c   mt) )
uMTerm3 = TestCase ( assertEqual "unify MTerm and Char"
                                 (True, singleton mt ch1)
                                 (unify mt  ch1) )
uMTerm4 = TestCase ( assertEqual "unify MTerm and Bind"
                                 (True, singleton mt b1)
                                 (unify mt  b1) )
uMTerm5 = TestCase ( assertEqual "unify MTerm and K"
                                 (True, singleton mt k1)
                                 (unify k1  mt) )
uMTerm6 = TestCase ( assertEqual "unify MTerm and seq"
                                 (True, singleton mt mseq)
                                 (unify mseq mt) )
uMTerm7 = TestCase ( assertEqual "unify MTerm and set"
                                 (True, singleton mt oset1)
                                 (unify mt oset1) )
uMTerm8 = TestCase ( assertEqual "unify MTerm and MTerm"
                                 (True, singleton mt2 mt)
                                 (unify mt2 mt) )

uMTermTests = TestList [ TestLabel "Unify meta terms test1" uMTerm1,
                         TestLabel "Unify meta terms test2" uMTerm2,
                         TestLabel "Unify meta terms test3" uMTerm3,
                         TestLabel "Unify meta terms test4" uMTerm4,
                         TestLabel "Unify meta terms test5" uMTerm5,
                         TestLabel "Unify meta terms test6" uMTerm6,
                         TestLabel "Unify meta terms test7" uMTerm7,
                         TestLabel "Unify meta terms test8" uMTerm8 ]

runUnifyMTermTests = runTestTT uMTermTests


----------------------------- empty term -----------------------------
uNil1 = TestCase ( assertEqual "unify Nil and Nil"
                               (True, empty)
                               (unify Nil Nil) )
uNil2 = TestCase ( assertEqual "unify MTerm and Nil"
                               (True, singleton mt Nil)
                               (unify mt Nil) )
uNil3 = TestCase ( assertEqual "unify Nil and MVar"
                               (False, empty)
                               (unify Nil (Var x)) )
uNil4 = TestCase ( assertEqual "unify MConst and Nil"
                               (False, empty)
                               (unify y Nil) )
uNil5 = TestCase ( assertEqual "unify Nil and MChar"
                               (False, empty)
                               (unify Nil mc1) )
uNil6 = TestCase ( assertEqual "unify MBind and Nil"
                               (False, empty)
                               (unify mb Nil) )

uNilTests = TestList [ TestLabel "Unify empty terms test1" uNil1,
                       TestLabel "Unify empty terms test2" uNil2,
                       TestLabel "Unify empty terms test3" uNil3,
                       TestLabel "Unify empty terms test4" uNil4,
                       TestLabel "Unify empty terms test5" uNil5,
                       TestLabel "Unify empty terms test6" uNil6 ]

runUnifyNilTests = runTestTT uNilTests


---------------------- run all unification tests ---------------------
(TestList x) +++ (TestList y) = TestList (x ++ y)

runAllUnifyTests = runTestTT allUnifyTests
    where
      allUnifyTests = uVarTests +++ uConstTests +++ uCharTests +++
                      uMTermTests +++ uBindTests +++ uKTests +++
                      uSeqTests +++ uSetTests +++ uNilTests




-- ###################################################################
--            Tests for application of substitutions to terms
-- ###################################################################

----------------------------- variables ------------------------------
o1 = singleton x v

aVar1 = TestCase ( assertEqual "apply subst to meta var"
                               (Var v)
                               (o1 .@. (Var x)) )
aVar2 = TestCase ( assertEqual "apply subst to meta const"
                               y 
                               (o1 .@. y) )
aVar3 = TestCase ( assertEqual "apply subst to var"
                               (Var v)
                               (o1 .@. (Var v)) )

aVarTests = TestList [ TestLabel "Apply subst to vars test1" aVar1,
                       TestLabel "Apply subst to vars test2" aVar2,
                       TestLabel "Apply subst to vars test3" aVar3 ]

runApplyVarTests = runTestTT aVarTests


----------------------------- constants ------------------------------
o2 = singleton y c

aConst1 = TestCase ( assertEqual "apply subst to meta const"
                                 c
                                 (o2 .@. y) )
aConst2 = TestCase ( assertEqual "apply subst to meta var"
                                 x
                                 (o2 .@. x) )
aConst3 = TestCase ( assertEqual "apply subst to const"
                                 c'
                                 (o2 .@. c') )

aCTests = TestList [ TestLabel "Apply subst to consts test1" aConst1,
                     TestLabel "Apply subst to consts test2" aConst2,
                     TestLabel "Apply subst to consts test2" aConst3 ]

runApplyConstTests = runTestTT aCTests


----------------------------- characters -----------------------------
o3 = singleton mc1 ch1

aChar1 = TestCase ( assertEqual "apply subst to meta char"
                                ch1
                                (o3 .@. mc1) )
aChar2 = TestCase ( assertEqual "apply subst to meta char"
                                mc2
                                (o3 .@. mc2) )
aChar3 = TestCase ( assertEqual "apply subst to char"
                                ch1
                                (o3 .@. ch1) )
aChar4 = TestCase ( assertEqual "apply subst to meta var"
                                x
                                (o3 .@. x) )
aChar5 = TestCase ( assertEqual "apply subst to meta const"
                                y
                                (o3 .@. y) )

aCharTests = TestList [ TestLabel "Apply subst to chars test1" aChar1,
                        TestLabel "Apply subst to chars test2" aChar2,
                        TestLabel "Apply subst to chars test3" aChar3,
                        TestLabel "Apply subst to chars test4" aChar4,
                        TestLabel "Apply subst to chars test5" aChar5 ]

runApplyCharTests = runTestTT aCharTests


------------------------------ binder --------------------------------
b4 = Bind v (Var x)
o4 = singleton mb b1

aBind1 = TestCase ( assertEqual "apply subst to meta var Bind"
                                b1
                                (o4 .@. mb) )
aBind2 = TestCase ( assertEqual "apply subst to Bind"
                                b1
                                (o4 .@. b1) )

aBindTests = TestList [ TestLabel "Apply subst to binder test1" aBind1,
                        TestLabel "Apply subst to binder test2" aBind2 ]

runApplyBindTests = runTestTT aBindTests


----------------------------- combiner -------------------------------
o5 = insert x (Ide "w") (singleton y (Const 5))

aComb1 = TestCase ( assertEqual "apply subst to combiner"
                                k2
                                (o5 .@. k1) )
aComb2 = TestCase ( assertEqual "apply subst to combiner"
                                k1
                                (o4 .@. k1) )
aComb3 = TestCase ( assertEqual "apply subst to combiner"
                                k1
                                (o3 .@. k1) )

aKTests = TestList [ TestLabel "Apply subst to combiner test1" aComb1,
                     TestLabel "Apply subst to combiner test2" aComb2,
                     TestLabel "Apply subst to combiner test3" aComb3 ]

runApplyKTests = runTestTT aKTests


----------------------------- sequences ------------------------------
mseqA = TSeq (MetaSeq (ISet [1,2]) (Var (MIde "e"))) 
o6 = insert (MetaISet "I") (ISet [1,2])
     (insert (MIde "e1") (Ide "x") (singleton (MIde "e1") (Ide "y")))

aSeq1 = TestCase ( assertEqual "apply subst to meta level seq"
                               mseqA
                               (o6 .@. mseq) )
aSeq2 = TestCase ( assertEqual "apply subst to object level seq"
                               oseq2
                               (o6 .@. oseq3) )

aSeqTests = TestList [ TestLabel "Apply subst to seq test1" aSeq1,
                       TestLabel "Apply subst to seq test2" aSeq2 ]

runApplySeqTests = runTestTT aSeqTests


------------------------------- sets ---------------------------------
msetA = TSet (MetaSet (ISet [1,2]) (Var (MIde "e"))) 
o7 = insert (MetaISet "I") (ISet [1,2])
     (insert (MIde "e1") (Ide "x") (singleton (MIde "e1") (Ide "y")))

aSet1 = TestCase ( assertEqual "apply subst to meta level set"
                               msetA
                               (o6 .@. mset) )
aSet2 = TestCase ( assertEqual "apply subst to object level set"
                               oset2
                               (o6 .@. oset3) )

aSetTests = TestList [ TestLabel "Apply subst to set test1" aSet1,
                       TestLabel "Apply subst to set test2" aSet2 ]

runApplySetTests = runTestTT aSetTests


-------------------------- meta terms --------------------------------
o8 = insert mt2 b1 (singleton mt (Var v))

aMTerm1 = TestCase ( assertEqual "apply subst to meta term"
                                 (Var v)
                                 (o8 .@. mt) )
aMTerm2 = TestCase ( assertEqual "apply subst to meta term"
                                 b1
                                 (o8 .@. mt2) )
aMTerm3 = TestCase ( assertEqual "apply subst to meta var"
                                 (Var x)
                                 (o8 .@. (Var x)) )
aMTerm4 = TestCase ( assertEqual "apply subst to meta const"
                                 y
                                 (o8 .@. y) )
aMTerm5 = TestCase ( assertEqual "apply subst to meta char"
                                 mc1 (o8 .@. mc1) )

aMTermTests =
    TestList [ TestLabel "Apply subst to meta term test1" aMTerm1,
               TestLabel "Apply subst to meta term test2" aMTerm2,
               TestLabel "Apply subst to meta term test3" aMTerm3,
               TestLabel "Apply subst to meta term test4" aMTerm4,
               TestLabel "Apply subst to meta term test5" aMTerm5 ]

runApplyMetaTermTests = runTestTT aMTermTests


----------------------------- empty term -----------------------------
o9 = singleton mt Nil

aNil1 = TestCase ( assertEqual "apply subst to Nil"
                               Nil
                               (o9 .@. Nil) )
aNil2 = TestCase ( assertEqual "apply subst to MTerm"
                               Nil
                               (o9 .@. mt) )
aNil3 = TestCase ( assertEqual "apply subst to Var"
                               (Var v)
                               (o9 .@. (Var v)) )
aNil4 = TestCase ( assertEqual "apply subst to MChar"
                               mc1
                               (o9 .@. mc1) )

aNilTests = TestList [ TestLabel "Apply subst to Nil test1" aNil1,
                       TestLabel "Apply subst to Nil test2" aNil2,
                       TestLabel "Apply subst to Nil test3" aNil3,
                       TestLabel "Apply subst to Nil test4" aNil4 ]

runApplyNilTests = runTestTT aNilTests


---------------------- run all apply tests ---------------------------
runAllApplyTests = runTestTT allApplyTests
    where
      allApplyTests = aVarTests +++ aCTests +++ aCharTests +++
                      aBindTests +++ aMTermTests +++ aKTests +++
                      aSeqTests +++ aSetTests +++ aNilTests