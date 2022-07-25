{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
-- {-# OPTIONS_GHC -ddump-splices #-}
----------------------------------------------------------------------
-- |
-- Module      :  Examples.Parser.FJ
-- Copyright   :  (c) 2010-2011, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
-- 
-- Parser and abstract syntax for FeatherweightJava.
----------------------------------------------------------------------
module Examples.Parser.FJ ( -- * Abstract Syntax
                            FJExpr (..),
                            FJMethod (..),
                            FJConstructor (..),
                            FJClass (..),
                            -- * Parser
                            Examples.Parser.FJ.parse,
                            Examples.Parser.FJ.parseExpr,
                            Examples.Parser.FJ.parseFromFile ) where

import TypeCheckLib.Syntax

import Text.Parsec
import Text.Parsec.String
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (javaStyle)

import Data.Typeable
import Prelude hiding (elem)
import Data.Foldable (elem)


-- ###################################################################
--                      Abstract Syntax for FJ
-- ###################################################################

---------------------------- Expressions -----------------------------

-- | FeatherweightJava expressions.
data FJExpr
    -- | Variables: @x@
    = Var Ide
    -- | Field lookup/ Method invocation
    | Invoke FJExpr FJExpr
    -- | Method call: @m(e1, ... , en)@
    | Meth Ide (Sequence FJExpr)
    -- | Constructor call: @new C(e1, ... , en)@
    | New Ty (Sequence FJExpr)
    -- | Cast: @(C) e;@
    | Cast Ty FJExpr
    -- | Assignment: @e1 = e2;@
    | Assign FJExpr FJExpr
    -- | Return statement: @return e;@
    | Return FJExpr
    -- | Meta level expressionq
    | MExpr String
      deriving (Show, Eq, Ord, Typeable)


instance AST FJExpr where
    index (Var x)       n = Var (index x n)
    index (Invoke e f)  n = Invoke (index e n) (index f n)
    index (Meth m args) n = Meth (index m n) (indexM args n)
    index (New c args)  n = New (index c n) (indexM args n)
    index (Cast c e)    n = Cast (index c n) (index e n)
    index (Assign l r)  n = Assign (index l n) (index r n)
    index (Return e)    n = Return (index e n)
    index (MExpr ide)   n = MExpr (ide ++ show n)

    (MExpr _) ~= e = case e of
                       MExpr _ -> False
                       _       -> True
    _ ~= _         = False

    isMeta (MExpr _) = True
    isMeta _         = False


$(deriveEvaluable ''FJExpr)

$(deriveSubstitutable ''FJExpr)

$(deriveInstantiable ''FJExpr)

$(deriveUnifiable ''FJExpr)

$(deriveVars ''FJExpr)


------------------------------ Methods -------------------------------

-- | FeatherweightJava method declarations.
data FJMethod = M { -- | Return type
                    mRetTy  :: Ty,
                    -- | Method name
                    mName   :: Ide,
                    -- | Parameters
                    mParams :: Sequence (Ty, FJExpr),
                    -- | Method body (return statement)
                    mBody   :: FJExpr
                  }
              | MM String  -- ^ Meta level method
                deriving (Show, Eq, Ord, Typeable)


instance AST FJMethod where
    index (MM ide)      n = MM (ide ++ show n)
    index (M rt m ps b) n = M (indexM rt n) (indexM m n)
                              (indexM ps n) (indexM b n)

    (MM _) ~= (M _ _ _ _) = True
    _      ~= _           = False

    isMeta (MM _)      = True
    isMeta (M _ _ _ _) = False


$(deriveEvaluable ''FJMethod)

$(deriveSubstitutable ''FJMethod)

$(deriveInstantiable ''FJMethod)

$(deriveUnifiable ''FJMethod)

$(deriveVars ''FJMethod)


---------------------------- Constructors ----------------------------

-- | FeatherweightJava constructor declaration.
data FJConstructor = C { -- | Constructor name
                         cName   :: Ty,
                         -- | Parameters
                         cParams :: Sequence (Ty, FJExpr),
                         -- | Call to super constructor
                         super   :: FJExpr,
                         -- | Assignments
                         assigns :: Sequence FJExpr
                       }
                   | MC String  -- ^ Meta level constructor.
                     deriving (Show, Eq, Ord, Typeable)


instance AST FJConstructor where
    index (MC ide)      n = MC (ide ++ show n)
    index (C c ps s as) n = C (indexM c n) (indexM ps n)
                              (indexM s n) (indexM as n)

    (MC _) ~= (C _ _ _ _) = True
    _      ~= _           = False

    isMeta (MC _) = True
    isMeta _      = False


$(deriveEvaluable ''FJConstructor)

$(deriveSubstitutable ''FJConstructor)

$(deriveInstantiable ''FJConstructor)

$(deriveUnifiable ''FJConstructor)

$(deriveVars ''FJConstructor)


------------------------------- Classes ------------------------------

-- | FeatherweightJava class definition.
data FJClass = Class { -- | Class name
                       clName      :: Ty,
                       -- | Superclass
                       superClass  :: Ty,
                       -- | Attributes
                       attributes  :: Sequence (Ty,FJExpr),
                       -- | Constructor
                       constructor :: FJConstructor,
                       -- | Methods
                       methods     :: Sequence FJMethod
                     }
               deriving (Show, Eq, Ord, Typeable)

instance AST FJClass where
    index (Class c d as k ms) n = Class (indexM c n) (indexM d n)
                                        (indexM as n) (indexM k n)
                                        (indexM ms n)

    _ ~= _ = False

    isMeta = const False


$(deriveEvaluable ''FJClass)

$(deriveSubstitutable ''FJClass)

$(deriveInstantiable ''FJClass)

$(deriveUnifiable ''FJClass)

$(deriveVars ''FJClass)


-- ###################################################################
--                     FeatherweightJava lexer
-- ###################################################################
javaDef = javaStyle{ P.reservedOpNames = ["=", "."]
                   , P.reservedNames   = ["class", "extends",
                                          "return", "super"]
                   , P.caseSensitive   = True
                   }

lexer  = P.makeTokenParser javaDef

parens          = P.parens lexer    
braces          = P.braces lexer
semi            = P.semi lexer    
semiSep         = P.semiSep lexer  
semiSep1        = P.semiSep1 lexer    
commaSep        = P.commaSep lexer
commaSep1       = P.commaSep1 lexer
brackets        = P.brackets lexer
whiteSpace      = P.whiteSpace lexer    
symbol          = P.symbol lexer    
identifier      = P.identifier lexer    
reserved        = P.reserved lexer    
reservedOp      = P.reservedOp lexer
integer         = P.integer lexer


-- ###################################################################
--                        FeatherweightJava parser
-- ###################################################################

pClasses :: Parser [FJClass]
pClasses = do classes <- many pClass
              return classes

pClass :: Parser FJClass
pClass = do reserved "class"
            cName <- identifier                -- class name
            reserved "extends"
            dName <- identifier                -- superclass name
            symbol "{"
            as <- many (try pAttr)             -- attributes
            c  <- pC                           -- constructor
            ms <- many pM                      -- methods
            symbol "}"
            return (Class (mkT cName) (mkT dName)
                          (seqFromList as) c
                          (seqFromList ms))

pAttr :: Parser (Ty,FJExpr)
pAttr = do ty <- identifier                    -- Attribute type
           x  <- identifier                    -- Attribute name
           semi
           return (mkT ty, Var (Ide x))

pC :: Parser FJConstructor
pC = do cName  <- identifier                   -- Constructor name
        params <- parens (commaSep pParam)     -- Parameters
        (s,as) <- braces (do reserved "super"
                             superArgs <- parens (commaSep pExpr)
                                          ; semi
                             assigns   <- pAs `sepEndBy` semi
                             return (Meth (Ide "super")
                                          (seqFromList superArgs),
                                     assigns)
                         )             -- Super call and assignments
        return (C (mkT cName) (seqFromList params) s (seqFromList as))

pM :: Parser FJMethod
pM = do rt   <- identifier                     -- Return type
        m    <- identifier                     -- Method name
        ps   <- parens (commaSep pParam)       -- Parameters
        body <- braces (do reserved "return"
                           e <- pExpr
                           semi
                           return (Return e)
                       )                       -- Return statement
        return (M (mkT rt) (Ide m) (seqFromList ps) body)

pParam :: Parser (Ty, FJExpr)
pParam = do ty <- identifier                   -- Parameter type
            v  <- identifier                   -- Parameter name
            return (mkT ty, Var (Ide v))
                 

--------------------- FeatherweightJava expressions ------------------
pExpr :: Parser FJExpr
pExpr = choice [ try pNew,
                 try pInvoke,
                 try pCast,
                 pVar ]

pVar :: Parser FJExpr
pVar = do v <- identifier
          return (Var (Ide v))

pInvoke :: Parser FJExpr
pInvoke = do obj <- pVar <|> parens pExpr
             reservedOp "."
             e <- (try pMeth) <|> pVar
             return (Invoke obj e)

pMeth :: Parser FJExpr
pMeth = do m    <- identifier
           args <- parens (commaSep pExpr)
           return (Meth (Ide m) (seqFromList args))

pNew :: Parser FJExpr
pNew = do reserved "new"
          c    <- identifier
          args <- parens (commaSep pExpr)
          return (New (mkT c) (seqFromList args))

pCast :: Parser FJExpr
pCast = do c <- parens identifier
           e <- pExpr
           return (Cast (mkT c) e)

pAs :: Parser FJExpr
pAs = do lhs <- (try pInvoke) <|> pVar
         reservedOp "="
         rhs <- pExpr
         return (Assign lhs rhs)



-- ###################################################################
--                     Exported parsing functions
-- ###################################################################

parse :: String -> [FJClass]
parse input = case Text.Parsec.parse pClasses "" input of
                Right ast -> ast
                Left err  -> error (show err)

parseExpr input = case Text.Parsec.parse pExpr "" input of
                    Right ast -> ast
                    Left err  -> error (show err)

parseFromFile :: String -> IO [FJClass]
parseFromFile filePath =
    do result <- Text.Parsec.String.parseFromFile pClasses filePath
       case result of
         Right ast -> return ast
         Left err  -> error (show err)