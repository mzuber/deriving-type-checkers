module Examples.Parser.MiniML ( Examples.Parser.MiniML.parse,
                                Examples.Parser.MiniML.parseFromFile ) where

import TypeCheckLib.AbstractSyntax
import TypeCheckLib.AbstractSyntax.Term

import Text.Parsec
import Text.Parsec.String as PS
import Text.Parsec.Expr
import qualified Text.Parsec.Token as P
import Text.Parsec.Language


-- ###################################################################
--                       Exported parsing functions
-- ###################################################################
parse :: String -> Term
parse input = case Text.Parsec.parse expr "" input of
                Right ast -> ast
                Left err  -> error (show err)

parseFromFile :: String -> IO Term
parseFromFile filePath = do result <- PS.parseFromFile expr filePath
                            case result of
                              Right ast -> return ast
                              Left err  -> error (show err)


-- ###################################################################
--                          Mini-ML lexer
-- ###################################################################
miniMLdef = emptyDef{ P.commentStart    = "{-"
                    , P.commentEnd      = "-}"
                    , P.identStart      = letter
                    , P.identLetter     = alphaNum
                    , P.reservedOpNames = ["+", "-", "*", "/",
                                           "=", "==", "\\", "."]
                    , P.reservedNames   = ["true", "false",
                                           "if", "then", "else",
                                           "let", "letrec", "in",
                                           "fix"]
                    }

lexer  = P.makeTokenParser miniMLdef

parens          = P.parens lexer    
symbol          = P.symbol lexer
comma           = P.comma lexer
commaSep        = P.commaSep lexer
identifier      = P.identifier lexer    
reserved        = P.reserved lexer    
reservedOp      = P.reservedOp lexer
natural         = P.natural lexer



-- ###################################################################
--                           Mini-ML parser
-- ###################################################################

expr = choice [try pair,
               try fix,
               try application,
               try abstraction,
               try conditional,
               try monolet,
               try letrec,
               try infixExpr,
               constant,
               try bool,
               try var,
               parens expr]

var = do ide <- identifier
         return (Var (Ide ide))

constant = do n <- natural
              return (Const n)

bool = do b <- (symbol "true") <|> (symbol "false")
          return (Var (Ide b))

pair = do p <- parens (do e1 <- expr
                          comma
                          e2 <- expr
                          return [e1,e2])
          return (K Tuple 2 p)

abstraction = do symbol "\\"
                 v <- var
                 symbol "."
                 e <- expr
                 return (K Abs 2 [v,e])

application =  do f <- (try (parens expr)) <|> var
                  e <- expr
                  return (K App 2 [f,e])

fix = do reserved "fix"
         e <- expr
         return (K App 2 [Var (Ide "fix"), e])

conditional = do reserved "if"
                 e1 <- expr
                 reserved "then"
                 e2 <- expr
                 reserved "else"
                 e3 <- expr
                 return (K IfThenElse 3 [e1,e2,e3])

monolet = do reserved "let"
             e1 <- expr
             reservedOp "="
             e2 <- expr
             reserved "in"
             e3 <- expr
             return (K Let 3 [e1,e2,e3])

letrec = do reserved "letrec"
            e1 <- expr
            reservedOp "="
            e2 <- expr
            reserved "in"
            e3 <- expr
            return (K LetRec 3 [e1,e2,e3])


infixExpr = buildExpressionParser operators
                                  (constant <|>
                                   bool <|>
                                   var <|>
                                   (parens expr))

operators = [ [ op "*"  AssocLeft, op "/"  AssocLeft ]
            , [ op "+"  AssocLeft, op "-"  AssocLeft ]
            , [ op "==" AssocLeft ] ]
    where
      op f assoc = Infix (do reservedOp f
                             return (\x y -> K App 2 [K App 2 [Var (Ide f),
                                                               x],
                                                      y])
                         ) assoc
