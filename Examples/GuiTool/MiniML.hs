----------------------------------------------------------------------
-- |
-- Module      :  Main
-- Copyright   :  (c) 2012, Fabian Linges
-- License     :  BSD3
-- 
-- Maintainer  :  linges@cs.tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
--
-- Example tool for visualizing the derived type checker for MiniML. 
----------------------------------------------------------------------
module Main where

import GuiTool.Gui
import TypeCheckLib.Rule

import Examples.TypeSystems.MiniML
import qualified Examples.Parser.MiniML as ML
import Prelude hiding (abs, div, and, or, const)
 

-- | Runs the GuiTool for MiniML with an empty context.
-- Needs a GuiConfig to run.
main = let gc = GuiConfig { --  A list of tuples with
                            --  a rule and its name.
                            namedRules    = rules
                            --  Global context for
                            --  the type checker.
                          , globalContext = empty
                            --  Expression parser.
                          , parseString   = ML.parse
                          }
       in runGui gc


-- | MiniML typing rules.
rules :: [(String,Rule)]
rules = [ ("true", true)
        , ("false", false)
        , ("const", const)
        , ("add", add)
        , ("sub", sub)
        , ("mul", mul)
        , ("div", div)
        , ("eqi", eqi)
        , ("and", and)
        , ("or", or)
        , ("abs", abs)
        , ("fix", fix)
        , ("app", app)
        , ("cond", cond)
        , ("pair", pair)
        , ("letpoly", letpoly)
        , ("letrec", letrec)
        , ("varpoly", varpoly)
        ]