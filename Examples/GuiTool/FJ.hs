----------------------------------------------------------------------
-- |
-- Module      :  Main
-- Copyright   :  (c) 2012, Martin Zuber
-- License     :  BSD3
-- 
-- Maintainer  :  martin.zuber@tu-berlin.de
-- Stability   :  experimental
-- Portability :  portable
--
-- Example tool for visualizing the derived type checker for FJ.
----------------------------------------------------------------------
module Main where

import GuiTool.Gui
import TypeCheckLib.Rule

import Examples.TypeSystems.FJ
import Examples.Parser.FJ (parseExpr, FJClass)
 

-- | Runs the GuiTool for MiniML with an empty context.
-- Needs a GuiConfig to run.
main = let gc = GuiConfig { --  A list of tuples with
                            --  a rule and its name.
                            namedRules    = rules []
                            --  Global context for
                            --  the type checker.
                          , globalContext = empty
                            --  Expression parser.
                          , parseString   = parseExpr
                          }
       in runGui gc


-- | MiniML typing rules.
rules :: [FJClass] -> [(String,Rule)]
rules prg = [ ("Var", var)
            , ("Field", field prg)
            , ("New", new prg)
            , ("Invoke", invoke prg)
            , ("Cast", cast prg)
            , ("Method", method prg)
            , ("Constructor", constructor prg)
            , ("Class", fjclass prg)
            ]