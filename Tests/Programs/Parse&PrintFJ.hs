module Main where

import Examples.Parser.FJ
import Examples.Printer.FJ
import System.Environment


main = do (fileName:_) <- getArgs
          ast <- parseFromFile fileName
          putStr (prettyFJ ast)