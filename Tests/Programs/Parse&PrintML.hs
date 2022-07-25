module Main where

import Examples.Parser.MiniML
import Examples.Printer.MiniML
import System.Environment


main = do (fileName:_) <- getArgs
          ast <- parseFromFile fileName
          putStr (prettyMiniML ast)