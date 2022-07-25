{-# LANGUAGE NoMonomorphismRestriction #-}
----------------------------------------------------------------------
-- |
-- Module      :  GuiTool.RuleTree
-- Copyright   :  (c) 2012, Fabian Linges
-- License     :  BSD3
-- 
-- Maintainer  :  linges@cs.tu-berlin.de
-- Stability   :  experimental
-- Portability :  non-portable
-- 
-- Functionality for building inference trees.
----------------------------------------------------------------------
module GuiTool.RuleTree ( InfTree(..)
                        , displayInfTree 
                        , fillInfo
                        , fromRule
                        , fromJudgement
                        , fromJudgementHideCtx
                        , marginSepName
                        , sepSpace
                        , specialSym
                        , textSpace
                        ) where

import Graphics.UI.Gtk
import Graphics.Rendering.Pango.Layout

import Control.Monad
import Data.String.Utils as U
import TypeCheckLib.Rule
import Data.List as L
import Data.Char
import Text.Regex



-- | InfTree represents an inference tree with the necessary
-- information where to display each child. Each node has a box,
-- within it can be displayed.
data InfTree = InfTree { content   :: String     -- ^ Content to display
                       , name      :: String     -- ^ Name of the rule
                       , boxWidth  :: Int
                       , boxHeight :: Int
                       , textWidth :: Int
                       , textHeight:: Int
                       , textX     :: Int        -- ^ Where the content starts on the x-axis
                       , textY     :: Int        -- ^ Where the content starts on the y-axis
                       , boxX      :: Int        -- ^ Where the box starts on the x-axis
                       , boxY      :: Int        -- ^ Where the box starts on the y-axis
                       , children  :: [InfTree]  -- ^ Children of the node
                       , invisible :: [InfTree]  -- ^ Invisible children of the node
                       , context   :: Context     
                       } deriving (Show, Eq)

-- | Generates InfTree from a Rule and a Name                         
fromRule :: Rule -> String -> InfTree
fromRule (Rule ps c) n = defaultTree { content = pprint c
                                     , name = n
                                     , children = map fromJudgement ps
                                     }


-- | Remove newlines
formatStr =  replace "\n" " " .  removeMultiSpace

-- | Replace 'Gamma' identifier with corresponding symbol.
replaceGamma = replace "Gamma" "Г"

-- |  Insert/replace special symbols  
specialSym = replaceGamma . replace "|- " "\x22A2\xa0\&" .
             replace "$" "τ" . replace "-&gt;" "→" . indicesMarkup 

-- | markup for indices 
indicesMarkup s = subRegex reg (escapeMarkup s) ("\\1<sub>\\2</sub>\\3")
    where 
      pat = "([[:alpha:]$]+)([[:digit:]]+)([[:space:],)]|$)"  
      reg = mkRegexWithOpts pat True True
  


-- | Removes multiply spaces and replaces them with one space
removeMultiSpace (' ':' ': xs) = removeMultiSpace (' ' : xs)
removeMultiSpace (x:xs) = x : removeMultiSpace xs
removeMultiSpace [] = []


-- TODO: 'fromJudgement' and 'fromJudgementHideCtx' could be merged
-- into one function by using a flag to determine if non-empty
-- contexts should be hidden or not.

-- | Generate InfTree from a Judgement
fromJudgement :: Judgement -> InfTree                          
fromJudgement j = defaultTree{ content = pprint j
                             , context = getContext j
                             }


-- | Generate InfTree from a Judgement but hide all non-empty contexts
fromJudgementHideCtx :: Judgement -> InfTree                          
fromJudgementHideCtx j = defaultTree{ content = pprint j'
                                    , context = ctx
                                    }
    where
      ctx = getContext j
            
      -- TODO: Quick and dirty, this should be done better.
      j' = if ctx /= empty then setCtx (MCtx "Gamma") j else j

      setCtx ctx (J _ e ty) = J ctx e ty
      setCtx _   c          = c


-- | Sets the default label style for displaying in a InfTree 
setLabelStyle l = widgetModifyFg l StateNormal (Color 0 0 45000)


-- | Select the context of a judgement.
getContext (J c _ _) = c
getContext _ = empty


-- | Renders an InfTree to a given GTKLayout and displays Infomartions
-- on a given label via events.  Displays invisble children
-- (i.e. constrains) in a tooltip.
displayInfTree layt label t = do
    rule <- labelNew Nothing 
    rname <- labelNew  Nothing
    m1 <- labelNew  $ Just ">" 
    m2 <- labelNew  $ Just "<" 
    m3 <- labelNew  $ Just "|" 
    labelSetMarkup rule (specialSym $ formatStr $ content t)
    labelSetMarkup rname (name t)
    eb <- eventBoxNew --evenBox wrapps name
    sep <- hSeparatorNew
    setLabelStyle rule 
    setLabelStyle m1 
    setLabelStyle m2
    setLabelStyle m3
    setLabelStyle rname 
    when (not (invisible t == [])) $
         set rname [widgetTooltipMarkup := (Just $ specialSym $ tipContent t)] 
    containerAdd eb rname
    onButtonPress eb showInfo
    eventBoxSetVisibleWindow eb False
    widgetSetSizeRequest rule (textWidth t) (textHeight t)
    layoutPut layt rule (textX t) (textY t) 
    widgetSetSizeRequest sep sepWidth 1 
    when (l > 0 || li > 0) $ layoutPut layt sep sepX sepY 
    when (l > 0 || li > 0) $ layoutPut layt eb nameX nameY 
    when (l > 0) $ mapM_ (displayInfTree layt label) (children t)
    (f,_) <- textSpace (name t)
    --layoutPut layt m1 (boxX t) (boxY t)
    --layoutPut layt m2 (boxX t + boxWidth t) (boxY t)
    --layoutPut layt m3 (sepX  + boxWidth t) (boxY t)
    return () 
        where
          sepWidth = max (xr - xl) $ textWidth t 
          sepY = textY t - (sepSpace * (3 `div` 2))
          sepX = if (xr - xl) < textWidth t then textX t else xl 
          l = length (children t)
          li = length (invisible t)
          ch' = children t
          xl = min (textXlch) (textX t) -- first child start or own start
          xr = max (textXrch) (textX t + textWidth t) -- last child end
          nameY = boxY t - (textHeight t `div` 2) 
          nameX = xl + sepWidth + marginSepName
          showInfo = \ e -> do labelSetMarkup label $ specialSym (infoText t)
                               return True
          textXlch = if null ch' then textX t else textX $ head ch'
          textXrch = if null ch' then textX t + textWidth t
                     else (textX $ last ch') + (textWidth $ last ch')


infoText t = "Context:\n" ++ pprint (context t) ++ "\n\n" ++ "Constraints:\n" ++ tipContent t
tipContent t = L.intercalate "\n" $ map content (invisible t)

-- | Set the fields in an InfTree with the necessary information like
-- postions and dimensiones.
fillInfo t = do t' <- fillWidthInfo t
                let t'' = fillTextXY $ fillBoxX (fillBoxY t') 0
                return t''
                 
-- | Set the fields textX and textY in an InfTree 
fillTextXY t@(InfTree{children = []}) = t{textY = y, textX = x}
    where
      xMid = boxX t + (boxWidth t `div` 2)  
      x    = xMid - (textWidth t `div` 2)
      yMid = boxY t + (boxHeight t `div` 2)  
      y    = yMid - (textHeight t `div` 2)

fillTextXY t@(InfTree{children = ch}) = t{children = ch', textX = x, textY = y}
    where
      ch'  = map fillTextXY ch
      xl   = textX $ head ch'
      xr   = (textX $ last ch') + (textWidth $ last ch')
      xMid = ((xr-xl) `div` 2) + xl 
      x    = xMid - (textWidth t `div` 2)
      yMid = boxY t + (boxHeight t `div` 2)  
      y    = yMid - (textHeight t `div` 2)

-- | Set the field boxX in an InfTree 
fillBoxX t x = let c  = foldl f ([], x) (children t)
                   c' = fst c
                   f  = \ (l,o) z -> let k = fillBoxX z o 
                                         w = boxWidth k
                                     in (l ++ [k], o + w) 
                  in t { boxX = x, children = c' }


-- | Set the field boxY in an InfTree 
fillBoxY t = let mx = (maxDepth t 0) + textHeight t 
                 ch = map (f mx) (children t) 
                 f  = \ m c -> let --should be boxHeight of the child,
                                   --doesnt matter here, all are the
                                   --same
                                   c' = map (f (m - boxHeight c)) (children c) 
                               in c { children = c', boxY = m }
              in if ch == [] then t { boxY = textHeight t }
                 else t { boxY = mx + boxHeight t, children = ch } --shifst if mx is 0 
            

-- | Gets the max depth of an InfTree
maxDepth :: InfTree -> Int -> Int
maxDepth (InfTree{children = []}) x = 0  
maxDepth t x = max x' x
    where
      x' = foldl (\ a b-> max a (maxDepth b (x+(boxHeight t)))) 0 (children t)


-- | Sets the fields textWidth, textHeight, boxHeight and boxWidth in an InfTree.
fillWidthInfo :: InfTree -> IO InfTree
fillWidthInfo t@(InfTree {children = []}) =
    do (textWs,textHs) <- textSpace (content t) 
       (textWn,textHn) <- textSpace (name t) 
       let newWidth = textWs + textWn + marginSepName + constantSpacing
       return $ t { boxWidth   = newWidth
                  , textWidth  = textWs
                  , boxHeight  = textHs + sepSpace
                  , textHeight = textHs
                  }

fillWidthInfo t = do
    (textWs,textHs) <- textSpace (content t) 
    (textWn,textHn) <- textSpace (name t)
    newC            <- mapM fillWidthInfo  (children t)
    let c = children t
        newWidth      = (max textWs childrenWidth) + textWn
        childrenWidth = (foldl f 0 newC) 
        addWidth      = textWs + textWn + marginSepName -
                        childrenWidth + constantSpacing
        newC'         = if childrenWidth > (textWs) then newC 
                        else  map (adjustWidth (addWidth `div` (length c))) newC
        f = (\ x y -> x + (boxWidth y))
    return $ t { children   =  newC'
               , boxWidth   = newWidth
               , textWidth  = textWs
               , boxHeight  = textHs + sepSpace
               , textHeight = textHs
               } 

-- | Adjust the BoxWith of a node and all his children with a given value.
adjustWidth :: Int -> InfTree -> InfTree
adjustWidth 0 t =  t
adjustWidth add t@(InfTree {boxWidth =w , children = []}) = t { boxWidth = w + add }
adjustWidth add t@(InfTree {boxWidth =w , children = c})  = t { boxWidth = w + add
                                                              , children = newC
                                                              } 
    where
      newC = map (adjustWidth (add `div` (length c)))  c


-- | Returns the text width and height of string.
-- Result depends on the GTK font settings of the user.
textSpace s = do  l <- labelNew Nothing  
                  labelSetMarkup l $ specialSym $ formatStr s 
                  p <- labelGetLayout l
                  (_,(Rectangle _ _ x _)) <- layoutGetPixelExtents p
                  --workaround, use same height for every text 
                  l <- labelNew Nothing  
                  labelSetMarkup l "T<sub>123</sub>"
                  p <- labelGetLayout l
                  (_,(Rectangle _ _ _ y)) <- layoutGetPixelExtents p
                  return (x,y)


-- | Space for seperators between a node and its child.
sepSpace :: Int
sepSpace = 6

-- | Space between the seperator line and the name of the rule.
marginSepName = 6

-- | Every node gets this spacing added to its width.
constantSpacing :: Int
constantSpacing = 40 

-- | Default InfTree with no information.
defaultTree = InfTree { content    = ""
                      , name       = ""
                      , boxWidth   = 0
                      , boxHeight  = 0
                      , textWidth  = 0
                      , textHeight = 0
                      , boxX       = -1
                      , boxY       = -1
                      , textX      = -1
                      , textY      = -1
                      , children   = []
                      , invisible  = []
                      , context    = empty
                      }
