{-# LANGUAGE ExistentialQuantification, DoAndIfThenElse #-}
----------------------------------------------------------------------
-- |
-- Module      :  GuiTool.Gui
-- Copyright   :  (c) 2012, Fabian Linges
-- License     :  BSD3
-- 
-- Maintainer  :  linges@cs.tu-berlin.de
-- Stability   :  experimental
-- Portability :  non-portable
-- 
-- This modules provides functionality to generate a gui-based tool
-- allowing the user to inspect and trace type type checkers derived
-- woth the help of the library.
----------------------------------------------------------------------
module GuiTool.Gui ( runGui
                   , GuiConfig (..)
                   ) where

import Graphics.UI.Gtk

import GuiTool.RuleTree

import TypeCheckLib.AbstractSyntax
import TypeCheckLib.AbstractSyntax.Term
import TypeCheckLib.Type
import TypeCheckLib.Rule
import TypeCheckLib.TypeChecker as TC hiding (and, or)
import TypeCheckLib.ConstraintGeneration
import TypeCheckLib.Substitution hiding (empty, app) 
import TypeCheckLib.ConstraintSolving as CS

import Prelude as P hiding (abs, div, and, or, const)
import Data.Typeable
import Data.Maybe
import Data.Tree
import Data.String.Utils
import qualified Data.List as L
import qualified Data.Map as M



-- | Collects everything that is needed to work on the GUI
-- Should only be used internally 
data Global a = PrettyPrint a =>
                Global { rules           :: [(String,Rule)]
                       , gcontext        :: Context
                       , ruleScroll      :: ScrolledWindow
                       , solverScroll    :: ScrolledWindow
                       , ruleVBox        :: VBox
                       , typeTextEntry   :: Entry
                       , solverViewport  :: Viewport
                       , typeAlign       :: Alignment
                       , showAllButton   :: Button
                       , typeLabelRight  :: Label
                       , typeLabelLeft   :: Label
                       , enterButton     :: Button
                       , fileChooser     :: FileChooserButton
                       , window          :: Window
                       , parse           :: String -> a 
                       }

-- | Configuration for the Gui
data GuiConfig a = PrettyPrint a => 
                   GuiConfig { -- | List of rules and with their coresponding name
                               namedRules    :: [(String,Rule)]
                               -- | Initial context for constraint solving
                             , globalContext :: Context
                               -- | Expression parser
                             , parseString   ::  String -> a
                             }
                            
-- | Starts the GTK Gui, needs a GuiConfig 
runGui gc = do
   initGUI
   g <- initGlobal gc 
   entrySetActivatesDefault (typeTextEntry g) True
   onClicked (enterButton g) (enterEvent g) 
   onCurrentFolderChanged (fileChooser g) (fileSelector g) 
   buildRuleView g
   standardInfo g
   onDestroy (window g) mainQuit
   widgetShowAll (window g)
   mainGUI

-- | Fills the global config 
initGlobal gc = do
    builder <- builderNew
    builderAddFromFile builder "gui.glade" 
    window        <- builderGetObject builder castToWindow mainWinID
    vbox          <- builderGetObject builder castToVBox ruleVBoxLayoutID
    scroll        <- builderGetObject builder castToScrolledWindow ruleScrollTreeID
    showAllButton <- builderGetObject builder castToButton ruleShowAllID 
    svp           <- builderGetObject builder castToViewport solverViewportID 
    rightLabel    <- builderGetObject builder castToLabel typeLabelRightID 
    leftLabel     <- builderGetObject builder castToLabel typeLabelLeftID 
    tvamain       <- builderGetObject builder castToAlignment typeViewMainID 
    solverScroll  <- builderGetObject builder castToScrolledWindow solverScrollID
    entry         <- builderGetObject builder castToEntry typeViewEntryID 
    enter         <- builderGetObject builder castToButton typeViewEnterID 
    fileChooserButton <- builderGetObject builder castToFileChooserButton typeViewFileID     
    return Global { 
             rules          = namedRules gc,
             gcontext       = globalContext gc,
             typeTextEntry  = entry,
             solverViewport = svp, 
             typeAlign      = tvamain,
             ruleScroll     = scroll,
             solverScroll   = solverScroll,
             ruleVBox       = vbox,
             showAllButton  = showAllButton,
             typeLabelRight = rightLabel,
             typeLabelLeft  = leftLabel,
             enterButton    = enter,
             fileChooser    = fileChooserButton,
             window         = window, 
             parse          = parseString gc}


-- ###################################################################
--                           Type View
-- ###################################################################

-- | Displays the global context in the type view
standardInfo g = let s = "Global Context:\n" ++ pprint (gcontext g)
                 in labelSetText (typeLabelLeft g) s

-- | Event handler for clicking the "Enter" button
enterEvent g = do s <-entryGetText (typeTextEntry g) 
                  renderTypeAndSolverView g s


-- | Renders InferenceTree in Typeview
-- and Steps in Solverview.
-- Gets the String which represends the term.
renderTypeAndSolverView g s = do
    let term = (parse g) s 
        (con,tree,tv) = evalTypeCheckM $ do 
                                tv <- freshTV
                                let j = J (gcontext g) term tv
                                (c,t) <- genCsScan (map snd $ rules g) j False 
                                return (c,t,tv)
        result = solveCsScan con
    labelSetText (typeLabelRight g) ""
    xs' <- labelListFromIRes $ fst  result 
    xs  <- addResultToLabel xs' (snd result) tv s
    let cs = map unsolv $ fst result
    buildStepView g cs xs 0 
    l <- generateInf (treeToSplitInf tree g) g
    clearContainer (typeAlign g) 
    containerAdd (typeAlign g) l
    widgetShowAll (typeAlign g)


-- | Adds the final result of the constrain solving at the end of the step through.
addResultToLabel xs result tv s = do 
    let xs'= init xs
        r  = case result of
               CS.Success o     -> pprintTy (o .@. tv)
               CS.NoRuleFound j -> "No matching rule found for:\n" ++ pprint j
               CS.Failure (C c) -> mkMsg (err c)
               CS.Error msg     -> msg
    text <- labelGetLabel (last xs)
    l<- labelNew Nothing
    labelSetMarkup l $ strip text ++ "\n\n\n" ++ (specialSym $ strip s ++ " :: "  ++  r)
    return (xs' ++ [l])    


-- TODO Error Handling, Filename with non ascci symbols
-- | Event handler for fileSelector. Reads file content, and
-- passes the content to renderTypeAndSolverView.
fileSelector g = do
    file <- fileChooserGetFilename (fileChooser g) 
    case file of
      Just fpath -> do -- putStrLn fpath
                       --print $ filePath (fileFromURI fpath)
                       s <- readFile fpath
                       renderTypeAndSolverView g s
                       return ()
      Nothing -> return () 


-- ###################################################################
--                              Solver View
-- ###################################################################

-- | Builds a list of labels from a  list of IntermediateResults.
labelListFromIRes l = mapM labelFromIRes l

-- | Build Infolabel from intermediate result from solving constraints 
labelFromIRes ir = let s1 =  showCon (con ir) ++ "Result: " ++ ppResult (res ir) 
                       s2 =  case res ir of
                                CS.Success o -> if o == subs ir then ""
                                                else "\nSubstitutions:\n"
                                                     ++ ppSub (subs ir)
                                _            -> ""
                   in do l <- labelNew Nothing
                         labelSetMarkup l $ specialSym $ s1 ++ s2 
                         return l


-- | Distinguish between real content and helper infos.
showable (Sep n) = False
showable _       = True  

showCon c = if showable c
            then "Current constraint: " ++ pprint c ++ "\n"
            else ""

-- | Build Gui to step through interintermediate results
buildStepView g cons list n =
    do let x = list !! n
           c = cons !! n
       sv <- solverListview $ filter showable c
       clearContainer (solverScroll g) 
       containerAdd (solverScroll g) sv
       widgetShowAll (solverScroll g)
       clearContainer (solverViewport g) 
       vbox  <- vBoxNew False 0
       hbox  <- hBoxNew False 0
       next  <- buttonNewWithLabel "Next"
       back  <- buttonNewWithLabel "Back"
       containerAdd (solverViewport g) vbox
       boxPackStart vbox x PackNatural 5
       boxPackEnd vbox hbox PackNatural 5
       boxPackEnd hbox next PackNatural 5
       boxPackEnd hbox back PackNatural 5
       if (n+2) > length list
       then widgetSetSensitive next False
       else do onClicked next $ clearContainer vbox >>
                                buildStepView g cons list (n+1)
               return ()
       if n < 1
       then widgetSetSensitive back False
       else do onClicked back $ clearContainer vbox >>
                                buildStepView g cons list (n-1)
               return ()
       widgetShowAll (solverViewport g)
       return ()

-- | Pretty print Results
ppResult (CS.Success sub)   = "Success \n" ++ ppSub sub 
ppResult (CS.Failure j)     = "Failure " ++ pprint j    
ppResult (CS.NoRuleFound j) = "Found no Rule for " ++ pprint j    
ppResult r                  =  show r   

ppSub s = concatMap printS (M.elems s)
printS (S m) = L.intercalate "\n" s  
    where
      s = L.map (\ (k,v) -> pprintTy k ++ " = " ++ pprintTy v) (M.toList m)

-- | Pretty Print if a is Type "Ty"
-- else just show a.
-- cast is necessary because substitutions are heterogenous.   
pprintTy a = case (cast a) :: Maybe Ty of
               Just t  -> pprint t
               Nothing -> show a

-- | Show constraints as list in solver view
solverListview c = do 
    model   <- listStoreNew c 
    view    <- treeViewNewWithModel model
    col     <- treeViewColumnNew
    treeViewColumnSetTitle col "Constraints"
    renderer <- cellRendererTextNew
    cellLayoutPackStart col renderer True
    cellLayoutSetAttributes col renderer model $
                            \row -> [ cellTextMarkup := Just $ specialSym $ pprint row]
    treeViewAppendColumn view col
    return view


-- ###################################################################
--                              Rule View
-- ###################################################################

-- | Builds Rule View
buildRuleView g = do 
    view <- ruleListview  g
    containerAdd (ruleScroll g) view
    onClicked (showAllButton g) (showAllRules g)

-- | Generates layout with one rule displayed
generateRule t = do
    tree <- fillInfo t
    let w = boxWidth tree + marginSepName 
        h = boxY tree + boxHeight tree  + sepSpace 
    layt <- layoutNew Nothing Nothing     
    layoutSetSize layt w h 
    dummy <- labelNew Nothing 
    widgetSetSizeRequest layt w h 
    --layoutPut layt mark2 (x) (30) 
    widgetModifyBg layt StateNormal backgroundColor
    displayInfTree layt dummy tree
    return layt

-- | Generates Inference Tree and displays it on the type view.
generateInf t g = do
    tree <- fillInfo t 
    let w = boxWidth tree + marginSepName 
        h = boxY tree + boxHeight tree + sepSpace 
    layt <- layoutNew Nothing Nothing     
    layoutSetSize layt w h 
    widgetSetSizeRequest layt w h  
    widgetModifyBg layt StateNormal backgroundColor 
    displayInfTree layt (typeLabelRight g) tree
    widgetShowAll layt 
    return layt

-- | Show all rules in rule view.
showAllRules g = do clearContainer $ ruleVBox g 
                    mapM_ f (tyFromRules $ rules g)
    where
      f a = do layTree <- generateRule a
               align <- alignmentNew 0.5 0.5 0 0
               containerAdd align layTree
               boxPackStart (ruleVBox g) align PackNatural 10 
               widgetShowAll (ruleVBox g)  
                 
-- | Shows one rule from selection in rule view.
showRule g treesel = do
    clearContainer $ ruleVBox g 
    sel <- treeSelectionGetSelectedRows treesel
    let s = head  (head sel)
        v = (tyFromRules $ rules g) !! s
    layTree <- generateRule v 
    boxPackStart (ruleVBox g) layTree PackNatural 0 
    widgetShowAll (ruleVBox g) 
 
-- | Clears a GTK container of all children
clearContainer c = do widlist <- containerGetChildren c 
                      mapM (containerRemove c) widlist

-- | Shows rules as List in ruleview
ruleListview g = do 
    model <- listStoreNew (tyFromRules $ rules g) 
    view <- treeViewNewWithModel model
    col <- treeViewColumnNew
    treeViewColumnSetTitle col "Rules"
    renderer <- cellRendererTextNew
    cellLayoutPackStart col renderer True
    cellLayoutSetAttributes col renderer model $ \row -> [ cellText := name row ]
    treeViewAppendColumn view col
    treeSel <- treeViewGetSelection view
    treeSelectionSetMode treeSel  SelectionSingle
    onSelectionChanged treeSel (showRule g treeSel)
    let longest = foldl (\ s a -> if (length s) > (length $ fst a) then s else fst a)
                  "" (rules g) 
        l = length (rules g)
    (x,y) <- textSpace longest 
    widgetSetSizeRequest view (x+20) (y*l)
    return view


-- ###################################################################
--                                Misc
-- ###################################################################

tyFromRules = map (\ (n,r)-> fromRule r n)

-- | Builds InfTree from a Tree 
treeToInf (Node (j,r) l) g = ty {children = c, name = n}
    where
      ty = fromJudgement j
      c  = map (\x-> treeToInf x g) l 
      n  = if isJust r
           then getRuleName (fromJust r) (rules g)
           else ""

-- | Build InfTree but split constraints and judgements. 
-- Contraints are not visible in normal InfTree
treeToSplitInf (Node (j,r) l) g =
    ty {children = c, name = n, invisible = i}
        where
          ty = fromJudgementHideCtx j
          js = filter isJTree l
          cs = filter (P.not . isJTree) l 
          c  = map (\x-> treeToSplitInf x g) js 
          i  = map (\x-> treeToSplitInf x g) cs
          n  = if isJust r
               then getRuleName (fromJust r) (rules g)
               else ""

isJTree (Node (j,r) l) = isJ j

-- | Search for Name of a rule in Tuple list
getRuleName r (x:xs) = if r == snd x then fst x
                       else getRuleName r xs
getRuleName _ [] = "none"

backgroundColor = Color 65535 65535 65535

ruleHboxID       = "rule-hbox"
mainWinID        = "window1"
ruleScrollTreeID = "rule-scroll"
ruleLayoutID     = "rule-layout"
ruleShowAllID    = "rule-showall"
ruleVBoxLayoutID = "rule-vbox-layout"
solverScrollID   = "solver-constraints-scroll" 
solverViewportID = "solver-viewport" 
typeLabelRightID = "type-label-right" 
typeLabelLeftID  = "type-label-left" 
typeViewFileID   = "type-view-file"
typeViewEntryID  = "type-view-entry" 
typeViewEnterID  = "type-view-enter-button" 
typeViewMainID   = "type-view-main-alignment"
