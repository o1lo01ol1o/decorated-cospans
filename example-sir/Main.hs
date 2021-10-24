{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Cospan.Structured (toOpenPetriMorphism)
import Cospan.Structured.Models.Sir
  ( SIRM (I', M', R', S'),
    gluedSir,
    initialStates,
  )
import qualified Data.Map as M
import Data.Maybe (mapMaybe)
import Data.String.Here (here)
import qualified Data.Text as T
import Data.These (These (That, These))
import Graphics.Vega.VegaLite (dataFromRows, dataRow)
import qualified Graphics.Vega.VegaLite as V
import qualified Knit.Report as K
import Numeric.GSL (odeSolve)
import Numeric.LinearAlgebra (Matrix, Vector, fromColumns, linspace, toColumns, toList, toRows)
import Petri.Models.Sir
  ( SIR (I, R, S),
    sirNet,
  )
import Petri.Stochastic (runPetriMorphism, toPetriMorphism, zeroStates)

ts :: Vector Double
ts = linspace 400 (0, 1000 :: Double)

sirSol :: Matrix Double
sirSol = odeSolve sirODE [0.99, 0.01, 0] ts
  where
    sirMorphism = toPetriMorphism (sirNet (0.04 :: Double) 0.02)
    sirODE _ [s, i, r] =
      let result = runPetriMorphism sirMorphism (M.fromList [(S, s), (I, i), (R, r)])
       in [result M.! S, result M.! I, result M.! R]
    sirODE _ _ = error "Impossible."

openSirSol :: Matrix Double
openSirSol = odeSolve openSirODE initStates ts
  where
    openSirMorphism = toOpenPetriMorphism $ gluedSir (0.04 :: Double) 0.02 0.005 0.009
    ascKeys = fst <$> M.toAscList initialStates
    initStates =
      fmap snd . M.toAscList
        . M.update (const $ Just 0.01) (These I I')
        . M.update (const $ Just 0.99) (These S S')
        $ initialStates
    openSirODE _ sts =
      let result = runPetriMorphism openSirMorphism . M.fromList $ zip ascKeys sts
       in snd <$> M.toAscList result

templateVars :: M.Map String String
templateVars =
  M.fromList
    [ ("lang", "English"),
      ("author", "o1ol10ol1o"),
      ("pagetitle", "SIR Model")
    ]

main :: IO ()
main = do
  let template = K.FromIncludedTemplateDir "pandoc-adaptive-bootstrap-KH.html"
  pandocWriterConfig <-
    K.mkPandocWriterConfig
      template
      templateVars
      K.mindocOptionsF

  let knitConfig =
        (K.defaultKnitConfig Nothing)
          { K.outerLogPrefix = Just "SimpleExample.Main",
            K.logIf = K.logAll,
            K.pandocWriterConfig = pandocWriterConfig
          }
  resE <- K.knitHtml knitConfig makeDoc
  case resE of
    Right htmlAsText ->
      K.writeAndMakePathLT "docs/SIR_model.html" htmlAsText
    Left err -> putStrLn $ "Pandoc Error: " ++ show err

md1 :: T.Text
md1 =
  [here|
# Some example markdown

* [Markdown][MarkdownLink] is a nice way to write formatted notes with a minimum of code.

* It supports links and tables and some *styling* information.

[MarkDownLink]:<https://pandoc.org/MANUAL.html#pandocs-markdown>

|]

makeDoc :: K.KnitOne effs => K.Sem effs ()
makeDoc = K.wrapPrefix "makeDoc" $ do
  K.logLE K.Info "adding some markdown..."
  K.addMarkDown md1
  K.addMarkDown
    "## Example HVega visualization."
  _ <- K.addHvega Nothing (Just "The SIR model") sirVis
  _ <- K.addHvega Nothing (Just "The (Glued) SIRM model") openSirVis
  pure ()

-- example using HVega
sirVis :: V.VegaLite
sirVis =
  let enc =
        V.encoding
          . V.position V.X [V.PName "Time", V.PmType V.Temporal]
          . V.position V.Y [V.PName "Population", V.PmType V.Quantitative]
          . V.color [V.MName "Place", V.MmType V.Nominal]
      bkg = V.background "rgba(0, 0, 0, 0.01)"
   in V.toVegaLite
        [ bkg,
          dataRows,
          V.mark V.Line [],
          enc [],
          V.height 640,
          V.width 960,
          V.autosize [V.AFit, V.APadding, V.AResize]
        ]
  where
    makeRow [t, s, i, r] =
      dataRow [("Time", V.Number t), ("Population", V.Number s), ("Place", V.Str "S")]
        . dataRow [("Time", V.Number t), ("Population", V.Number i), ("Place", V.Str "I")]
        . dataRow [("Time", V.Number t), ("Population", V.Number r), ("Place", V.Str "R")]
    makeRow _ = error "Impossible"
    dataRows = dataFromRows [] . foldl1 (.) data' $ []
    data' = fmap (makeRow . toList) . toRows . fromColumns $ ts : toColumns sirSol

openSirVis :: V.VegaLite
openSirVis =
  let enc =
        V.encoding
          . V.position V.X [V.PName "Time", V.PmType V.Temporal]
          . V.position V.Y [V.PName "Population", V.PmType V.Quantitative]
          . V.color [V.MName "Place", V.MmType V.Nominal]
      bkg = V.background "rgba(0, 0, 0, 0.01)"
   in V.toVegaLite
        [ bkg,
          dataRows,
          V.mark V.Line [],
          enc [],
          V.height 640,
          V.width 960,
          V.autosize [V.AFit, V.APadding, V.AResize]
        ]
  where
    makeRow m =
      let t = m M.! Nothing
          i = m M.! Just (These I I')
          r = m M.! Just (These R R')
          s = m M.! Just (These S S')
          d = m M.! Just (That M')
       in dataRow [("Time", V.Number t), ("Population", V.Number s), ("Place", V.Str "Susceptible")]
            . dataRow [("Time", V.Number t), ("Population", V.Number i), ("Place", V.Str "Infected")]
            . dataRow [("Time", V.Number t), ("Population", V.Number r), ("Place", V.Str "Recoverd")]
            . dataRow [("Time", V.Number t), ("Population", V.Number d), ("Place", V.Str "Dead")]
    ascKeys = Just . fst <$> M.toAscList initialStates
    selectColumn c@(Nothing, _) = Just c
    selectColumn c@(Just (These S S'), _) = Just c
    selectColumn c@(Just (These I I'), _) = Just c
    selectColumn c@(Just (These R R'), _) = Just c
    selectColumn c@(Just (That M'), _) = Just c
    selectColumn _ = Nothing
    selectedColumns = M.toAscList . M.fromList . mapMaybe selectColumn $ zip (Nothing : ascKeys) (ts : toColumns openSirSol)
    dataRows = dataFromRows [] . foldl1 (.) data' $ []
    data' = fmap (makeRow . M.fromList . zip (fmap fst selectedColumns) . toList) . toRows . fromColumns . fmap snd $ selectedColumns
