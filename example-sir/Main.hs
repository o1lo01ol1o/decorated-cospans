{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import qualified Data.Map as M
import Data.String.Here (here)
import qualified Data.Text as T
import Graphics.Vega.VegaLite (dataFromRows, dataRow)
import qualified Graphics.Vega.VegaLite as V
import qualified Knit.Report as K
import Numeric.GSL (odeSolve)
import Numeric.LinearAlgebra (Matrix, Vector, fromColumns, linspace, toColumns, toList, toRows)
import Petri.Stochastic
  ( SIR (I, R, S),
    runPetriMorphism,
    sirNet,
    toPetriMorphism,
  )

ts :: Vector Double
ts = linspace 400 (0, 1000 :: Double)

-- FD TODO will be necessary to pass map rather than monoidal map to sirMorphism
sol :: Matrix Double
sol = odeSolve sirODE [0.99, 0.01, 0] ts
  where
    sirMorphism = toPetriMorphism (sirNet (0.04 :: Double) 0.02)
    sirODE _ [s, i, r] =
      let result = runPetriMorphism sirMorphism (M.fromList [(S, s), (I, i), (R, r)])
       in [result M.! S, result M.! I, result M.! R]
    sirODE _ _ = error "Impossible."

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
    data' = fmap (makeRow . toList) . toRows . fromColumns $ ts : toColumns sol
