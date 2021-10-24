{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cospan.Structured.Models.Sir where

import Cospan.Structured (OpenStochastic, StructuredCospan (StructuredCospan, apex), composeH)
import Data.Map (Map)
import Data.These (These)
import GHC.Generics (Generic)
import Petri.Models.Sir (R, SIR (..), sirNet)
import Petri.Stochastic
  ( PetriNode,
    Stochastic (net),
    place,
    toStochastic,
    transition,
    zeroStates,
  )

openSirNet ::
  r ->
  r ->
  OpenStochastic SIR R r
openSirNet r1 r2 = StructuredCospan (sirNet r1 r2) (const [S]) (const [S, I, R])

data Rm = MortalityRate | AntibodyDecay
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

data SIRM = M' | S' | I' | R'
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

r' :: PetriNode SIRM t
r' = place R'

i' :: PetriNode SIRM t
i' = place I'

s' :: PetriNode SIRM t
s' = place S'

m' :: PetriNode SIRM t
m' = place M'

mr :: PetriNode p Rm
mr = transition MortalityRate

ad :: PetriNode p Rm
ad = transition AntibodyDecay

sirReinfectionWithMortality :: r -> r -> Stochastic SIRM Rm r
sirReinfectionWithMortality im rir = toStochastic rateFn sirrmEdges
  where
    rateFn MortalityRate = im
    rateFn AntibodyDecay = rir
    sirrmEdges =
      [ (r', ad),
        (ad, s'),
        (i', mr),
        (mr, m')
      ]

openSirReinfectionWithMortality :: r -> r -> OpenStochastic SIRM Rm r
openSirReinfectionWithMortality im rir =
  StructuredCospan
    (sirReinfectionWithMortality im rir)
    (const [S', I', R'])
    (const [S', I', R', M'])

-- >>> show . netEdgeList . apex $ gluedSir 0.1 0.1 0.1 0.1
-- "[(One,Place (These S S'),Transition (Left R_1)),(One,Place (These I I'),Transition (Left R_1)),(One,Place (These I I'),Transition (Left R_2)),(One,Place (These I I'),Transition (Right MortalityRate)),(One,Place (These R R'),Transition (Right AntibodyDecay)),(FiniteCount 2,Transition (Left R_1),Place (These I I')),(One,Transition (Left R_2),Place (These R R')),(One,Transition (Right MortalityRate),Place (That M')),(One,Transition (Right AntibodyDecay),Place (These S S'))]"
gluedSir ::
  r ->
  r ->
  r ->
  r ->
  OpenStochastic (These SIR SIRM) (Either R Rm) r
gluedSir r1 r2 im rir = composeH glue (openSirNet r1 r2) (openSirReinfectionWithMortality im rir)
  where
    glue =
      [ (S, S'),
        (I, I'),
        (R, R')
      ]

-- >>> show initialStates
-- "fromList [(That M',0),(These S S',0),(These I I',0),(These R R',0)]"
initialStates :: Num r => Map (These SIR SIRM) r
initialStates = zeroStates . net . apex $ gluedSir 0 0 0 0
