{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cospan.Models.Sir where

import Cospan ( OpenStochastic, Cospan(Cospan), composeH )
import Data.Finitary (Finitary (Cardinality))
import Data.Map (Map)
import Data.These (These)
import GHC.Generics (Generic)
import GHC.TypeNats (KnownNat, type (+), type (*))
import Petri.Models.Sir ( R, SIR(..), sirNet )
import Petri.Stochastic
    ( Stochastic,
      PetriNode,
      toStochastic,
      place,
      transition,
      zeroStates )

openSirNet ::
  r ->
  r ->
  OpenStochastic SIR R r
openSirNet r1 r2 = Cospan (sirNet r1 r2) (const [S]) (const [S, I, R])

data Rm = MortalityRate | AntibodyDecay
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving anyclass (Finitary)

data SIRM = M' | S' | I' | R'
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving anyclass (Finitary)

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
  Cospan
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

deriving anyclass instance
  ( Eq a,
    Eq b,
    Finitary a,
    Finitary b,
    KnownNat
      ( Cardinality a
          + ( Cardinality b
                + ( ( Cardinality
                        a
                    )
                      *
                      ( Cardinality
                          b
                      )
                  )
            )
      )
  ) =>
  Finitary (These a b)

-- >>> show initialStates
-- "fromList [(This S,0),(This I,0),(This R,0),(That M',0),(That S',0),(That I',0),(That R',0),(These S M',0),(These S S',0),(These S I',0),(These S R',0),(These I M',0),(These I S',0),(These I I',0),(These I R',0),(These R M',0),(These R S',0),(These R I',0),(These R R',0)]"
initialStates :: Num r => Map (These SIR SIRM) r
initialStates = zeroStates @(These SIR SIRM)
