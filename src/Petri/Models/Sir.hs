{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Petri.Models.Sir where

import Data.Map (Map)
import qualified Data.Map as Map
import GHC.Generics (Generic)
import Petri.Stochastic
  ( PetriNode,
    Stochastic,
    place,
    runPetriMorphism,
    toPetriMorphism,
    toStochastic,
    transition,
  )

-- | The SIR model
data SIR = S | I | R
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

s :: PetriNode SIR t
s = place S

i :: PetriNode SIR t
i = place I

r :: PetriNode SIR t
r = place R

data R = R_1 | R_2
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

r_1 :: PetriNode p R
r_1 = transition R_1

r_2 :: PetriNode p R
r_2 = transition R_2

sirEdges :: [(PetriNode SIR R, PetriNode SIR R)]
sirEdges =
  [ (s, r_1),
    (r_1, i),
    (r_1, i),
    (i, r_1),
    (i, r_2),
    (r_2, r)
  ]

-- | Define a SIR model given two rates
-- >>> let r_1 = 0.02
-- >>> let r_2 = 0.05
-- >>> show . netEdgeList $ sirNet r_1 r_2
-- "[(One,Place S,Transition R_1),(One,Place I,Transition R_1),(One,Place I,Transition R_2),(FiniteCount 2,Transition R_1,Place I),(One,Transition R_2,Place R)]"
sirNet :: r -> r -> Stochastic SIR R r
sirNet r1 r2 = toStochastic rateFn sirEdges
  where
    rateFn R_1 = r1
    rateFn R_2 = r2

-- >>> _test
-- fromList [(S,-0.2),(I,0.15000000000000002),(R,5.0e-2)]
_test :: Map SIR Double
_test =
  let testPetrinet = sirNet 0.02 0.05
   in runPetriMorphism (toPetriMorphism testPetrinet) (Map.fromList [(S, 10), (I, 1), (R, 0)])
