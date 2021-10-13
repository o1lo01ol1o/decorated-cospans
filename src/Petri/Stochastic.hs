{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | A stochastic petri net is a petri net with rate constants for every transition.  See: https://math.ucr.edu/home/baez/structured_vs_decorated/structured_vs_decorated_companions_web.pdf
module Petri.Stochastic
  ( toStochastic,
    runPetriMorphism,
    toPetriMorphism,
    toVectorField,
    sirNet,
    SIR (..),
    debug,
  )
where

import Algebra.Graph.AdjacencyMap
  ( AdjacencyMap (..),
    edgeList,
    edges,
  )
import Control.Monad.State.Strict (MonadState, execState, modify)
import Data.Bifunctor (Bifunctor (bimap))
import Data.Finitary
  ( Finitary (Cardinality, end, fromFinite, toFinite),
    inhabitants,
  )
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Matrix (Matrix, unsafeGet, unsafeSet, zero)
import Data.Vector (generate)
import qualified Data.Vector as Vector
import Debug.Trace (trace)
import GHC.Generics (Generic)
import GHC.TypeNats (type (<=))

-- | Nodes in the graph will either be Places or Transitions
data PetriNode p t = Place p | Transition t
  deriving stock (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

instance Bifunctor PetriNode where
  bimap f _ (Place p) = Place $ f p
  bimap _ f (Transition p) = Transition $ f p

-- TODO:  It may in some cases also be defined by multiple edges between two nodes. Dunno what semanticcs are required here.
data Stochastic p t r = Stochastic
  { net :: AdjacencyMap (PetriNode p t),
    rate :: t -> r
  }

newtype PetriMorphism p r = PetriMorphism
  { unPetriMorphism ::
      Map p r ->
      Map p r
  }
  deriving stock (Generic)
  deriving newtype (Monoid, Semigroup)

-- | Run a PetriMorphism with some initial values.  Note that we only combine the updates after the whole graph is composed.
runPetriMorphism :: PetriMorphism p b -> Map p b -> Map p b
runPetriMorphism (PetriMorphism endo) = endo

for :: [a] -> (a -> b) -> [b]
for = flip fmap

-- | Debug prints
debug :: c -> String -> c
debug = flip trace

toStochastic ::
  (Ord p, Ord t) =>
  (t -> r) ->
  [(PetriNode p t, PetriNode p t)] ->
  Stochastic p t r
toStochastic rateFn netEdges = Stochastic (edges netEdges) rateFn

-- | The SIR model
data SIR = S | I | R
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving anyclass (Finitary)

s :: PetriNode SIR t
s = Place S

i :: PetriNode SIR t
i = Place I

r :: PetriNode SIR t
r = Place R

data R = R_1 | R_2
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving anyclass (Finitary)

r_1 :: PetriNode p R
r_1 = Transition R_1

r_2 :: PetriNode p R
r_2 = Transition R_2

sirEdges :: [(PetriNode SIR R, PetriNode SIR R)]
sirEdges =
  [ (s, r_1),
    (r_1, i),
    (i, r_1),
    (i, r_2),
    (r_2, r)
  ]

-- | Define a SIR model given two rates
-- >>> let r_1 = 0.02
-- >>> let r_2 = 0.05
-- >>> let kont = toPetriMorphism $sirNet r_1 r_2
-- >>> let inits = (Map.fromList $ [(S, 0.99), (I, 0.01), (R, 0)])
-- >>> let t1 = runPetriMorphism kont inits
-- >>> let t2 = runPetriMorphism kont (t1 <> inits)
-- >>> let t3 = runPetriMorphism kont (t2 <> t1 <> inits)
-- >>> show t1
-- >>> show t2
-- >>> show t3
sirNet :: r -> r -> Stochastic SIR R r
sirNet r1 r2 = toStochastic rateFn sirEdges
  where
    rateFn R_1 = r1
    rateFn R_2 = r2

-- >>> _test
_test :: Map SIR Double
_test =
  let testPetrinet = sirNet 0.02 0.05
      stochasticNet = net testPetrinet
      ratePart = rate testPetrinet
      kont = toVectorField stochasticNet ratePart
   in runPetriMorphism (PetriMorphism kont) (Map.fromList [(S, 0.99), (I, 0.01), (R, 0)])

toPetriMorphism ::
  ( Floating r,
    Finitary p,
    Finitary t,
    Show r,
    Show t,
    Show p,
    1 <= Cardinality p,
    1 <= Cardinality t,
    Ord p
  ) =>
  Stochastic p t r ->
  PetriMorphism p r
toPetriMorphism pn = PetriMorphism $ toVectorField (net pn) (rate pn)

_test2 :: Map SIR Double
_test2 =
  let testPetrinet = sirNet 0.02 0.05
   in runPetriMorphism (toPetriMorphism testPetrinet) (Map.fromList [(S, 0.99), (I, 0.01), (R, 0)])

-- | Encodes if the Place (row) is an input / output of the Transition (column)
data TransitionMatrices r = TransitionMatrices
  { transitionMatricesInput :: Matrix r,
    transitionMatricesOutput :: Matrix r
  }
  deriving stock (Eq, Show, Generic)

unsafeSet' :: a -> (Int, Int) -> Matrix a -> Matrix a
unsafeSet' v (a, b) = unsafeSet v (a + 1, b + 1)

-- | Is the Place serving as an input or output of the Transition?
registerConnection ::
  (Num r, Show p, Show t, MonadState (TransitionMatrices r) m, Finitary p, Finitary t) =>
  (PetriNode p t, PetriNode p t) ->
  m ()
registerConnection (Place source, Transition target) =
  modify
    ( \st ->
        st
          { transitionMatricesInput =
              unsafeSet'
                1
                (fromIntegral $ toFinite source, fromIntegral $ toFinite target)
                . transitionMatricesInput
                $ st
          }
    )
    `debug` show ("registerConnection: (Place source, Transition target)" <> show source <> " " <> show target)
registerConnection (Transition source, Place target) =
  modify
    ( \st ->
        st
          { transitionMatricesOutput =
              unsafeSet'
                1
                ( fromIntegral $ toFinite target,
                  fromIntegral $ toFinite source
                )
                . transitionMatricesOutput
                $ st
          }
    )
    `debug` show ("registerConnection: (Transition source, Place target)" <> show source <> " " <> show target)
registerConnection _ = error "Invalid edge: places must alternate with transitions!" -- TODO: use throwM or expose safe API functions

toTransitionMatrices ::
  forall r p t.
  ( Num r,
    Finitary p,
    Show p,
    Show t,
    Show r,
    Finitary t,
    1 <= Cardinality p,
    1 <= Cardinality t
  ) =>
  AdjacencyMap (PetriNode p t) ->
  TransitionMatrices r
toTransitionMatrices pn = execState go (TransitionMatrices zeros zeros) `debug` ("toTransitionMatrices: " <> show zeros)
  where
    go = mconcat <$> traverse registerConnection (edgeList pn)
    zeros = zero ((1 +) . fromIntegral $ toFinite @p end) ((1 +) . fromIntegral $ toFinite @t end)

-- | Converts 0 indexed values to 1 indexed values and then calles unsafeGet
unsafeGet' :: Int -> Int -> Matrix a -> a
unsafeGet' a b = unsafeGet (a + 1) (b + 1)

-- | Yield a function that calculates the vectorfield of a StochasticNet with initial conditions at some time `t` for the given the network
-- and rate function.  We use `Map`s here only for convience.
-- See https://en.wikipedia.org/wiki/Petri_net#Formulation_in_terms_of_vectors_and_matrices
-- and https://arxiv.org/abs/1704.02051 for details.
-- This implmentation is not optimized for performance though it uses @Vector@ under the hood.  We care
-- more about portability at the momement and so use a pure Haskell implementation over using
-- BLAS in `HMatrix`, `hasktorch`, or massiv.
-- >>> fromIntegral . toFinite <$> inhabitants @SIR
toVectorField ::
  forall r p t.
  ( Floating r,
    Show r,
    Finitary p,
    Finitary t,
    Show t,
    Show p,
    1 <= Cardinality p,
    1 <= Cardinality t,
    Ord p
  ) =>
  AdjacencyMap (PetriNode p t) ->
  (t -> r) ->
  (Map p r -> Map p r)
toVectorField pn rate' = du . currentRates
  where
    -- auxiliary helpers
    (TransitionMatrices input output) = toTransitionMatrices pn
    dt = output - input
    forPlaces = for (inhabitants @p)
    forTransitions = for (inhabitants @t)
    toIdx f = f . (fromIntegral . toFinite)
    forTransitionIdx = forTransitions . toIdx
    nTransitions = (1 +) . fromIntegral $ toFinite @t end
    -- calculate a vecotr of current rate coefficients of each transition given by rate * product of all inputs to that transition
    currentRates u =
      generate
        nTransitions
        ( \t_i ->
            let transition = fromFinite @t (fromIntegral t_i) `debug` show (fromFinite @t (fromIntegral t_i))
             in (rate' transition *) . product $
                  for (inhabitants @p) $
                    \place ->
                      let s_i = fromIntegral $ toFinite place `debug` show (place, transition, u)
                          valAtS = u Map.! place `debug` show (s_i, t_i, input)
                       in valAtS ** unsafeGet' s_i t_i input `debug` show (unsafeGet' s_i t_i input) -- will either valAtS ^ 1 or valAtS ^ 0
        )
    -- calculate the derivative of the initial states `u` by multiplying the rates against the values of the final transition matrix
    du rates =
      Map.fromList $
        forPlaces
          ( \place -> (place,) $
              sum $
                forTransitionIdx $
                  \t_i ->
                    let s_i = (fromIntegral . toFinite $ place) `debug` ("du rates: t_i " <> show t_i)
                     in case rates Vector.!? t_i of
                          Nothing -> error $ "case rates " <> show t_i
                          Just r' -> r' * unsafeGet' s_i t_i dt `debug` ("du rates place: " <> show place)
          )
