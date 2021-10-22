{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
  )
where

import Algebra.Graph.Labelled (Graph, edgeList, edges)
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
import GHC.Generics (Generic)
import GHC.Num (Natural)
import GHC.TypeNats (type (<=))

-- | Nodes in the graph will either be Places or Transitions
data PetriNode p t = Place p | Transition t
  deriving stock (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

instance Bifunctor PetriNode where
  bimap f _ (Place p) = Place $ f p
  bimap _ f (Transition p) = Transition $ f p

-- | We only represent single edges in the Graph data structure but Petri nets may have multiple edges between nodes
-- so we annotate the edge with a monoidal label that can tell us how many edges we deal with between a pair of vertices.
data FiniteCount a = Zero | One | FiniteCount a
  deriving stock (Eq, Ord, Functor, Show)

getFiniteCount :: Num p => FiniteCount p -> p
getFiniteCount Zero = 0
getFiniteCount One = 1
getFiniteCount (FiniteCount c) = c

_isZero :: FiniteCount a -> Bool
_isZero Zero = True
_isZero _ = False

instance Num a => Semigroup (FiniteCount a) where
  Zero <> x = x
  x <> Zero = x
  One <> One = FiniteCount 2
  One <> (FiniteCount c) = FiniteCount (c + 1)
  (FiniteCount c) <> One = FiniteCount (c + 1)
  (FiniteCount a) <> (FiniteCount b) = FiniteCount (a + b)

instance Num a => Monoid (FiniteCount a) where
  mempty = Zero
  mappend = (<>)

-- TODO:  It may in some cases also be defined by multiple edges between two nodes. Dunno what semanticcs are required here.
data Stochastic p t r = Stochastic
  { net :: Graph (FiniteCount Natural) (PetriNode p t),
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

for :: Functor f => f a -> (a -> b) -> f b
for = flip fmap

toStochastic ::
  (t -> r) ->
  [(PetriNode p t, PetriNode p t)] ->
  Stochastic p t r
toStochastic rateFn specdEdges = Stochastic (edges netEdges) rateFn
  where
    netEdges = fmap (\(src, target) -> (One, src, target)) specdEdges

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
    (r_1, i),
    (i, r_1),
    (i, r_2),
    (r_2, r)
  ]

-- | Define a SIR model given two rates
-- >>> let r_1 = 0.02
-- >>> let r_2 = 0.05
-- >>> show . edgeList . net $ sirNet r_1 r_2
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

toPetriMorphism ::
  ( Floating r,
    Finitary p,
    Finitary t,
    Ord t,
    Ord p,
    1 <= Cardinality p,
    1 <= Cardinality t
  ) =>
  Stochastic p t r ->
  PetriMorphism p r
toPetriMorphism pn = PetriMorphism $ toVectorField (net pn) (rate pn)

-- | Encodes if the Place (row) is an input / output of the Transition (column)
data TransitionMatrices r = TransitionMatrices
  { transitionMatricesInput :: Matrix r,
    transitionMatricesOutput :: Matrix r
  }
  deriving stock (Eq, Show, Generic)

-- | unsafeSet using 0-indexed semantics
unsafeSetZeroIndexed :: a -> (Int, Int) -> Matrix a -> Matrix a
unsafeSetZeroIndexed v (a, b) = unsafeSet v (a + 1, b + 1)

toFiniteNum :: forall i a. (Finitary i, Num a) => i -> a
toFiniteNum = fromIntegral . toFinite

-- | Is the Place serving as an input or output of the Transition?
registerConnection ::
  (Num r, MonadState (TransitionMatrices r) m, Finitary p, Finitary t) =>
  (FiniteCount Natural, PetriNode p t, PetriNode p t) ->
  m ()
registerConnection (count, Place source, Transition target) =
  modify
    ( \st ->
        st
          { transitionMatricesInput =
              unsafeSetZeroIndexed
                (fromIntegral $ getFiniteCount count)
                ( toFiniteNum source,
                  toFiniteNum target
                )
                . transitionMatricesInput
                $ st
          }
    )
registerConnection (count, Transition source, Place target) =
  modify
    ( \st ->
        st
          { transitionMatricesOutput =
              unsafeSetZeroIndexed
                (fromIntegral $ getFiniteCount count)
                ( toFiniteNum target,
                  toFiniteNum source
                )
                . transitionMatricesOutput
                $ st
          }
    )
registerConnection _ = error "Invalid edge: places must alternate with transitions!" -- TODO: use throwM or expose safe API functions

toTransitionMatrices ::
  forall r p t.
  ( Num r,
    Finitary p,
    Ord p,
    Ord t,
    Finitary t,
    1 <= Cardinality p,
    1 <= Cardinality t
  ) =>
  Graph (FiniteCount Natural) (PetriNode p t) ->
  TransitionMatrices r
toTransitionMatrices pn = execState go (TransitionMatrices zeros zeros)
  where
    go = mconcat <$> traverse registerConnection (edgeList pn)
    zeros = zero ((1 +) $ toFiniteNum @p end) ((1 +) $ toFiniteNum @t end)

-- | Converts 0 indexed values to 1 indexed values and then calles unsafeGet
unsafeGetZeroIndexed :: Int -> Int -> Matrix a -> a
unsafeGetZeroIndexed a b = unsafeGet (a + 1) (b + 1)

-- | Yield a function that calculates the vectorfield of a StochasticNet with initial conditions at some time `t` for the given the network
-- and rate function.  We use `Map`s here only for convience.
-- See https://en.wikipedia.org/wiki/Petri_net#Formulation_in_terms_of_vectors_and_matrices
-- and https://arxiv.org/abs/1704.02051 for details.
-- This implmentation is not optimized for performance though it uses @Vector@ under the hood.  We care
-- more about portability at the momement and so use a pure Haskell implementation over using
-- BLAS in `HMatrix`, `hasktorch`, or massiv.
toVectorField ::
  forall r p t.
  ( Floating r,
    Finitary p,
    Finitary t,
    Ord t,
    1 <= Cardinality p,
    1 <= Cardinality t,
    Ord p
  ) =>
  Graph (FiniteCount Natural) (PetriNode p t) ->
  (t -> r) ->
  (Map p r -> Map p r)
toVectorField pn rate' = fun
  where
    fun = du . currentRates
    -- auxiliary helpers
    (TransitionMatrices input output) = toTransitionMatrices pn
    dt = output - input
    forPlaces = for (inhabitants @p)
    forTransitions = for (inhabitants @t)
    toIdx f = f . (fromIntegral . toFinite)
    forTransitionIdx = forTransitions . toIdx
    nTransitions = (1 +) . fromIntegral $ toFinite @t end
    -- calculate a vecotr of current rate coefficients of each transition given by rate * product of all inputs to that transition
    currentRates u = rateVec
      where
        !rateVec =
          generate
            nTransitions
            ( \t_i ->
                let transition = fromFinite @t (fromIntegral t_i)
                 in (rate' transition *) . product $
                      for (inhabitants @p) $
                        \place ->
                          let s_i = fromIntegral $ toFinite place
                              valAtS = u Map.! place
                           in valAtS ** unsafeGetZeroIndexed s_i t_i input -- will either valAtS ^ 1 or valAtS ^ 0
            )

    -- calculate the derivative of the initial states `u` by multiplying the rates against the values of the final transition matrix
    du rates = m
      where
        !m =
          Map.fromList $
            forPlaces
              ( \place -> (place,) $
                  sum $
                    forTransitionIdx $
                      \t_i ->
                        let !s_i = (fromIntegral . toFinite $ place)
                         in (rates Vector.! t_i) * unsafeGetZeroIndexed s_i t_i dt
              )
