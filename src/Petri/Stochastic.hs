{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
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

-- | A stochastic petri net is a petri net with rate constants for every transition.  See: https://math.ucr.edu/home/baez/structured_vs_decorated/structured_vs_decorated_companions_web.pdf
module Petri.Stochastic
  ( toStochastic,
    runPetriMorphism,
    toPetriMorphism,
    toVectorField,
    FiniteCount,
    PetriNode,
    PetriMorphism,
    Stochastic (..),
    place,
    netEdgeList,
    transition,
    zeroStates,
  )
where

import Algebra.Graph.Labelled.AdjacencyMap (AdjacencyMap, edges, vertexSet)
import qualified Algebra.Graph.Labelled.AdjacencyMap as AM
import Control.Monad.State.Strict (MonadState, execState, modify)
import Data.Bifunctor (Bifunctor (bimap))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Matrix (Matrix, unsafeGet, unsafeSet, zero)
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import Data.Vector (generate)
import qualified Data.Vector as Vector
import GHC.Generics (Generic)
import GHC.Num (Natural)

-- | Nodes in the graph will either be Places or Transitions
data PetriNode p t = Place p | Transition t
  deriving stock (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

place :: p -> PetriNode p t
place = Place

transition :: t -> PetriNode p t
transition = Transition

instance Bifunctor PetriNode where
  bimap f _ (Place p) = Place $ f p
  bimap _ f (Transition p) = Transition $ f p

zeroStates :: (Num r, Ord p) => AdjacencyMap e (PetriNode p t) -> Map p r
zeroStates = Map.fromList . fmap (,0) . getPlaces

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
  { net :: AdjacencyMap (FiniteCount Natural) (PetriNode p t),
    rate :: t -> r
  }

netEdgeList ::
  Stochastic p t r ->
  [(FiniteCount Natural, PetriNode p t, PetriNode p t)]
netEdgeList = AM.edgeList . net

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
  (Ord p, Ord t) =>
  (t -> r) ->
  [(PetriNode p t, PetriNode p t)] ->
  Stochastic p t r
toStochastic rateFn specdEdges = Stochastic (edges netEdges) rateFn
  where
    netEdges = fmap (\(src, target) -> (One, src, target)) specdEdges

toPetriMorphism ::
  ( Floating r,
    Ord p,
    Ord t
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

-- | Is the Place serving as an input or output of the Transition?
registerConnection ::
  (Num r, Ord p, Ord t, MonadState (TransitionMatrices r) m) =>
  (Map p Int, Map t Int) ->
  (FiniteCount Natural, PetriNode p t, PetriNode p t) ->
  m ()
registerConnection (p2i, t2i) (count, Place source, Transition target) =
  modify
    ( \st ->
        st
          { transitionMatricesInput =
              unsafeSetZeroIndexed
                (fromIntegral $ getFiniteCount count)
                ( p2i Map.! source,
                  t2i Map.! target
                )
                . transitionMatricesInput
                $ st
          }
    )
registerConnection (p2i, t2i) (count, Transition source, Place target) =
  modify
    ( \st ->
        st
          { transitionMatricesOutput =
              unsafeSetZeroIndexed
                (fromIntegral $ getFiniteCount count)
                ( p2i Map.! target,
                  t2i Map.! source
                )
                . transitionMatricesOutput
                $ st
          }
    )
registerConnection _ _ = error "Invalid edge: places must alternate with transitions!" -- TODO: use throwM or expose safe API functions

justTransitions :: PetriNode p a -> Maybe a
justTransitions (Transition t) = Just t
justTransitions _ = Nothing

justPlaces :: PetriNode a t -> Maybe a
justPlaces (Place p) = Just p
justPlaces _ = Nothing

getTransitions :: AdjacencyMap (FiniteCount Natural) (PetriNode p t) -> [t]
getTransitions = getNode justTransitions

getPlaces :: AdjacencyMap e (PetriNode b t) -> [b]
getPlaces = getNode justPlaces

getNode :: (a -> Maybe b) -> AdjacencyMap e a -> [b]
getNode f = mapMaybe f . Set.toList . vertexSet

switchMap :: Map a Int -> Map Int a
switchMap = Map.fromList . fmap (\(a, b) -> (b, a)) . Map.toList

idxMap :: Ord k => [k] -> Map k Int
idxMap i = Map.fromList $ zip i [0 :: Int ..]

idxMaps :: Ord a => [a] -> (Map a Int, Map Int a)
idxMaps i = (a, b)
  where
    a = idxMap i
    b = switchMap a

toTransitionMatrices ::
  forall r p t.
  (Num r, Ord t, Ord p) =>
  (Map p Int, Map t Int) ->
  AdjacencyMap (FiniteCount Natural) (PetriNode p t) ->
  TransitionMatrices r
toTransitionMatrices maps pn = execState go (TransitionMatrices zeros zeros)
  where
    go = mconcat <$> traverse (registerConnection maps) (AM.edgeList pn)
    ts = getTransitions pn
    ns = getPlaces pn
    zeros = zero (length ns) (length ts)

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
-- TODO: lots of little efficienciey improvements in the function construction.  We needlessly switch between the index representation and the Sum type representation in places
toVectorField ::
  forall r p t.
  ( Floating r,
    Ord p,
    Ord t
  ) =>
  AdjacencyMap (FiniteCount Natural) (PetriNode p t) ->
  (t -> r) ->
  (Map p r -> Map p r)
toVectorField pn rate' = fun
  where
    fun = du . currentRates
    -- auxiliary helpers
    (TransitionMatrices input output) = toTransitionMatrices (placeToIdx, transitionToIdx) pn
    dt = output - input
    allPlaces = getPlaces pn
    allTransitions = getTransitions pn
    forPlaces = for allPlaces
    (placeToIdx, _) = idxMaps allPlaces
    (transitionToIdx, idxToTransition) = idxMaps allTransitions
    nTransitions = length allTransitions
    -- calculate a vecotr of current rate coefficients of each transition given by rate * product of all inputs to that transition
    currentRates u = rateVec
      where
        !rateVec =
          generate
            nTransitions
            ( \t_i ->
                let transition = idxToTransition Map.! t_i
                 in (rate' transition *) . product $
                      for allPlaces $
                        \place ->
                          let s_i = placeToIdx Map.! place
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
                    for allTransitions $
                      \transition ->
                        let !t_i = transitionToIdx Map.! transition
                            !s_i = placeToIdx Map.! place
                         in (rates Vector.! t_i) * unsafeGetZeroIndexed s_i t_i dt
              )
