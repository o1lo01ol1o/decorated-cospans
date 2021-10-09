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
-- DONE?: This will be more efficient if we lean on linear algebra and use morphisms in VectK by building a "vector field representation"
-- of the transition matrix.  This amounts to building the representation of the graph in a matrix of edges and computing rates and updates using BLAS primatives.
-- See: https://github.com/AlgebraicJulia/AlgebraicPetri.jl/blob/91535bd5aea8b8bbc3de25d1c7b55071017c1801/src/AlgebraicPetri.jl#L256-L264
-- We can do this using HMatix if we don't care about cross compilation to JS or we can maybe use massiv if we do, tbd.
module Petri.Stochastic
  ( toStochastic,
    runPetriMorphism,
    toPetriMorphism,
    foldMapNeighbors,
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
import Data.Map
import qualified Data.Map as Map
import Data.Matrix hiding (trace)
import qualified Data.Set as Set
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

-- | This is like @foldMap@ except will walk our graph and bail once everything has been seen.
foldMapNeighbors ::
  (Ord p, Ord t, Show p, Show t) =>
  AdjacencyMap (PetriNode p t) ->
  Set.Set (PetriNode p t, PetriNode p t) ->
  PetriNode p t ->
  (PetriMorphism p b -> (PetriNode p t, PetriNode p t, PetriNode p t) -> PetriMorphism p b) ->
  PetriMorphism p b
foldMapNeighbors net' seen start f =
  case Map.lookup start (adjacencyMap net') of
    Nothing -> mempty
    Just transitions -> foldMap (<> mempty) $
      for (Set.toList transitions) $
        \transition -> case Map.lookup transition (adjacencyMap net') of
          Nothing -> mempty
          Just targets -> foldMap (<> mempty) $
            for (Set.toList targets) $ \target ->
              if Set.member (start, target) seen
                then mempty
                else
                  let recurse =
                        foldMapNeighbors
                          net'
                          (Set.singleton (start, target) <> seen)
                          target
                          f
                   in f recurse (start, transition, target)

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
-- >>> let inits = (Map.fromList $ [(S, Sum 0.99), (I, Sum 0.01), (R, 0)])
-- >>> let t1 = runPetriMorphism kont inits
-- >>> let t2 = runPetriMorphism kont (t1 <> inits)
-- >>> let t3 = runPetriMorphism kont (t2 <> t1 <> inits)
-- >>> show t1
-- >>> show t2
-- >>> show t3
sirNet :: (Num r, Eq r) => r -> r -> Stochastic SIR R r
-- need to have Stochastic datatype take as field the rate function (rateFn)
-- test should pull the values required by toVectorField out
sirNet r1 r2 = toStochastic rateFn sirEdges
  where
    rateFn R_1 = r1
    rateFn R_2 = r2

-- >>> test
-- MonoidalMap {getMonoidalMap = fromList [(S,Sum {getSum = -1.9602e-4}),(I,Sum {getSum = 1.8602e-4}),(R,Sum {getSum = 1.0e-5})]}
test :: Map SIR Double
test =
  let testPetrinet = sirNet 0.02 0.05
      stochasticNet = net testPetrinet
      ratePart = rate testPetrinet
      kont = toVectorField stochasticNet ratePart
   in runPetriMorphism (PetriMorphism kont) (Map.fromList [(S, 0.99), (I, 0.01), (R, 0)])

toPetriMorphism ::
  ( Floating r,
    Finitary p,
    Finitary t,
    1 <= Cardinality p,
    1 <= Cardinality t,
    Ord p
  ) =>
  Stochastic p t r ->
  PetriMorphism p r
toPetriMorphism pn = PetriMorphism $toVectorField (net pn) (rate pn)

test2 :: Map SIR Double
test2 =
  let testPetrinet = sirNet 0.02 0.05
   in runPetriMorphism (toPetriMorphism testPetrinet) (Map.fromList [(S, 0.99), (I, 0.01), (R, 0)])

-- | Encodes if the Place (row) is an input / output of the Transition (column)
data TransitionMatrices r = TransitionMatrices
  { transitionMatricesInput :: Matrix r,
    transitionMatricesOutput :: Matrix r
  }
  deriving stock (Eq, Show, Generic)

-- | Is the Place serving as an input or output of the Transition?
registerConnection ::
  (Num r, MonadState (TransitionMatrices r) m, Finitary p, Finitary t) =>
  (PetriNode p t, PetriNode p t) ->
  m ()
registerConnection (Place source, Transition target) =
  modify
    ( \st ->
        st
          { transitionMatricesInput =
              unsafeSet
                1
                (fromIntegral $ toFinite source, fromIntegral $ toFinite target)
                . transitionMatricesInput
                $ st
          }
    )
registerConnection (Transition source, Place target) =
  modify
    ( \st ->
        st
          { transitionMatricesOutput =
              unsafeSet
                1
                ( fromIntegral $ toFinite source,
                  fromIntegral $ toFinite target
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
    Finitary t,
    1 <= Cardinality p,
    1 <= Cardinality t
  ) =>
  AdjacencyMap (PetriNode p t) ->
  TransitionMatrices r
toTransitionMatrices pn = execState go (TransitionMatrices zeros zeros)
  where
    go = mconcat <$> traverse registerConnection (edgeList pn)
    zeros = zero (fromIntegral $ toFinite @p end) (fromIntegral $ toFinite @t end)

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
    nTransitions = fromIntegral $ toFinite @t end
    -- calculate a vecotr of current rate coefficients of each transition given by rate * product of all inputs to that transition
    currentRates u =
      generate
        nTransitions
        ( \t_i ->
            let transition = fromFinite @t (fromIntegral t_i)
             in (rate' transition *) . product $
                  for (inhabitants @p) $
                    \place ->
                      let s_i = fromIntegral $ toFinite place
                          valAtS = u Map.! place
                       in valAtS ** unsafeGet s_i t_i input -- will either valAtS ^ 1 or valAtS ^ 0
        )
    -- calculate the derivative of the initial states `u` by multiplying the rates against the values of the final transition matrix
    du rates =
      Map.fromList $
        forPlaces
          ( \place -> (place,) $
              sum $
                forTransitionIdx $
                  \t_i ->
                    let s_i = (fromIntegral . toFinite $ place)
                     in rates Vector.! t_i * unsafeGet s_i t_i dt
          )
