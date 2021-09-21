{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

-- | A stochastic petri net is a petri net with rate constants for every transition.  See: https://math.ucr.edu/home/baez/structured_vs_decorated/structured_vs_decorated_companions_web.pdf
module Petri.Stochastic (toStocastic, appInitial, thread) where

import Algebra.Graph.AdjacencyMap
  ( AdjacencyMap (..),
    edges,
  )
import Control.Monad.State (State, forM, gets, modify, runState)
import Data.Bifunctor (Bifunctor (bimap))
import Data.Finitary (Finitary, inhabitants)
import Data.Function ((&))
import qualified Data.Map as Map
import qualified Data.Map.Monoidal.Strict as MMap
import Data.Maybe (fromMaybe)
import Data.Monoid (Endo (..), Sum (Sum))
import qualified Data.Set as Set
import Debug.Trace (trace)
import GHC.Generics (Generic)

data PetriNode p t = Place p | Transition t
  deriving stock (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)

instance Bifunctor PetriNode where
  bimap f _ (Place p) = Place $ f p
  bimap _ f (Transition p) = Transition $ f p

data Stochastic p t r = Stochastic
  { net :: AdjacencyMap (PetriNode p t),
    rate :: t -> r
  }

-- | State used to thread' the dynamics
data PropagationState p t r = PropagationState
  { -- | The transitions seen during the traveral of the net
    computedTransitions :: Set.Set (PetriNode p t, PetriNode p t),
    -- | The composed morphism: given a `MonnoidalMap` of initial values, return a `MonnoidalMap` of final values.
    placeMorphism :: Endo (MMap.MonoidalMap p (Sum r)),
    -- |
    petriNet :: Stochastic p t r
  }

-- | Endo needs to alway be a function of the values of each place so that the net can be provided with initial values.
-- >>> let mm =  MMap.fromList [(S, 1), (I, 0), (R, 0)]
-- >>> let sEndo = fromMaybe mempty . MMap.lookup S
-- >>> let rateFn = (0.3 *)
-- >>> let go = reduceSource @Double sEndo rateFn
-- >>> go mm
-- Sum {getSum = -0.3}
reduceSource ::
  Num a =>
  (MMap.MonoidalMap p (Sum a) -> Sum a) ->
  (a -> a) ->
  (MMap.MonoidalMap p (Sum a) -> Sum a)
reduceSource smFn rateFun = kont
  where
    kont initialState = amt initialState
    amt initialState = fmap (negate . rateFun) . smFn $ initialState

-- >>> let mm =  MMap.fromList [(S, 1), (I, 0), (R, 0)]
-- >>> let sEndo = fromMaybe mempty . MMap.lookup S
-- >>> let tEndo = fromMaybe mempty . MMap.lookup I
-- >>> let rateFn = (0.3 *)
-- >>> let go = increaseTarget @Double sEndo rateFn tEndo
-- >>> go mm
-- Sum {getSum = 0.3}
increaseTarget ::
  Num a =>
  (MMap.MonoidalMap p (Sum a) -> Sum a) ->
  (a -> a) ->
  (MMap.MonoidalMap p (Sum a) -> Sum a) ->
  (MMap.MonoidalMap p (Sum a) -> Sum a)
increaseTarget sm rateFun tmFn = kont
  where
    kont initialState = (tmFn initialState <>) . amt $ initialState
    amt = fmap rateFun . sm

computeUpdates ::
  (Ord p, Num r) =>
  (t -> r) ->
  Endo (MMap.MonoidalMap p (Sum r)) ->
  PetriNode p t ->
  PetriNode p t ->
  PetriNode p t ->
  ( Endo (MMap.MonoidalMap p (Sum r)),
    Endo (MMap.MonoidalMap p (Sum r))
  )
computeUpdates rateFn (Endo initialValues) (Place source) (Transition t') (Place target) =
  let sEndo = fromMaybe mempty . MMap.lookup source . initialValues
      tEndo = fromMaybe mempty . MMap.lookup target . initialValues
      targetUpdate = MMap.singleton target . increaseTarget sEndo (rateFn t' *) tEndo
      sourceUpdate = MMap.singleton source . reduceSource sEndo (rateFn t' *)
   in (Endo sourceUpdate, Endo targetUpdate)
computeUpdates _ _ _ _ _ = (mempty, mempty)

mappEndo :: (Ord k, Semigroup v) => Endo (MMap.MonoidalMap k v) -> Endo (MMap.MonoidalMap k v)
mappEndo endo = Endo (\v -> appEndo endo v <> v)

-- | This is too difficult to reason about.  Do it all in ContT and skip all the Endo / State buisness
thread' :: (Ord t, Ord p, Num r) => PetriNode p t -> State (PropagationState p t r) (Endo (MMap.MonoidalMap p (Sum r)))
thread' s = do
  net' <- gets (adjacencyMap . net . petriNet)
  case Map.lookup s net' of
    Just transitions -> fmap mconcat <$> forM (Set.toList transitions) $
      \t ->
        case Map.lookup t net' of
          Just targets -> fmap mconcat <$> forM (Set.toList targets) $ \target -> do
            haveSeen <- gets computedTransitions
            if Set.member (s, target) haveSeen
              then pure mempty
              else do
                initialValues <- gets placeMorphism
                rateFn <- gets (rate . petriNet)
                let (sourceUpdate, targetUpdates) = computeUpdates rateFn initialValues s t target
                modify
                  ( \st ->
                      st
                        { placeMorphism = mappEndo targetUpdates <> initialValues,
                          computedTransitions = Set.singleton (s, target) <> haveSeen
                        }
                  )
                (mappEndo sourceUpdate <>) <$> thread' target
          Nothing -> pure mempty
    Nothing -> pure mempty

thread ::
  (Ord p, Ord t, Num r) =>
  p ->
  Stochastic p t r ->
  Endo (MMap.MonoidalMap p (Sum r))
thread start pn =
  let (updates, st') = flip runState (PropagationState mempty mempty pn) $ thread' (Place start)
   in Endo (\v -> appEndo updates v <> appEndo (placeMorphism st') v)

debug :: c -> String -> c
debug = flip trace

toStocastic ::
  (Ord p, Ord t) =>
  (t -> r) ->
  [(PetriNode p t, PetriNode p t)] ->
  Stochastic p t r
toStocastic rateFn netEdges = Stochastic (edges netEdges) rateFn

-- | The SIR model
data SIR = S | I | R
  deriving stock (Eq, Ord, Show, Enum, Bounded)

s :: PetriNode SIR t
s = Place S

i :: PetriNode SIR t
i = Place I

r :: PetriNode SIR t
r = Place R

data R = R_1 | R_2
  deriving stock (Eq, Ord, Show, Enum, Bounded)

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

appInitial :: forall b p. MMap.MonoidalMap p (Sum b) -> Endo (MMap.MonoidalMap p (Sum b)) -> MMap.MonoidalMap p (Sum b)
appInitial initial (Endo go) = go initial

-- | Define a SIR model given two rates
-- >>> let r_1 = 0.02
-- >>> let r_2 = 0.05
-- >>> let net = sirNet r_1 r_2
-- >>> let endos = thread S net
-- >>> appInitial @Double (MMap.fromList $ [(S, 1), (I, 0), (R, 0)]) endos
-- MonoidalMap {getMonoidalMap = fromList [(S,Sum {getSum = 1.98}),(I,Sum {getSum = 7.69024e-2}),(R,Sum {getSum = 2.8744800000000004e-2})]}
sirNet :: r -> r -> Stochastic SIR R r
sirNet r1 r2 = toStocastic rateFn sirEdges
  where
    rateFn R_1 = r1
    rateFn R_2 = r2
