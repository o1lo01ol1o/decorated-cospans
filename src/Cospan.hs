{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Cospan where

import Algebra.Graph.Labelled.AdjacencyMap (AdjacencyMap, gmap, overlay)
import Data.Biapplicative (Bifunctor)
import Data.Bifunctor (Bifunctor (bimap, first))
import Data.Finitary (Finitary (Cardinality))
import Data.List (nub)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.These (These (..))
import GHC.Generics (Generic)
import GHC.TypeNats (type (<=))
import Petri.Stochastic (PetriMorphism, PetriNode, Stochastic (Stochastic), toPetriMorphism)

-- | A Cospan `x` is just the apex x and
-- functions to pick out the inputs and outputs at the boundary of `x`
data Cospan x y z = Cospan
  { -- | The apex object x
    apex :: x,
    -- | The input leg
    input :: x -> y,
    -- | The output leg
    output :: x -> z
  }
  deriving stock (Generic)

-- | An OpenStochastic net is a petri net with two "legs" that form its inputs and outputs.
type OpenStochastic p t r = Cospan (Stochastic p t r) [p] [p]

toOpenPetriMorphism ::
  ( Floating r,
    Finitary p,
    Finitary t,
    Ord p,
    1 <= Cardinality p,
    1 <= Cardinality t
  ) =>
  OpenStochastic p t r ->
  PetriMorphism p r
toOpenPetriMorphism = toPetriMorphism . apex

-- | Merge places given two maps of places that should be merge and the union of Either place.
mergePlaces :: (Ord p', Ord p) => Map p p' -> Map p' p -> Either p p' -> These p p'
mergePlaces mp _ (Left p) =
  case Map.lookup p mp of
    Nothing -> This p
    Just p' -> These p p'
mergePlaces _ mp' (Right p') =
  case Map.lookup p' mp' of
    Nothing -> That p'
    Just p -> These p p'

gmapBimap ::
  (Bifunctor p, Monoid e, Ord (p a c), Ord (p b d), Eq e) =>
  (a -> b) ->
  (c -> d) ->
  AdjacencyMap e (p a c) ->
  AdjacencyMap e (p b d)
gmapBimap f g = gmap (bimap f g)

legPushforward ::
  (Eq p, Eq p') =>
  (Either p p' -> These p p') ->
  Stochastic p t r ->
  Stochastic p' t' r ->
  (Stochastic p t r -> [p]) ->
  (Stochastic p' t' r -> [p']) ->
  (Stochastic (These p p') (Either t t') r -> [These p p'])
legPushforward merge' xL xR legL legR = const pushforward
  where
    legL' = Left <$> legL xL
    legR' = Right <$> legR xR
    pushforward = nub $ (merge' <$> legL') <> (merge' <$> legR')

-- | take the coproduct of two AdjacencyMaps by glueing the nodes and transitions with Either.
composeNetV ::
  ( Monoid e,
    Ord (p (Either a1 b1) (Either a2 b2)),
    Eq e,
    Bifunctor p,
    Ord (p a1 a2),
    Ord (p b1 b2)
  ) =>
  AdjacencyMap e (p a1 a2) ->
  AdjacencyMap e (p b1 b2) ->
  AdjacencyMap e (p (Either a1 b1) (Either a2 b2))
composeNetV netL netR = overlay netL' netR'
  where
    netL' = gmapBimap Left Left netL
    netR' = gmapBimap Right Right netR

ratePushforward :: (t1 -> p) -> (t2 -> p) -> Either t1 t2 -> p
ratePushforward rateL rateR = \case
  Right t -> rateR t
  Left t -> rateL t

-- | Vertical composition.  This simply "stacks" two nets on one another where nodes and transitions will be either from one
-- or from the other and neither will new edges be created nor will places be merged.
composeV ::
  (Ord p, Ord p', Ord t, Ord t') =>
  OpenStochastic p t r ->
  OpenStochastic p' t' r ->
  OpenStochastic (Either p p') (Either t t') r
composeV (Cospan apeL iL oL) (Cospan apeR iR oR) = Cospan (Stochastic netC rateC) iC oC
  where
    (Stochastic netL rateL) = apeL
    (Stochastic netR rateR) = apeR
    netC = composeNetV netL netR
    rateC = ratePushforward rateL rateR
    iR' = Right <$> iR apeR
    oR' = Right <$> oR apeR
    iL' = Left <$> iL apeL
    oL' = Left <$> oL apeL
    iC _ = iR' <> iL'
    oC _ = oR' <> oL'

-- | Horizontal composition of OpenStochastic petri nets. The resuting net is glued together using `Either` for transitions
-- and `These` for places since some places will be "merged" when legs are composed.
composeH ::
  forall p t p' t' r.
  (Ord p, Ord p', Ord t, Ord t') =>
  -- | The list of places that should be merged:  Since places are different types here, we need to know which pairs should "plugged" together in a composition.  Most likely these will be pairs of input / output places.
  [(p, p')] ->
  -- | The left
  OpenStochastic p t r ->
  -- | The right
  OpenStochastic p' t' r ->
  OpenStochastic (These p p') (Either t t') r
composeH toMerge (Cospan apeL iL oL) (Cospan apeR iR oR) = pushforward
  where
    (Stochastic netL rateL) = apeL
    (Stochastic netR rateR) = apeR
    mp = Map.fromList toMerge
    mp' = Map.fromList $ fmap (\(a, b) -> (b, a)) toMerge
    mergePlaces' = mergePlaces mp mp'
    netPushForward = gmap @_ @_ @(PetriNode (These p p') (Either t t')) (first mergePlaces') (composeNetV netL netR)
    rateC = ratePushforward rateL rateR
    iPushForward = legPushforward mergePlaces' apeL apeR iL iR
    oPushForward = legPushforward mergePlaces' apeL apeR oL oR
    pushforward = Cospan (Stochastic netPushForward rateC) iPushForward oPushForward