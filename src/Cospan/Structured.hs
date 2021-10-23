{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Cospan.Structured where

import Algebra.Graph.Labelled.AdjacencyMap (AdjacencyMap, gmap, overlay)
import Data.Biapplicative (Bifunctor)
import Data.Bifunctor (Bifunctor (bimap, first))
import Data.Finitary (Finitary (Cardinality))
import Data.List (nub)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.These (These (..))
import GHC.Generics (Generic)
import GHC.Num (Natural)
import GHC.TypeNats (type (<=))
import Petri.Stochastic (FiniteCount, PetriMorphism, PetriNode, Stochastic (Stochastic, net, rate), toPetriMorphism)

-- | A StructuredCospan `x` is just the apex x and
-- functions to pick out the inputs and outputs at the boundary of `x`
data StructuredCospan x y z = StructuredCospan
  { -- | The apex object x
    apex :: x,
    -- | The input leg
    input :: x -> y,
    -- | The output leg
    output :: x -> z
  }
  deriving stock (Generic)

-- | An OpenStochastic net is a petri net with two "legs" that form its inputs and outputs.
type OpenStochastic p t r = StructuredCospan (Stochastic p t r) [p] [p]

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

-- | Caclulate the pushforward by using the provided function to map from Either to These.
legPushforward' ::
  (Eq p, Eq p') =>
  (Either p p' -> These p p') ->
  Stochastic p t r ->
  Stochastic p' t' r ->
  (Stochastic p t r -> [p]) ->
  (Stochastic p' t' r -> [p']) ->
  (Stochastic (These p p') (Either t t') r -> [These p p'])
legPushforward' merge' xL xR legL legR = const pushforward
  where
    legL' = Left <$> legL xL
    legR' = Right <$> legR xR
    pushforward = nub $ (merge' <$> legL') <> (merge' <$> legR')

-- | take the coproduct of two AdjacencyMaps by glueing the nodes and transitions with Either.
composeNetV' ::
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
composeNetV' netL netR = overlay netL' netR'
  where
    netL' = gmapBimap Left Left netL
    netR' = gmapBimap Right Right netR

composeNetV ::
  (Ord a1, Ord b1, Ord a2, Ord b2) =>
  StructuredCospan (Stochastic a1 a2 r1) y1 z1 ->
  StructuredCospan (Stochastic b1 b2 r2) y2 z2 ->
  AdjacencyMap
    (FiniteCount Natural)
    (PetriNode (Either a1 b1) (Either a2 b2))
composeNetV l r = composeNetV' (net (apex l)) (net (apex r))

ratePushforward' :: (t1 -> p) -> (t2 -> p) -> Either t1 t2 -> p
ratePushforward' rateL rateR = \case
  Right t -> rateR t
  Left t -> rateL t

ratePushforward ::
  StructuredCospan (Stochastic p1 t1 p2) y1 z1 ->
  StructuredCospan (Stochastic p3 t2 p2) y2 z2 ->
  Either t1 t2 ->
  p2
ratePushforward l r = ratePushforward' (rate (apex l)) (rate (apex r))

composeInputLegV ::
  OpenStochastic p t r ->
  OpenStochastic p' t' r ->
  [Either p p']
composeInputLegV l r = (Right <$> input r (apex r)) <> (Left <$> input l (apex l))

composeOutputLegV ::
  OpenStochastic p t r ->
  OpenStochastic p' t' r ->
  [Either p p']
composeOutputLegV l r = (Right <$> output r (apex r)) <> (Left <$> output l (apex l))

-- | Vertical composition.  This simply "stacks" two nets on one another where nodes and transitions will be either from one
-- or from the other and neither will new edges be created nor will places be merged.
composeV ::
  (Ord p, Ord p', Ord t, Ord t') =>
  OpenStochastic p t r ->
  OpenStochastic p' t' r ->
  OpenStochastic (Either p p') (Either t t') r
composeV l r = StructuredCospan (Stochastic netC rateC) iC oC
  where
    netC = composeNetV l r
    rateC = ratePushforward l r
    iC _ = composeInputLegV l r
    oC _ = composeOutputLegV l r

inputLegPushforward ::
  (Eq p, Eq p') =>
  (Either p p' -> These p p') ->
  StructuredCospan (Stochastic p t r) [p] z1 ->
  StructuredCospan (Stochastic p' t' r) [p'] z2 ->
  Stochastic (These p p') (Either t t') r ->
  [These p p']
inputLegPushforward f l r = legPushforward' f (apex l) (apex r) (input l) (input r)

outputLegPushforward ::
  (Eq p, Eq p') =>
  (Either p p' -> These p p') ->
  StructuredCospan (Stochastic p t r) y1 [p] ->
  StructuredCospan (Stochastic p' t' r) y2 [p'] ->
  Stochastic (These p p') (Either t t') r ->
  [These p p']
outputLegPushforward f l r = legPushforward' f (apex l) (apex r) (output l) (output r)

-- | Horizontal composition of OpenStochastic petri nets. The resuting net is glued together using `Either` for transitions
-- and `These` for places since some places will be "merged" when legs are composed.
-- Any places in the in the list of merge nodes that are not in the legs will be disregarded.
composeH ::
  forall p t p' t' r.
  (Ord p, Ord p', Ord t, Ord t') =>
  -- | The list of places that should be merged.
  [(p, p')] ->
  -- | The left
  OpenStochastic p t r ->
  -- | The right
  OpenStochastic p' t' r ->
  OpenStochastic (These p p') (Either t t') r
composeH toMerge l@(StructuredCospan apeL _ oL) r@(StructuredCospan apeR iR _) = StructuredCospan (Stochastic netPushForward rateC) iPushForward oPushForward
  where
    mergeSet = Set.fromList toMerge
    toMerge' = filter (`Set.member` mergeSet) $ zip (oL apeL) (iR apeR)
    mp = Map.fromList toMerge
    mp' = Map.fromList $ fmap (\(a, b) -> (b, a)) toMerge'
    howToMergePlaces = mergePlaces mp mp'
    netPushForward = gmap @_ @_ @(PetriNode (These p p') (Either t t')) (first howToMergePlaces) (composeNetV l r) -- Not certain that gmap will do the right thing when keys suddenly end up the same (need to mappendd the value)
    rateC = ratePushforward l r
    iPushForward = inputLegPushforward howToMergePlaces l r
    oPushForward = outputLegPushforward howToMergePlaces l r
