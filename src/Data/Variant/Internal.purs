module Data.Variant.Internal
  ( FProxy(..)
  , VariantRep(..)
  , VariantCase
  , VariantFCase
  , class VariantTags, variantTags
  , class Contractable, contractWith
  , class VariantMatchCases
  , class VariantFMatchCases
  , lookup
  , lookupTag
  , lookupEq
  , lookupOrd
  , lookupLast
  , lookupFirst
  , lookupPred
  , lookupSucc
  , lookupCardinality
  , lookupFromEnum
  , lookupToEnum
  , BoundedDict
  , BoundedEnumDict
  , impossible
  , module Exports
  ) where

import Prelude

import Control.Alternative (class Alternative, empty)
import Data.List as L
import Data.Maybe (Maybe(..))
import Data.Maybe as M
import Data.Symbol (class IsSymbol, SProxy(SProxy), reflectSymbol)
import Partial.Unsafe (unsafeCrashWith)
import Prim.Row as Row
import Record.Unsafe (unsafeGet, unsafeHas) as Exports
import Type.Equality (class TypeEquals)
import Type.Row (RProxy(..), RLProxy(..)) as Exports
import Type.Row (RProxy, RLProxy(..))
import Type.Row as R

-- | Proxy for a `Functor`.
data FProxy (a ∷ Type → Type) = FProxy

newtype VariantRep a = VariantRep
  { type ∷ String
  , value ∷ a
  }

class VariantMatchCases (rl ∷ R.RowList) (vo ∷ # Type) b | rl → vo b

instance variantMatchCons
  ∷ ( VariantMatchCases rl vo' b
    , Row.Cons sym a vo' vo
    , TypeEquals k (a → b)
    )
  ⇒ VariantMatchCases (R.Cons sym k rl) vo b

instance variantMatchNil
  ∷ VariantMatchCases R.Nil () b

class VariantFMatchCases (rl ∷ R.RowList) (vo ∷ # Type) a b | rl → vo a b

instance variantFMatchCons
  ∷ ( VariantFMatchCases rl vo' a b
    , Row.Cons sym (FProxy f) vo' vo
    , TypeEquals k (f a → b)
    )
  ⇒ VariantFMatchCases (R.Cons sym k rl) vo a b

instance variantFMatchNil
  ∷ VariantFMatchCases R.Nil () a b

foreign import data VariantCase ∷ Type

foreign import data VariantFCase ∷ Type → Type

class VariantTags (rl ∷ R.RowList) where
  variantTags ∷ RLProxy rl → L.List String

instance variantTagsNil ∷ VariantTags R.Nil where
  variantTags _ = L.Nil

instance variantTagsCons ∷ (VariantTags rs, IsSymbol sym) ⇒ VariantTags (R.Cons sym a rs) where
  variantTags _ = L.Cons (reflectSymbol (SProxy ∷ SProxy sym)) (variantTags (RLProxy ∷ RLProxy rs))

-- | A specialized lookup function which bails early. Foldable's `elem`
-- | is always worst-case.
lookupTag ∷ String → L.List String → Boolean
lookupTag tag = go
  where
  go = case _ of
    t L.: ts
      | t == tag → true
      | otherwise → go ts
    L.Nil → false

lookupEq
  ∷ L.List String
  → L.List (VariantCase → VariantCase → Boolean)
  → VariantRep VariantCase
  → VariantRep VariantCase
  → Boolean
lookupEq tags eqs (VariantRep v1) (VariantRep v2)
  | v1.type == v2.type = lookup "eq" v1.type tags eqs v1.value v2.value
  | otherwise = false

lookupOrd
  ∷ L.List String
  → L.List (VariantCase → VariantCase → Ordering)
  → VariantRep VariantCase
  → VariantRep VariantCase
  → Ordering
lookupOrd tags ords (VariantRep v1) (VariantRep v2) =
  case compare v1.type v2.type of
    EQ → lookup "compare" v1.type tags ords v1.value v2.value
    cp → cp

lookup
  ∷ ∀ a
  . String
  → String
  → L.List String
  → L.List a
  → a
lookup name tag = go
  where
  go = case _, _ of
    L.Cons t ts, L.Cons f fs
      | t == tag → f
      | otherwise → go ts fs
    _, _ → impossible name

lookupLast
  ∷ ∀ a b
  . String
  → (a → b)
  → L.List String
  → L.List a
  → { type ∷ String, value ∷ b }
lookupLast name f = go
  where
  go = case _, _ of
    L.Cons t L.Nil, L.Cons x L.Nil → { type: t, value: f x }
    L.Cons _ ts, L.Cons _ xs → go ts xs
    _, _ → impossible name

lookupFirst
  ∷ ∀ a b
  . String
  → (a → b)
  → L.List String
  → L.List a
  → { type ∷ String, value ∷ b }
lookupFirst name f = go
  where
  go = case _, _ of
    L.Cons t _, L.Cons x _ → { type: t, value: f x }
    _, _ → impossible name

lookupPred
  ∷ ∀ a
  . VariantRep a
  → L.List String
  → L.List (BoundedDict a)
  → L.List (BoundedEnumDict a)
  → Maybe (VariantRep a)
lookupPred (VariantRep rep) = go1
  where
  go1 = case _, _, _ of
    L.Cons t1 ts1, L.Cons b1 bs1, L.Cons d1 ds1
      | t1 == rep.type →
          case d1.pred rep.value of
            Nothing → Nothing
            Just z  → Just $ VariantRep { type: rep.type, value: z }
      | otherwise → go2 t1 b1 d1 ts1 bs1 ds1
    _, _, _ → impossible "pred"

  go2 t1 b1 d1 = case _, _, _ of
    L.Cons t2 ts2, L.Cons b2 bs2, L.Cons d2 ds2
      | t2 == rep.type →
          case d2.pred rep.value of
            Nothing → Just $ VariantRep { type: t1, value: b1.top }
            Just z  → Just $ VariantRep { type: rep.type, value: z }
      | otherwise → go2 t2 b2 d2 ts2 bs2 ds2
    _, _, _ → impossible "pred"

lookupSucc
  ∷ ∀ a
  . VariantRep a
  → L.List String
  → L.List (BoundedDict a)
  → L.List (BoundedEnumDict a)
  → Maybe (VariantRep a)
lookupSucc (VariantRep rep) = go
  where
  go = case _, _, _ of
    L.Cons t1 ts1, L.Cons b1 bs1, L.Cons d1 ds1
      | t1 == rep.type →
          case d1.succ rep.value of
            Just z  → Just $ VariantRep { type: t1, value: z }
            Nothing → case ts1, bs1 of
              L.Cons t2 _, L.Cons b2 _ → Just $ VariantRep { type: t2, value: b2.bottom }
              _, _ → Nothing
      | otherwise → go ts1 bs1 ds1
    _, _, _ → impossible "succ"

lookupCardinality
  ∷ ∀ a
  . L.List (BoundedEnumDict a)
  → Int
lookupCardinality = go 0
  where
  go acc = case _ of
    L.Cons d ds → go (acc + d.cardinality) ds
    L.Nil → acc

lookupFromEnum
  ∷ ∀ a
  . VariantRep a
  → L.List String
  → L.List (BoundedEnumDict a)
  → Int
lookupFromEnum (VariantRep rep) = go 0
  where
  go acc = case _, _ of
    L.Cons t ts, L.Cons d ds
      | t == rep.type → acc + d.fromEnum rep.value
      | otherwise → go (acc + d.cardinality) ts ds
    _, _ → impossible "fromEnum"

lookupToEnum
  ∷ ∀ a
  . Int
  → L.List String
  → L.List (BoundedEnumDict a)
  → Maybe (VariantRep a)
lookupToEnum = go
  where
  go ix = case _, _ of
    L.Cons t ts, L.Cons d ds
      | d.cardinality > ix →
          case d.toEnum ix of
            Just a → Just $ VariantRep { type: t, value: a }
            _ → Nothing
      | otherwise → go (ix - d.cardinality) ts ds
    _, _ → Nothing

class Contractable gt lt where
  contractWith ∷ ∀ f a. Alternative f ⇒ RProxy gt → RProxy lt → String → a → f a

instance contractWithInstance
  ∷ ( R.RowToList lt ltl
    , Row.Union lt a gt
    , VariantTags ltl
    )
  ⇒ Contractable gt lt
  where
  contractWith _ _ tag a
    | lookupTag tag (variantTags (RLProxy ∷ RLProxy ltl)) = pure a
    | otherwise = empty

type BoundedDict a =
  { top ∷ a
  , bottom ∷ a
  }

type BoundedEnumDict a =
  { pred ∷ a → M.Maybe a
  , succ ∷ a → M.Maybe a
  , fromEnum ∷ a → Int
  , toEnum ∷ Int → M.Maybe a
  , cardinality ∷ Int
  }

impossible ∷ ∀ a. String → a
impossible str = unsafeCrashWith $ "Data.Variant: impossible `" <> str <> "`"
