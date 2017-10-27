module Data.Variant.Internal
  ( FProxy(..)
  , VariantRep(..)
  , VariantCase
  , VariantFCase
  , class VariantTags, variantTags
  , class Contractable, contractWith
  , class VariantMatchCases
  , class VariantFMatchCases
  , lookupTag
  , lookupEq
  , lookupOrd
  , lookup
  , lookup'
  , BoundedDict
  , BoundedEnumDict
  , fromJust
  , module Exports
  ) where

import Prelude
import Control.Alternative (class Alternative, empty)
import Data.List as L
import Data.Maybe as M
import Data.Symbol (class IsSymbol, SProxy(SProxy), reflectSymbol)
import Data.Record.Unsafe (unsafeGet, unsafeHas) as Exports
import Partial.Unsafe (unsafeCrashWith)
import Type.Equality (class TypeEquals)
import Type.Row as R
import Type.Row (RProxy, RLProxy(..))
import Type.Row (RProxy(..), RLProxy(..)) as Exports

-- | Proxy for a `Functor`.
data FProxy (a ∷ Type → Type) = FProxy

newtype VariantRep a = VariantRep
  { type ∷ String
  , value ∷ a
  }

class VariantMatchCases (rl ∷ R.RowList) (vo ∷ # Type) b | rl → vo b

instance variantMatchCons
  ∷ ( VariantMatchCases rl vo' b
    , RowCons sym a vo' vo
    , TypeEquals k (a → b)
    )
  ⇒ VariantMatchCases (R.Cons sym k rl) vo b

instance variantMatchNil
  ∷ VariantMatchCases R.Nil () b

class VariantFMatchCases (rl ∷ R.RowList) (vo ∷ # Type) a b | rl → vo a b

instance variantFMatchCons
  ∷ ( VariantFMatchCases rl vo' a b
    , RowCons sym (FProxy f) vo' vo
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
lookup name tag tags as = fromJust name $ lookup' tag tags as

fromJust
  ∷ ∀ a
  . String
  → M.Maybe a
  → a
fromJust name = case _ of
  M.Just a → a
  _ → unsafeCrashWith $ "Data.Variant: impossible `" <> name <> "`"

lookup'
  ∷ ∀ a
  . String
  → L.List String
  → L.List a
  → M.Maybe a
lookup' tag = go
  where
  go = case _, _ of
    L.Cons t ts, L.Cons f fs
      | t == tag → M.Just f
      | otherwise → go ts fs
    _, _ → M.Nothing

class Contractable gt lt where
  contractWith ∷ ∀ f a. Alternative f ⇒ RProxy gt → RProxy lt → String → a → f a

instance contractWithInstance
  ∷ ( R.RowToList lt ltl
    , Union lt a gt
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
