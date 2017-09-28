module Data.Variant.Internal
  ( FProxy(..)
  , VariantCase
  , class VariantTags, variantTags
  , class Contractable, contractWith
  , class VariantMatchCases
  , class VariantFMatchCases
  , lookupTag
  , lookupEq
  , lookupOrd
  , lookup
  , module Exports
  ) where

import Prelude
import Control.Alternative (class Alternative, empty)
import Data.List as L
import Data.Symbol (class IsSymbol, SProxy(SProxy), reflectSymbol)
import Data.Tuple (Tuple(..))
import Data.Record.Unsafe (unsafeGet, unsafeHas) as Exports
import Partial.Unsafe (unsafeCrashWith)
import Type.Equality (class TypeEquals)
import Type.Row as R
import Type.Row (RProxy, RLProxy(..))
import Type.Row (RProxy(..), RLProxy(..)) as Exports

-- | Proxy for a `Functor`.
data FProxy (a ∷ Type → Type) = FProxy

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
  → Tuple String VariantCase
  → Tuple String VariantCase
  → Boolean
lookupEq tags eqs (Tuple t1 c1) (Tuple t2 c2)
  | t1 == t2  = lookup "eq" t1 tags eqs c1 c2
  | otherwise = false

lookupOrd
  ∷ L.List String
  → L.List (VariantCase → VariantCase → Ordering)
  → Tuple String VariantCase
  → Tuple String VariantCase
  → Ordering
lookupOrd tags ords (Tuple t1 c1) (Tuple t2 c2) =
  case compare t1 t2 of
    EQ → lookup "compare" t1 tags ords c1 c2
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
      | t == tag  → f
      | otherwise → go ts fs
    _, _ →
      unsafeCrashWith $ "Data.Variant: impossible `" <> name <> "`"

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
