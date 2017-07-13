module Data.Variant.Internal
  ( LProxy(..)
  , VariantCase
  , class VariantTags
  , variantTags
  , lookupEq
  , lookupOrd
  ) where

import Prelude
import Data.List as L
import Data.Symbol (SProxy(..), class IsSymbol, reflectSymbol)
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafeCrashWith)
import Type.Row as R

data LProxy (rl ∷ R.RowList) = LProxy

foreign import data VariantCase ∷ Type

class VariantTags (rl ∷ R.RowList) where
  variantTags ∷ LProxy rl → L.List String

instance variantTagsNil ∷ VariantTags R.Nil where
  variantTags _ = L.Nil

instance variantTagsCons ∷ (VariantTags rs, IsSymbol sym) ⇒ VariantTags (R.Cons sym a rs) where
  variantTags _ = L.Cons (reflectSymbol (SProxy ∷ SProxy sym)) (variantTags (LProxy ∷ LProxy rs))

lookupEq
  ∷ ∀ r
  . L.List String
  → L.List (VariantCase → VariantCase → Boolean)
  → Tuple String VariantCase
  → Tuple String VariantCase
  → Boolean
lookupEq tags eqs (Tuple t1 c1) (Tuple t2 c2) =
  if t1 == t2
    then go tags eqs
    else false
  where
  go = case _, _ of
    L.Cons t ts, L.Cons e es →
      if t == t1
        then e c1 c2
        else go ts es
    _, _ → unsafeCrashWith "Data.Variant: impossible eq"

lookupOrd
  ∷ ∀ r
  . L.List String
  → L.List (VariantCase → VariantCase → Ordering)
  → Tuple String VariantCase
  → Tuple String VariantCase
  → Ordering
lookupOrd tags ords (Tuple t1 c1) (Tuple t2 c2) =
  case compare t1 t2 of
    EQ → go tags ords
    cp → cp
  where
  go = case _, _ of
    L.Cons t ts, L.Cons c cs →
      if t == t1
        then c c1 c2
        else go ts cs
    _, _ →
      unsafeCrashWith "Data.Variant: impossible compare"
