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
  ∷ L.List String
  → L.List (VariantCase → VariantCase → Boolean)
  → Tuple String VariantCase
  → Tuple String VariantCase
  → Boolean
lookupEq tags eqs (Tuple t1 c1) (Tuple t2 c2)
  | t1 == t2  = lookupBinaryFn "eq" t1 tags eqs c1 c2
  | otherwise = false

lookupOrd
  ∷ L.List String
  → L.List (VariantCase → VariantCase → Ordering)
  → Tuple String VariantCase
  → Tuple String VariantCase
  → Ordering
lookupOrd tags ords (Tuple t1 c1) (Tuple t2 c2) =
  case compare t1 t2 of
    EQ → lookupBinaryFn "compare" t1 tags ords c1 c2
    cp → cp

lookupBinaryFn
  ∷ ∀ a b
  . String
  → String
  → L.List String
  → L.List (a → a → b)
  → a
  → a
  → b
lookupBinaryFn name tag = go
  where
  go = case _, _ of
    L.Cons t ts, L.Cons f fs
      | t == tag  → f
      | otherwise → go ts fs
    _, _ →
      unsafeCrashWith $ "Data.Variant: impossible `" <> name <> "`"
