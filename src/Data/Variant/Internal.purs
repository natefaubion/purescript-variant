module Data.Variant.Internal
  ( RLProxy(..)
  , VariantCase
  , class VariantTags
  , variantTags
  , lookupTag
  , lookupEq
  , lookupOrd
  ) where

import Prelude
import Data.List as L
import Data.Symbol (SProxy(..), class IsSymbol, reflectSymbol)
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafeCrashWith)
import Type.Row as R

data RLProxy (rl ∷ R.RowList) = RLProxy

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
