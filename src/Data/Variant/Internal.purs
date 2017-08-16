module Data.Variant.Internal
  ( FProxy(..)
  , VariantCase
  , class VariantTags, variantTags
  , class Contractable, contractWith
  , class VariantRecordMatching
  , class VariantMatchEachCase
  , class VariantFRecordMatching
  , class VariantFMatchEachCase
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
import Data.Record.Unsafe (unsafeGet) as Exports
import Partial.Unsafe (unsafeCrashWith)
import Type.Row as R
import Type.Row (RProxy, RLProxy(..))
import Type.Row (RProxy(..), RLProxy(..)) as Exports

-- | Proxy for a `Functor`.
data FProxy (a ∷ Type → Type) = FProxy

-- | Type class that matches a row for a `record` that will eliminate a row for
-- | a `variant`, producing a `result` of the specified type. Just a wrapper for
-- | `RLMatch` to convert `RowToList` and vice versa.
class VariantRecordMatching
    (variant ∷ # Type)
    (record ∷ # Type)
    result
  | → variant record result
instance variantRecordMatching
  ∷ ( R.RowToList variant vlist
    , R.RowToList record rlist
    , VariantMatchEachCase vlist rlist result
    , R.ListToRow vlist variant
    , R.ListToRow rlist record )
  ⇒ VariantRecordMatching variant record result

-- | Checks that a `RowList` matches the argument to be given to the function
-- | in the other `RowList` with the same label, such that it will produce the
-- | result type.
class VariantMatchEachCase
    (vlist ∷ R.RowList)
    (rlist ∷ R.RowList)
    result
  | vlist → rlist result
  , rlist → vlist result
instance variantMatchNil
  ∷ VariantMatchEachCase R.Nil R.Nil r
instance variantMatchCons
  ∷ VariantMatchEachCase v r res
  ⇒ VariantMatchEachCase
    (R.Cons sym a v)
    (R.Cons sym (a → res) r)
    res

class VariantFRecordMatching
    (variant ∷ # Type)
    (record ∷ # Type)
    typearg
    result
  | → variant record typearg result
instance variantFRecordMatching
  ∷ ( R.RowToList variant vlist
    , R.RowToList record rlist
    , VariantFMatchEachCase vlist rlist typearg result
    , R.ListToRow vlist variant
    , R.ListToRow rlist record )
  ⇒ VariantFRecordMatching variant record typearg result

-- | Checks that a `RowList` matches the argument to be given to the function
-- | in the other `RowList` with the same label, such that it will produce the
-- | result type.
class VariantFMatchEachCase
    (vlist ∷ R.RowList)
    (rlist ∷ R.RowList)
    typearg
    result
  | vlist → rlist typearg result
  , rlist → vlist typearg result
instance variantFMatchNil
  ∷ VariantFMatchEachCase R.Nil R.Nil a r
instance variantFMatchCons
  ∷ VariantFMatchEachCase v r a res
  ⇒ VariantFMatchEachCase
    (R.Cons sym (FProxy f) v)
    (R.Cons sym (f a → res) r)
    a res

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
