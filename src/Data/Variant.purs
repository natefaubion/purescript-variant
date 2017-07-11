module Data.Variant
  ( Variant
  , inj
  , prj
  , elim
  , on
  , case_
  , default
  , class VariantRecordElim
  , class VariantMatch
  , module Exports
  ) where

import Prelude
import Data.Maybe (Maybe(..), fromJust)
import Data.Symbol (SProxy, class IsSymbol, reflectSymbol)
import Data.Symbol (SProxy(..)) as Exports
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import Unsafe.Coerce (unsafeCoerce)
import Type.Row as R
import Type.Row (class RowToList, class ListToRow)
import Data.StrMap as SM

data Variant (a ∷ # Type)

-- | Inject into the variant at a given label.
-- | ```purescript
-- | intAtFoo :: forall r. Variant (foo :: Int | r)
-- | intAtFoo = inj (SProxy :: SProxy "foo") 42
-- | ```
inj
  ∷ ∀ sym a r1 r2
  . RowCons sym a r1 r2
  ⇒ IsSymbol sym
  ⇒ SProxy sym
  → a
  → Variant r2
inj p a = coerceV (Tuple (reflectSymbol p) a)
  where
  coerceV ∷ Tuple String a → Variant r2
  coerceV = unsafeCoerce

-- | Attempt to read a variant at a given label.
-- | ```purescript
-- | case prj (SProxy :: SProxy "foo") intAtFoo of
-- |   Just i  -> i + 1
-- |   Nothing -> 0
-- | ```
prj
  ∷ ∀ sym a r1 r2
  . RowCons sym a r1 r2
  ⇒ IsSymbol sym
  ⇒ SProxy sym
  → Variant r2
  → Maybe a
prj p = on p Just (const Nothing)

-- | Attempt to read a variant at a given label by providing branches.
-- | The failure branch receives the provided variant, but with the label
-- | removed.
on
  ∷ ∀ sym a b r1 r2
  . RowCons sym a r1 r2
  ⇒ IsSymbol sym
  ⇒ SProxy sym
  → (a → b)
  → (Variant r1 → b)
  → Variant r2
  → b
on p f g r =
  case coerceV r of
    Tuple tag a | tag == reflectSymbol p → f a
    _ → g (coerceR r)
  where
  coerceV ∷ Variant r2 → Tuple String a
  coerceV = unsafeCoerce

  coerceR ∷ Variant r2 → Variant r1
  coerceR = unsafeCoerce

-- | Type class that matches a row for a `record` that will eliminate a row for
-- | a `variant`, producing a `result` of the specified type. Just a wrapper for
-- | `VariantMatch` to convert `RowToList` and vice versa.
class VariantRecordElim
    (variant ∷ # Type)
    (record ∷ # Type)
    result
  | variant result → record
  , record → variant result
instance variantRecordElim
  ∷ ( RowToList variant vlist
    , RowToList record rlist
    , VariantMatch vlist rlist result
    , ListToRow vlist variant
    , ListToRow rlist record )
  ⇒ VariantRecordElim variant record result

-- | Checks that a `RowList` matches the argument to be given to the function
-- | in the other `RowList` with the same label, such that it will produce the
-- | result type.
class VariantMatch
    (vlist ∷ R.RowList)
    (rlist ∷ R.RowList)
    result
  | vlist result → rlist
  , rlist → vlist result
instance variantMatchNil
  ∷ VariantMatch R.Nil R.Nil r
instance variantMatchCons
  ∷ VariantMatch v r res
  ⇒ VariantMatch (R.Cons sym a v) (R.Cons sym (a → res) r) res

-- | Eliminate a `variant` with a `record` containing methods to handle each
-- | case and produce a unified `result`.
-- |
-- | This means that if `variant` contains a row of type `a`, a row with the
-- | same label must have type `a -> b` in `record`, where `b` is the same
-- | `result` type for every row of `record`.
-- |
-- | Methods in `record` cannot have any constraints, due to limitations in
-- | PureScript's type system. This means that class methods must be given a
-- | concrete type, as in `{ foo: show :: Int -> String }`. Other functions
-- | using `forall` will still work if they do not contain constraints, but note
-- | that even `id` must be given a type annotation to be used in this way,
-- | since it normally depends on `Category`: use `id :: forall a. a -> a` not
-- | `id :: forall a c. Category c => c a a`.
elim
  ∷ ∀ variant record result
  . VariantRecordElim variant record result
  ⇒ Variant variant
  → Record record
  → result
elim v r =
  case coerceV v of
    Tuple tag a →
      a # unsafePartial fromJust
        (SM.lookup tag (coerceR r))
  where
  coerceV ∷ ∀ a. Variant variant → Tuple String a
  coerceV = unsafeCoerce

  coerceR ∷ ∀ a. Record record → SM.StrMap a
  coerceR = unsafeCoerce

-- | Combinator for exhaustive pattern matching.
-- | ```purescript
-- | caseFn :: Variant (foo :: Int, bar :: String, baz :: Boolean) -> String
-- | caseFn = case_
-- |  # on (SProxy :: SProxy "foo") (\foo -> "Foo: " <> show foo)
-- |  # on (SProxy :: SProxy "bar") (\bar -> "Bar: " <> bar)
-- |  # on (SProxy :: SProxy "baz") (\baz -> "Baz: " <> show baz)
-- | ```
case_ ∷ ∀ a. Variant () → a
case_ r = unsafeCrashWith case unsafeCoerce r of
  Tuple tag _ → "Data.Variant: pattern match failure [" <> tag <> "]"

-- | Combinator for partial matching with a default value in case of failure.
-- | ```purescript
-- | caseFn :: forall r. Variant (foo :: Int, bar :: String | r) -> String
-- | caseFn = default "No match"
-- |  # on (SProxy :: SProxy "foo") (\foo -> "Foo: " <> show foo)
-- |  # on (SProxy :: SProxy "bar") (\bar -> "Bar: " <> bar)
-- | ```
default ∷ ∀ a r. a → Variant r → a
default a _ = a
