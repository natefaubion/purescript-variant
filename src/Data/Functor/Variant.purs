module Data.Functor.Variant
  ( VariantF
  , inj
  , prj
  , on
  , onMatch
  , case_
  , match
  , default
  , expand
  , contract
  , module Exports
  ) where

import Prelude

import Control.Alternative (class Alternative, empty)
import Data.Symbol (SProxy(..)) as Exports
import Data.Symbol (SProxy, class IsSymbol, reflectSymbol)
import Data.Tuple (Tuple(..), fst)
import Data.Variant.Internal (class Contractable, contractWith, VariantCase, RProxy(..), FProxy, class VariantFMatchCases, unsafeGet, unsafeHas)
import Data.Variant.Internal (class Contractable, FProxy(..), class VariantFMatchCases) as Exports
import Partial.Unsafe (unsafeCrashWith)
import Type.Row as R
import Unsafe.Coerce (unsafeCoerce)

data FBox (f ∷ Type → Type) a = FBox (∀ x y. (x → y) → f x → f y) (f a)

instance functorFBox ∷ Functor (FBox f) where
  map f (FBox map' a) = FBox map' (map' f a)

data VariantF (f ∷ # Type) a

instance functorVariantF ∷ Functor (VariantF r) where
  map f a =
    case coerceY a of
      Tuple tag a' → coerceV (Tuple tag (f <$> a'))
    where
    coerceY ∷ ∀ f a. VariantF r a → Tuple String (FBox f a)
    coerceY = unsafeCoerce

    coerceV ∷ ∀ f a. Tuple String (FBox f a) → VariantF r a
    coerceV = unsafeCoerce

-- | Inject into the variant at a given label.
-- | ```purescript
-- | maybeAtFoo :: forall r. VariantF (foo :: FProxy Maybe | r) Int
-- | maybeAtFoo = inj (SProxy :: SProxy "foo") (Just 42)
-- | ```
inj
  ∷ ∀ sym f a r1 r2
  . RowCons sym (FProxy f) r1 r2
  ⇒ IsSymbol sym
  ⇒ Functor f
  ⇒ SProxy sym
  → f a
  → VariantF r2 a
inj p a = coerceV (Tuple (reflectSymbol p) (FBox map a))
  where
  coerceV ∷ Tuple String (FBox f a) → VariantF r2 a
  coerceV = unsafeCoerce

-- | Attempt to read a variant at a given label.
-- | ```purescript
-- | case prj (SProxy :: SProxy "foo") maybeAtFoo of
-- |   Just (Just i) -> i + 1
-- |   _ -> 0
-- | ```
prj
  ∷ ∀ sym f a r1 r2 g
  . RowCons sym (FProxy f) r1 r2
  ⇒ Alternative g
  ⇒ IsSymbol sym
  ⇒ SProxy sym
  → VariantF r2 a
  → g (f a)
prj p = on p pure (const empty)

-- | Attempt to read a variant at a given label by providing branches.
-- | The failure branch receives the provided variant, but with the label
-- | removed.
on
  ∷ ∀ sym f a b r1 r2
  . RowCons sym (FProxy f) r1 r2
  ⇒ IsSymbol sym
  ⇒ SProxy sym
  → (f a → b)
  → (VariantF r1 a → b)
  → VariantF r2 a
  → b
on p f g r =
  case coerceY r of
    Tuple tag (FBox _ a) | tag == reflectSymbol p → f a
    _ → g (coerceR r)
  where
  coerceY ∷ VariantF r2 a → Tuple String (FBox f a)
  coerceY = unsafeCoerce

  coerceR ∷ VariantF r2 a → VariantF r1 a
  coerceR = unsafeCoerce

-- | Match a `VariantF` with a `Record` containing functions for handling cases.
-- | This is similar to `on`, except instead of providing a single label and
-- | handler, you can provide a record where each field maps to a particular
-- | `VariantF` case.
-- |
-- | ```purescript
-- | onMatch
-- |  { foo: \foo -> "Foo: " <> maybe "nothing" id foo
-- |  , bar: \bar -> "Bar: " <> snd bar
-- |  }
-- | ```
-- |
-- | Polymorphic functions in records (such as `show` or `id`) can lead
-- | to inference issues if not all polymorphic variables are specified
-- | in usage. When in doubt, label methods with specific types, such as
-- | `show :: Int -> String`, or give the whole record an appropriate type.
onMatch
  ∷ ∀ rl r r1 r2 r3 a b
  . R.RowToList r rl
  ⇒ VariantFMatchCases rl r1 a b
  ⇒ Union r1 r2 r3
  ⇒ Record r
  → (VariantF r2 a → b)
  → VariantF r3 a
  → b
onMatch r k v =
  case coerceV v of
    Tuple tag (FBox _ a) | unsafeHas tag r → unsafeGet tag r a
    _ → k (coerceR v)

  where
  coerceV ∷ ∀ f. VariantF r3 a → Tuple String (FBox f a)
  coerceV = unsafeCoerce

  coerceR ∷ VariantF r3 a → VariantF r2 a
  coerceR = unsafeCoerce

-- | Combinator for exhaustive pattern matching.
-- | ```purescript
-- | caseFn :: VariantF (foo :: FProxy Maybe, bar :: FProxy (Tuple String), baz :: FProxy (Either String)) Int -> String
-- | caseFn = case_
-- |  # on (SProxy :: SProxy "foo") (\foo -> "Foo: " <> maybe "nothing" show foo)
-- |  # on (SProxy :: SProxy "bar") (\bar -> "Bar: " <> show (snd bar))
-- |  # on (SProxy :: SProxy "baz") (\baz -> "Baz: " <> either id show baz)
-- | ```
case_ ∷ ∀ a b. VariantF () a → b
case_ r = unsafeCrashWith case unsafeCoerce r of
  Tuple tag _ → "Data.Functor.Variant: pattern match failure [" <> tag <> "]"

-- | Combinator for exhaustive pattern matching using an `onMatch` case record.
-- | ```purescript
-- | matchFn :: VariantF (foo :: FProxy Maybe, bar :: FProxy (Tuple String), baz :: FProxy (Either String)) Int -> String
-- | matchFn = case_ # match
-- |  { foo: \foo -> "Foo: " <> maybe "nothing" show foo
-- |  , bar: \bar -> "Bar: " <> show (snd bar)
-- |  , baz: \baz -> "Baz: " <> either id show baz
-- |  }
-- | ```
match
  ∷ ∀ rl r r1 r2 a b
  . R.RowToList r rl
  ⇒ VariantFMatchCases rl r1 a b
  ⇒ Union r1 () r2
  ⇒ Record r
  → VariantF r2 a
  → b
match r = case_ # onMatch r

-- | Combinator for partial matching with a default value in case of failure.
-- | ```purescript
-- | caseFn :: forall r. VariantF (foo :: FProxy Maybe, bar :: FProxy (Tuple String) | r) Int -> String
-- | caseFn = default "No match"
-- |  # on (SProxy :: SProxy "foo") (\foo -> "Foo: " <> maybe "nothing" show foo)
-- |  # on (SProxy :: SProxy "bar") (\bar -> "Bar: " <> show (snd bar))
-- | ```
default ∷ ∀ a b r. a → VariantF r b → a
default a _ = a

-- | Every `VariantF lt a` can be cast to some `VariantF gt a` as long as `lt` is a
-- | subset of `gt`.
expand
  ∷ ∀ lt mix gt a
  . Union lt mix gt
  ⇒ VariantF lt a
  → VariantF gt a
expand = unsafeCoerce

-- | A `VariantF gt a` can be cast to some `VariantF lt a`, where `lt` is is a subset
-- | of `gt`, as long as there is proof that the `VariantF`'s runtime tag is
-- | within the subset of `lt`.
contract
  ∷ ∀ lt gt f a
  . Alternative f
  ⇒ Contractable gt lt
  ⇒ VariantF gt a
  → f (VariantF lt a)
contract v =
  contractWith
    (RProxy ∷ RProxy gt)
    (RProxy ∷ RProxy lt)
    (fst $ coerceV v)
    (coerceR v)
  where
  coerceV ∷ VariantF gt a → Tuple String VariantCase
  coerceV = unsafeCoerce

  coerceR ∷ VariantF gt a → VariantF lt a
  coerceR = unsafeCoerce
