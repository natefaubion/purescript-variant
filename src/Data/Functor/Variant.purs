module Data.Functor.Variant
  ( VariantF
  , FProxy(..)
  , inj
  , prj
  , on
  , case_
  , default
  , module Exports
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy, class IsSymbol, reflectSymbol)
import Data.Symbol (SProxy(..)) as Exports
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafeCrashWith)
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

data FProxy (a ∷ Type → Type) = FProxy

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
  ∷ ∀ sym f a r1 r2
  . RowCons sym (FProxy f) r1 r2
  ⇒ IsSymbol sym
  ⇒ SProxy sym
  → VariantF r2 a
  → Maybe (f a)
prj p = on p Just (const Nothing)

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

-- | Combinator for partial matching with a default value in case of failure.
-- | ```purescript
-- | caseFn :: forall r. VariantF (foo :: FProxy Maybe, bar :: FProxy (Tuple String) | r) Int -> String
-- | caseFn = default "No match"
-- |  # on (SProxy :: SProxy "foo") (\foo -> "Foo: " <> maybe "nothing" show foo)
-- |  # on (SProxy :: SProxy "bar") (\bar -> "Bar: " <> show (snd bar))
-- | ```
default ∷ ∀ a b r. a → VariantF r b → a
default a _ = a
