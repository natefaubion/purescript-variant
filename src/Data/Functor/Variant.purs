module Data.Functor.Variant
  ( VariantF
  , inj
  , prj
  , on
  , case_
  , default
  , match
  , expand
  , contract
  , module Exports
  ) where

import Prelude

import Control.Alternative (class Alternative, empty)
import Data.Maybe (fromJust)
import Data.StrMap as SM
import Data.Symbol (SProxy(..)) as Exports
import Data.Symbol (SProxy, class IsSymbol, reflectSymbol)
import Data.Tuple (Tuple(..), fst)
import Data.Variant.Internal (class Contractable, contractWith, VariantCase, class VRFMatching, RProxy(..), FProxy)
import Data.Variant.Internal (class Contractable, FProxy(..)) as Exports
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
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

-- | Match a `variant` with a `record` containing methods to handle each case
-- | to produce a `result`.
-- |
-- | This means that if `variant` contains a row of type `FProxy f`, a row with
-- | the same label must have type `f a -> result` in `record`, where `result`
-- | is the same type for every row of `record`.
-- |
-- | Polymorphic methods in `record` may create problems with the type system
-- | if the polymorphism is not fully generalized to the whole record type
-- | or if not all polymorphic variables are specified in usage. When in doubt,
-- | label methods with specific types, such as `show :: Int -> String`, or
-- | give the whole record an appropriate type.
match
  ∷ ∀ variant record typearg result
  . VRFMatching variant record typearg result
  ⇒ VariantF variant typearg
  → Record record
  → result
match v r =
  case coerceV v of
    Tuple tag (FBox _ a) →
      a # unsafePartial fromJust
        (SM.lookup tag (coerceR r))
  where
  coerceV ∷ ∀ f. VariantF variant typearg → Tuple String (FBox f typearg)
  coerceV = unsafeCoerce

  coerceR ∷ ∀ a. Record record → SM.StrMap a
  coerceR = unsafeCoerce

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
