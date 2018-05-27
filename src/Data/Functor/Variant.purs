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
  , class VariantFShows, variantFShows
  , module Exports
  ) where

import Prelude

import Control.Alternative (class Alternative, empty)
import Data.List as L
import Data.Symbol (SProxy(..)) as Exports
import Data.Symbol (SProxy, class IsSymbol, reflectSymbol)
import Data.Variant.Internal (class Contractable, FProxy(..), class VariantFMatchCases) as Exports
import Data.Variant.Internal (class Contractable, class VariantFMatchCases, class VariantTags, FProxy, RLProxy(..), RProxy(..), VariantFCase, VariantCase, contractWith, lookup, unsafeGet, unsafeHas, variantTags)
import Partial.Unsafe (unsafeCrashWith)
import Prim.Row as Row
import Type.Equality (class TypeEquals)
import Type.Proxy (Proxy(..))
import Type.Row as R
import Unsafe.Coerce (unsafeCoerce)

newtype VariantFRep f a = VariantFRep
  { type ∷ String
  , value ∷ f a
  , map ∷ ∀ x y. (x → y) → f x → f y
  }

data VariantF (f ∷ # Type) a

instance functorVariantF ∷ Functor (VariantF r) where
  map f a =
    case coerceY a of
      VariantFRep v → coerceV $ VariantFRep
        { type: v.type
        , value: v.map f v.value
        , map: v.map
        }
    where
    coerceY ∷ ∀ f a. VariantF r a → VariantFRep f a
    coerceY = unsafeCoerce

    coerceV ∷ ∀ f a. VariantFRep f a → VariantF r a
    coerceV = unsafeCoerce

-- | Inject into the variant at a given label.
-- | ```purescript
-- | maybeAtFoo :: forall r. VariantF (foo :: FProxy Maybe | r) Int
-- | maybeAtFoo = inj (SProxy :: SProxy "foo") (Just 42)
-- | ```
inj
  ∷ ∀ sym f a r1 r2
  . Row.Cons sym (FProxy f) r1 r2
  ⇒ IsSymbol sym
  ⇒ Functor f
  ⇒ SProxy sym
  → f a
  → VariantF r2 a
inj p value = coerceV $ VariantFRep { type: reflectSymbol p, value, map }
  where
  coerceV ∷ VariantFRep f a → VariantF r2 a
  coerceV = unsafeCoerce

-- | Attempt to read a variant at a given label.
-- | ```purescript
-- | case prj (SProxy :: SProxy "foo") maybeAtFoo of
-- |   Just (Just i) -> i + 1
-- |   _ -> 0
-- | ```
prj
  ∷ ∀ sym f a r1 r2 g
  . Row.Cons sym (FProxy f) r1 r2
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
  . Row.Cons sym (FProxy f) r1 r2
  ⇒ IsSymbol sym
  ⇒ SProxy sym
  → (f a → b)
  → (VariantF r1 a → b)
  → VariantF r2 a
  → b
on p f g r =
  case coerceY r of
    VariantFRep v | v.type == reflectSymbol p → f v.value
    _ → g (coerceR r)
  where
  coerceY ∷ VariantF r2 a → VariantFRep f a
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
  ⇒ Row.Union r1 r2 r3
  ⇒ Record r
  → (VariantF r2 a → b)
  → VariantF r3 a
  → b
onMatch r k v =
  case coerceV v of
    VariantFRep v' | unsafeHas v'.type r → unsafeGet v'.type r v'.value
    _ → k (coerceR v)

  where
  coerceV ∷ ∀ f. VariantF r3 a → VariantFRep f a
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
  VariantFRep v → "Data.Functor.Variant: pattern match failure [" <> v.type <> "]"

-- | Combinator for exhaustive pattern matching using an `onMatch` case record.
-- | ```purescript
-- | matchFn :: VariantF (foo :: FProxy Maybe, bar :: FProxy (Tuple String), baz :: FProxy (Either String)) Int -> String
-- | matchFn = match
-- |  { foo: \foo -> "Foo: " <> maybe "nothing" show foo
-- |  , bar: \bar -> "Bar: " <> show (snd bar)
-- |  , baz: \baz -> "Baz: " <> either id show baz
-- |  }
-- | ```
match
  ∷ ∀ rl r r1 r2 a b
  . R.RowToList r rl
  ⇒ VariantFMatchCases rl r1 a b
  ⇒ Row.Union r1 () r2
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
  . Row.Union lt mix gt
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
    (case coerceV v of VariantFRep v' → v'.type)
    (coerceR v)
  where
  coerceV ∷ ∀ g. VariantF gt a → VariantFRep g a
  coerceV = unsafeCoerce

  coerceR ∷ VariantF gt a → VariantF lt a
  coerceR = unsafeCoerce

class VariantFShows (rl ∷ R.RowList) x where
  variantFShows ∷ RLProxy rl → Proxy x → L.List (VariantCase → String)

instance showVariantFNil ∷ VariantFShows R.Nil x where
  variantFShows _ _ = L.Nil

instance showVariantFCons ∷ (VariantFShows rs x, TypeEquals a (FProxy f), Show (f x), Show x) ⇒ VariantFShows (R.Cons sym a rs) x where
  variantFShows _ p =
    L.Cons (coerceShow show) (variantFShows (RLProxy ∷ RLProxy rs) p)
    where
    coerceShow ∷ (f x → String) → VariantCase → String
    coerceShow = unsafeCoerce

instance showVariantF ∷ (R.RowToList r rl, VariantTags rl, VariantFShows rl a, Show a) ⇒ Show (VariantF r a) where
  show v1 =
    let
      VariantFRep v = unsafeCoerce v1 ∷ VariantFRep VariantFCase a
      tags = variantTags (RLProxy ∷ RLProxy rl)
      shows = variantFShows (RLProxy ∷ RLProxy rl) (Proxy ∷ Proxy a)
      body = lookup "show" v.type tags shows (unsafeCoerce v.value ∷ VariantCase)
    in
      "(inj @" <> show v.type <> " " <> body <> ")"
