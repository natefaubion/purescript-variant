module Data.Variant
  ( Variant
  , inj
  , prj
  , on
  , case_
  , default
  , match
  , expand
  , contract
  , class VariantEqs, variantEqs
  , class VariantOrds, variantOrds
  , class VariantShows, variantShows
  , module Exports
  ) where

import Prelude

import Control.Alternative (empty, class Alternative)
import Data.List as L
import Data.Symbol (SProxy(..)) as Exports
import Data.Symbol (SProxy, class IsSymbol, reflectSymbol)
import Data.Tuple (Tuple(..), fst)
import Data.Variant.Internal (RLProxy(..), class VariantTags, variantTags, VariantCase, lookupEq, lookupOrd, lookup, class Contractable, RProxy(..), contractWith, unsafeGet, unsafeHas, class VariantMatchCases)
import Data.Variant.Internal (class Contractable, class VariantMatchCases) as Exports
import Partial.Unsafe (unsafeCrashWith)
import Type.Row as R
import Unsafe.Coerce (unsafeCoerce)

foreign import data Variant ∷ # Type → Type

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
  ∷ ∀ sym a r1 r2 f
  . RowCons sym a r1 r2
  ⇒ IsSymbol sym
  ⇒ Alternative f
  ⇒ SProxy sym
  → Variant r2
  → f a
prj p = on p pure (const empty)

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

-- | Match a `Variant` with a `Record` containing functions for handling cases.
-- | This is similar to `on`, except instead of providing a single label and
-- | handler, you can provide a record where each field maps to a particular
-- | `Variant` case.
-- |
-- | ```purescript
-- | caseFn :: Variant (foo :: Int, bar :: String, baz :: Boolean) -> String
-- | caseFn = case_ # match
-- |   { foo: \foo -> "Foo: " <> show foo
-- |   , bar: \bar -> "Bar: " <> bar
-- |   , baz: \baz -> "Baz: " <> show baz
-- |   }
-- | ```
-- |
-- | Like with `on`, this can be combined with `default` as well for partial
-- | matches.
-- |
-- | Polymorphic functions in records (such as `show` or `id`) can lead
-- | to inference issues if not all polymorphic variables are specified
-- | in usage. When in doubt, label methods with specific types, such as
-- | `show :: Int -> String`, or give the whole record an appropriate type.
match
  ∷ ∀ rl r r1 r2 r3 b
  . R.RowToList r rl
  ⇒ VariantMatchCases rl r1 b
  ⇒ Union r1 r2 r3
  ⇒ Record r
  → (Variant r2 → b)
  → Variant r3
  → b
match r k v =
  case coerceV v of
    Tuple tag a | unsafeHas tag r → unsafeGet tag r a
    _ → k (coerceR v)

  where
  coerceV ∷ ∀ a. Variant r3 → Tuple String a
  coerceV = unsafeCoerce

  coerceR ∷ Variant r3 → Variant r2
  coerceR = unsafeCoerce

-- | Every `Variant lt` can be cast to some `Variant gt` as long as `lt` is a
-- | subset of `gt`.
expand
  ∷ ∀ lt a gt
  . Union lt a gt
  ⇒ Variant lt
  → Variant gt
expand = unsafeCoerce

-- | A `Variant gt` can be cast to some `Variant lt`, where `lt` is is a subset
-- | of `gt`, as long as there is proof that the `Variant`'s runtime tag is
-- | within the subset of `lt`.
contract
  ∷ ∀ lt gt f
  . Alternative f
  ⇒ Contractable gt lt
  ⇒ Variant gt
  → f (Variant lt)
contract v =
  contractWith
    (RProxy ∷ RProxy gt)
    (RProxy ∷ RProxy lt)
    (fst $ coerceV v)
    (coerceR v)
  where
  coerceV ∷ Variant gt → Tuple String VariantCase
  coerceV = unsafeCoerce

  coerceR ∷ Variant gt → Variant lt
  coerceR = unsafeCoerce

class VariantEqs (rl ∷ R.RowList) where
  variantEqs ∷ RLProxy rl → L.List (VariantCase → VariantCase → Boolean)

instance eqVariantNil ∷ VariantEqs R.Nil where
  variantEqs _ = L.Nil

instance eqVariantCons ∷ (VariantEqs rs, Eq a) ⇒ VariantEqs (R.Cons sym a rs) where
  variantEqs _ =
    L.Cons (coerceEq eq) (variantEqs (RLProxy ∷ RLProxy rs))
    where
    coerceEq ∷ (a → a → Boolean) → VariantCase → VariantCase → Boolean
    coerceEq = unsafeCoerce

instance eqVariant ∷ (R.RowToList r rl, VariantTags rl, VariantEqs rl) ⇒ Eq (Variant r) where
  eq v1 v2 =
    let
      c1 = unsafeCoerce v1 ∷ Tuple String VariantCase
      c2 = unsafeCoerce v2 ∷ Tuple String VariantCase
      tags = variantTags (RLProxy ∷ RLProxy rl)
      eqs = variantEqs (RLProxy ∷ RLProxy rl)
    in
      lookupEq tags eqs c1 c2

class VariantOrds (rl ∷ R.RowList) where
  variantOrds ∷ RLProxy rl → L.List (VariantCase → VariantCase → Ordering)

instance ordVariantNil ∷ VariantOrds R.Nil where
  variantOrds _ = L.Nil

instance ordVariantCons ∷ (VariantOrds rs, Ord a) ⇒ VariantOrds (R.Cons sym a rs) where
  variantOrds _ =
    L.Cons (coerceOrd compare) (variantOrds (RLProxy ∷ RLProxy rs))
    where
    coerceOrd ∷ (a → a → Ordering) → VariantCase → VariantCase → Ordering
    coerceOrd = unsafeCoerce

instance ordVariant ∷ (R.RowToList r rl, VariantTags rl, VariantEqs rl, VariantOrds rl) ⇒ Ord (Variant r) where
  compare v1 v2 =
    let
      c1 = unsafeCoerce v1 ∷ Tuple String VariantCase
      c2 = unsafeCoerce v2 ∷ Tuple String VariantCase
      tags = variantTags (RLProxy ∷ RLProxy rl)
      ords = variantOrds (RLProxy ∷ RLProxy rl)
    in
      lookupOrd tags ords c1 c2

class VariantShows (rl ∷ R.RowList) where
  variantShows ∷ RLProxy rl → L.List (VariantCase → String)

instance showVariantNil ∷ VariantShows R.Nil where
  variantShows _ = L.Nil

instance showVariantCons ∷ (VariantShows rs, Show a) ⇒ VariantShows (R.Cons sym a rs) where
  variantShows _ =
    L.Cons (coerceShow show) (variantShows (RLProxy ∷ RLProxy rs))
    where
    coerceShow ∷ (a → String) → VariantCase → String
    coerceShow = unsafeCoerce

instance showVariant ∷ (R.RowToList r rl, VariantTags rl, VariantShows rl) ⇒ Show (Variant r) where
  show v1 =
    let
      Tuple t c = unsafeCoerce v1 ∷ Tuple String VariantCase
      tags = variantTags (RLProxy ∷ RLProxy rl)
      shows = variantShows (RLProxy ∷ RLProxy rl)
      body = lookup "show" t tags shows c
    in
      "(inj @" <> show t <> " (" <> body <> "))"
