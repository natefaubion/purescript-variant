module Data.Variant
  ( Variant
  , inj
  , prj
  , on
  , case_
  , default
  , expand
  , contract
  , RWProxy(..)
  , class VariantEqs, variantEqs
  , class VariantOrds, variantOrds
  , class Contractable, rowTags
  , module Exports
  ) where

import Prelude
import Control.Alternative (empty, class Alternative)
import Data.List as L
import Data.Symbol (SProxy, class IsSymbol, reflectSymbol)
import Data.Symbol (SProxy(..)) as Exports
import Data.Tuple (Tuple(..), fst)
import Data.Variant.Internal (RLProxy(..), class VariantTags, variantTags, VariantCase, lookupEq, lookupOrd, lookupTag)
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

-- | Every `Variant ra` can be cast to some `Variant rb` as long as `ra` is a
-- | subset of `rb`.
expand
  ∷ ∀ ra rb rs
  . Union ra rs rb
  ⇒ Variant ra
  → Variant rb
expand = unsafeCoerce

-- | A `Variant rb` can be cast to some `Variant ra`, where `ra` is is a subset
-- | of `rb`, as long as there is proof that the `Variant`'s runtime tag is
-- | within the subset of `ra`.
contract
  ∷ ∀ ra rb f
  . Alternative f
  ⇒ Contractable rb ra
  ⇒ Variant rb
  → f (Variant ra)
contract v =
  if lookupTag (fst (coerceV v)) (rowTags (RWProxy ∷ RWProxy rb ra))
    then pure (coerceR v)
    else empty
  where
  coerceV ∷ ∀ a. Variant rb → Tuple String a
  coerceV = unsafeCoerce

  coerceR ∷ Variant rb → Variant ra
  coerceR = unsafeCoerce

data RWProxy (gt ∷ # Type) (lt ∷ # Type) = RWProxy

class Contractable (gt ∷ # Type) (lt ∷ # Type) where
  rowTags ∷ RWProxy gt lt → L.List String

instance
  contractable
  ∷ (R.RowToList lt ltl, VariantTags ltl, Union lt a gt) ⇒ Contractable gt lt
  where
    rowTags _ = variantTags (RLProxy ∷ RLProxy ltl)

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
