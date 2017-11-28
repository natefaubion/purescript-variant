module Data.Variant
  ( Variant
  , inj
  , prj
  , on
  , onMatch
  , case_
  , match
  , default
  , expand
  , contract
  , class VariantEqs, variantEqs
  , class VariantOrds, variantOrds
  , class VariantShows, variantShows
  , class VariantBounded, variantBounded
  , class VariantBoundedEnums, variantBoundedEnums
  , module Exports
  ) where

import Prelude

import Control.Alternative (empty, class Alternative)
import Data.Enum (class Enum, pred, succ, class BoundedEnum, Cardinality(..), fromEnum, toEnum, cardinality)
import Data.Foldable as F
import Data.List as L
import Data.Symbol (SProxy(..)) as Exports
import Data.Symbol (SProxy, class IsSymbol, reflectSymbol)
import Data.Maybe as M
import Data.Variant.Internal (RLProxy(..), class VariantTags, variantTags, VariantCase, VariantRep(..), BoundedEnumDict, BoundedDict, lookupEq, lookupOrd, lookup, class Contractable, RProxy(..), contractWith, unsafeGet, unsafeHas, class VariantMatchCases, fromJust)
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
inj p value = coerceV $ VariantRep { type: reflectSymbol p, value }
  where
  coerceV ∷ VariantRep a → Variant r2
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
    VariantRep v | v.type == reflectSymbol p → f v.value
    _ → g (coerceR r)
  where
  coerceV ∷ Variant r2 → VariantRep a
  coerceV = unsafeCoerce

  coerceR ∷ Variant r2 → Variant r1
  coerceR = unsafeCoerce

-- | Match a `Variant` with a `Record` containing functions for handling cases.
-- | This is similar to `on`, except instead of providing a single label and
-- | handler, you can provide a record where each field maps to a particular
-- | `Variant` case.
-- |
-- | ```purescript
-- | onMatch
-- |   { foo: \foo -> "Foo: " <> foo
-- |   , bar: \bar -> "Bar: " <> bar
-- |   }
-- | ````
-- |
-- | Polymorphic functions in records (such as `show` or `id`) can lead
-- | to inference issues if not all polymorphic variables are specified
-- | in usage. When in doubt, label methods with specific types, such as
-- | `show :: Int -> String`, or give the whole record an appropriate type.
onMatch
  ∷ ∀ rl r r1 r2 r3 b
  . R.RowToList r rl
  ⇒ VariantMatchCases rl r1 b
  ⇒ Union r1 r2 r3
  ⇒ Record r
  → (Variant r2 → b)
  → Variant r3
  → b
onMatch r k v =
  case coerceV v of
    VariantRep v' | unsafeHas v'.type r → unsafeGet v'.type r v'.value
    _ → k (coerceR v)

  where
  coerceV ∷ ∀ a. Variant r3 → VariantRep a
  coerceV = unsafeCoerce

  coerceR ∷ Variant r3 → Variant r2
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
  VariantRep v → "Data.Variant: pattern match failure [" <> v.type <> "]"

-- | Combinator for exhaustive pattern matching using an `onMatch` case record.
-- | ```purescript
-- | matchFn :: Variant (foo :: Int, bar :: String, baz :: Boolean) -> String
-- | matchFn = match
-- |   { foo: \foo -> "Foo: " <> show foo
-- |   , bar: \bar -> "Bar: " <> bar
-- |   , baz: \baz -> "Baz: " <> show baz
-- |   }
-- | ```
match
  ∷ ∀ rl r r1 r2 b
  . R.RowToList r rl
  ⇒ VariantMatchCases rl r1 b
  ⇒ Union r1 () r2
  ⇒ Record r
  → Variant r2
  → b
match r = case_ # onMatch r

-- | Combinator for partial matching with a default value in case of failure.
-- | ```purescript
-- | caseFn :: forall r. Variant (foo :: Int, bar :: String | r) -> String
-- | caseFn = default "No match"
-- |  # on (SProxy :: SProxy "foo") (\foo -> "Foo: " <> show foo)
-- |  # on (SProxy :: SProxy "bar") (\bar -> "Bar: " <> bar)
-- | ```
default ∷ ∀ a r. a → Variant r → a
default a _ = a

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
    (case coerceV v of VariantRep v' → v'.type)
    (coerceR v)
  where
  coerceV ∷ ∀ a. Variant gt → VariantRep a
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
      c1 = unsafeCoerce v1 ∷ VariantRep VariantCase
      c2 = unsafeCoerce v2 ∷ VariantRep VariantCase
      tags = variantTags (RLProxy ∷ RLProxy rl)
      eqs = variantEqs (RLProxy ∷ RLProxy rl)
    in
      lookupEq tags eqs c1 c2

class VariantBounded (rl ∷ R.RowList) where
  variantBounded ∷ RLProxy rl → L.List (BoundedDict VariantCase)

instance boundedVariantNil ∷ VariantBounded R.Nil where
  variantBounded _ = L.Nil

instance boundedVariantCons ∷ (VariantBounded rs, Bounded a) ⇒ VariantBounded (R.Cons sym a rs) where
  variantBounded _ = L.Cons dict (variantBounded (RLProxy ∷ RLProxy rs))
    where
    dict ∷ BoundedDict VariantCase
    dict =
      { top: coerceA top
      , bottom: coerceA bottom
      }

    coerceA ∷ a → VariantCase
    coerceA = unsafeCoerce

instance boundedVariant
  ∷ ( R.RowToList r rl
    , VariantTags rl
    , VariantEqs rl
    , VariantOrds rl
    , VariantBounded rl
    )
  ⇒ Bounded (Variant r)
  where
    top =
      let
        repToV ∷ ∀ rr a. VariantRep a → Variant rr
        repToV = unsafeCoerce

        prx = RLProxy ∷ RLProxy rl
      in
       repToV
         $ VariantRep
         $ fromJust "top"
         $ { type: _, value: _}
         <$> L.last (variantTags prx)
         <*> (map _.top $ L.last $ variantBounded prx)

    bottom =
      let
        repToV ∷ ∀ rr a. VariantRep a → Variant rr
        repToV = unsafeCoerce

        prx = RLProxy ∷ RLProxy rl
      in
       repToV
         $ VariantRep
         $ fromJust "bottom"
         $ { type: _, value: _ }
         <$> L.head (variantTags prx)
         <*> (map _.bottom $ L.head $ variantBounded prx)

class VariantBounded rl ⇐ VariantBoundedEnums rl where
  variantBoundedEnums ∷ RLProxy rl → L.List (BoundedEnumDict VariantCase)

instance enumVariantNil ∷ VariantBoundedEnums R.Nil where
  variantBoundedEnums _ = L.Nil

instance enumVariantCons
  ∷ (VariantBoundedEnums rs, BoundedEnum a) ⇒ VariantBoundedEnums (R.Cons sym a rs)
  where
    variantBoundedEnums _ = L.Cons dict (variantBoundedEnums (RLProxy ∷ RLProxy rs))
      where
      dict ∷ BoundedEnumDict VariantCase
      dict =
        { pred: coerceAToMbA pred
        , succ: coerceAToMbA succ
        , fromEnum: coerceFromEnum fromEnum
        , toEnum: coerceToEnum toEnum
        , cardinality: coerceCardinality cardinality
        }

      coerceA ∷ a → VariantCase
      coerceA = unsafeCoerce

      coerceAToMbA ∷ (a → M.Maybe a) → VariantCase → M.Maybe VariantCase
      coerceAToMbA = unsafeCoerce

      coerceFromEnum ∷ (a → Int) → VariantCase → Int
      coerceFromEnum = unsafeCoerce

      coerceToEnum ∷ (Int → M.Maybe a) → Int → M.Maybe VariantCase
      coerceToEnum = unsafeCoerce

      coerceCardinality ∷ Cardinality a → Int
      coerceCardinality = unsafeCoerce

instance enumVariant
  ∷ ( R.RowToList r rl
    , VariantTags rl
    , VariantEqs rl
    , VariantOrds rl
    , VariantBoundedEnums rl
    )
  ⇒ Enum (Variant r) where
    pred a = coerceOut case dict.pred $ coerceIn arep.value of
      M.Just b → M.Just $ VariantRep arep{ value = b }
      M.Nothing
        | tagIx == 0 → M.Nothing
        | otherwise →
          map VariantRep
          $ { type: _
            , value: _
            }
          <$> (L.index tags $ tagIx - 1)
          <*> (map _.top $ L.index bounds $ tagIx - 1)

        where
        prx = RLProxy ∷ RLProxy rl

        coerceIn ∷ ∀ a. a → VariantCase
        coerceIn = unsafeCoerce

        coerceOut ∷ M.Maybe (VariantRep VariantCase) → M.Maybe (Variant r)
        coerceOut = unsafeCoerce

        VariantRep arep = unsafeCoerce a

        tagIx ∷ Int
        tagIx = fromJust "enum" $ L.findIndex (eq arep.type) tags

        tags = variantTags prx
        bounds = variantBounded prx
        dicts = variantBoundedEnums prx
        dict = fromJust "enum" $ L.index dicts tagIx

    succ a = coerceOut case dict.succ $ coerceIn arep.value of
      M.Just b → M.Just $ VariantRep arep{ value = b }
      M.Nothing
        | tagIx == total - 1 → M.Nothing
        | otherwise →
          map VariantRep
          $ { type: _
            , value: _
            }
          <$> (L.index tags $ tagIx + 1)
          <*> (map _.bottom $ L.index bounds $ tagIx + 1)

        where
        prx = RLProxy ∷ RLProxy rl

        coerceIn ∷ ∀ a. a → VariantCase
        coerceIn = unsafeCoerce

        coerceOut ∷ M.Maybe (VariantRep VariantCase) → M.Maybe (Variant r)
        coerceOut = unsafeCoerce

        VariantRep arep = unsafeCoerce a

        tagIx ∷ Int
        tagIx = fromJust "enum" $ L.findIndex (eq arep.type) tags

        tags = variantTags prx
        bounds = variantBounded prx
        dicts = variantBoundedEnums prx
        dict = fromJust "enum" $ L.index dicts tagIx
        total = L.length tags

instance boundedEnumVariant
  ∷ ( R.RowToList r rl
    , VariantTags rl
    , VariantEqs rl
    , VariantOrds rl
    , VariantBoundedEnums rl
    )
  ⇒ BoundedEnum (Variant r) where
    cardinality =
      Cardinality
      $ F.sum
      $ map _.cardinality
      $ variantBoundedEnums (RLProxy ∷ RLProxy rl)

    fromEnum inp = go 0 (variantTags prx) (variantBoundedEnums prx)
      where
      prx = RLProxy ∷ RLProxy rl
      VariantRep arep = unsafeCoerce inp

      go ∷ Int → L.List String → L.List (BoundedEnumDict VariantCase) → Int
      go acc = case _, _ of
        L.Cons k tlk, L.Cons dict tldict
          | k == arep.type →
              acc + dict.fromEnum arep.value
          | otherwise →
              let c = dict.cardinality
              in go (acc + c) tlk tldict
        _, _ → unsafeCrashWith "Data.Variant: impossible boundedEnum"

    toEnum n = go n (variantTags prx) (variantBoundedEnums prx)
      where
      prx = RLProxy ∷ RLProxy rl

      repToV ∷ ∀ rr a. VariantRep a → Variant rr
      repToV = unsafeCoerce

      go ix = case _, _ of
        L.Cons k tlk, L.Cons dict tldict
          | dict.cardinality > ix  → case dict.toEnum ix of
              M.Just a → M.Just $ repToV $ VariantRep { type: k, value: a }
              M.Nothing → M.Nothing -- this is impossible in fact
          | otherwise → go (ix - dict.cardinality) tlk tldict
        _, _ → M.Nothing

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
      c1 = unsafeCoerce v1 ∷ VariantRep VariantCase
      c2 = unsafeCoerce v2 ∷ VariantRep VariantCase
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
      VariantRep v = unsafeCoerce v1 ∷ VariantRep VariantCase
      tags = variantTags (RLProxy ∷ RLProxy rl)
      shows = variantShows (RLProxy ∷ RLProxy rl)
      body = lookup "show" v.type tags shows v.value
    in
      "(inj @" <> show v.type <> " " <> body <> ")"
