module Test.VariantF where

import Prelude

import Data.Either (Either(..))
import Data.Functor.Variant (FProxy, SProxy(..), VariantF, case_, contract, default, inj, match, on, onMatch, prj, revariantF, unvariantF)
import Data.List as L
import Data.Maybe (Maybe(..), isJust)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Test.Assert (assert')

type TestVariants =
  ( foo ∷ FProxy Maybe
  , bar ∷ FProxy (Tuple String)
  , baz ∷ FProxy (Either String)
  )

_foo ∷ SProxy "foo"
_foo = SProxy

_bar ∷ SProxy "bar"
_bar = SProxy

_baz ∷ SProxy "baz"
_baz = SProxy

foo ∷ ∀ r. VariantF (foo ∷ FProxy Maybe | r) Int
foo = inj _foo (Just 42)

bar ∷ ∀ r. VariantF (bar ∷ FProxy (Tuple String) | r) Int
bar = inj _bar (Tuple "bar" 42)

baz ∷ ∀ r. VariantF (baz ∷ FProxy (Either String) | r) Int
baz = inj _baz (Left "baz")

completeness ∷ ∀ r a. VariantF r a → VariantF r a
completeness = revariantF <<< unvariantF

test ∷ Effect Unit
test = do
  assert' "prj: Foo" $ prj _foo foo == Just (Just 42)
  assert' "prj: !Foo" $ prj _foo bar == (Nothing ∷ Maybe (Maybe Int))

  let
    case1 ∷ VariantF TestVariants Int → String
    case1 = case_
      # on _foo (\a → "foo: " <> show a)
      # on _bar (\a → "bar: " <> show a)
      # on _baz (\a → "baz: " <> show a)

  assert' "case1: foo" $ case1 foo == "foo: (Just 42)"
  assert' "case1: bar" $ case1 bar == "bar: (Tuple \"bar\" 42)"
  assert' "case1: baz" $ case1 baz == "baz: (Left \"baz\")"

  let
    case2 ∷ VariantF TestVariants Int → String
    case2 = default "no match"
      # on _foo (\a → "foo: " <> show a)
      # on _bar (\a → "bar: " <> show a)

  assert' "case2: foo" $ case2 foo == "foo: (Just 42)"
  assert' "case2: bar" $ case2 bar == "bar: (Tuple \"bar\" 42)"
  assert' "case2: baz" $ case2 baz == "no match"

  let
    case3 ∷ VariantF (foo ∷ FProxy Maybe) String → String
    case3 = case_ # on _foo (\a → "foo: " <> show a)

  assert' "map" $ case3 (show <$> foo) == "foo: (Just \"42\")"

  let
    match' ∷ VariantF TestVariants Int → String
    match' = match
      { foo: \a → "foo: " <> show a
      , bar: \a → "bar: " <> show a
      , baz: \a → "baz: " <> show a
      }

  assert' "match: foo" $ match' foo == "foo: (Just 42)"
  assert' "match: bar" $ match' bar == "bar: (Tuple \"bar\" 42)"
  assert' "match: baz" $ match' baz == "baz: (Left \"baz\")"

  let
    onMatch' ∷ VariantF TestVariants Int → String
    onMatch' = case_
      # onMatch
        { foo: \a → "foo: " <> show a
        , baz: \a → "baz: " <> show a
        }
      # onMatch
        { bar: \a → "bar: " <> show a
        }

  assert' "onMatch: foo" $ onMatch' foo == "foo: (Just 42)"
  assert' "onMatch: bar" $ onMatch' bar == "bar: (Tuple \"bar\" 42)"
  assert' "onMatch: baz" $ onMatch' baz == "baz: (Left \"baz\")"

  let
    map' ∷ VariantF TestVariants Int → String
    map' = case_
      # on _foo (\a → "foo: " <> show a)
      # on _bar (\a → "bar: " <> show a)
      # on _baz (\a → "baz: " <> show a)

    map'' ∷ VariantF TestVariants Int → String
    map'' = map (_ + 2) >>> map'

  assert' "map: foo" $ map'' foo == "foo: (Just 44)"
  assert' "map: bar" $ map'' bar == "bar: (Tuple \"bar\" 44)"
  assert' "map: baz" $ map'' baz == "baz: (Left \"baz\")"

  assert' "contract: pass"
    $ isJust
    $ (contract (foo ∷ VariantF TestVariants Int) ∷ Maybe (VariantF (foo ∷ FProxy Maybe) Int))

  assert' "contract: fail"
    $ L.null
    $ (contract (bar ∷ VariantF TestVariants Int) ∷ L.List (VariantF (foo ∷ FProxy Maybe) Int))

  assert' "show" $ show (foo :: VariantF TestVariants Int) ==  """(inj @"foo" (Just 42))"""
