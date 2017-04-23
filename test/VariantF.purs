module Test.VariantF where

import Prelude
import Control.Monad.Eff (Eff)
import Data.Either (Either(..))
import Data.Functor.Variant (VariantF, on, case_, default, inj, prj, SProxy(..), FProxy)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Test.Assert (assert', ASSERT)

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

test ∷ Eff (assert ∷ ASSERT) Unit
test = do
  assert' "prj: Foo" $ prj _foo foo == Just (Just 42)
  assert' "prj: !Foo" $ prj _foo bar == Nothing ∷ Maybe (Maybe Int)

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
