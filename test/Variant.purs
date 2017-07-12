module Test.Variant where

import Prelude
import Control.Monad.Eff (Eff)
import Data.Maybe (Maybe(..))
import Data.Variant (Variant, on, case_, default, inj, prj, SProxy(..), match, (##), (:+:), mapCase, ($$), variant, downcast)
import Test.Assert (assert', ASSERT)

type TestVariants =
  ( foo ∷ Int
  , bar ∷ String
  , baz ∷ Boolean
  )

_foo ∷ SProxy "foo"
_foo = SProxy

_bar ∷ SProxy "bar"
_bar = SProxy

_baz ∷ SProxy "baz"
_baz = SProxy

foo ∷ ∀ r. Variant (foo ∷ Int | r)
foo = inj _foo 42

bar ∷ ∀ r. Variant (bar ∷ String | r)
bar = inj _bar "bar"

baz ∷ ∀ r. Variant (baz ∷ Boolean | r)
baz = inj _baz true

cases ∷ { foo ∷ Int → String, bar ∷ String → String, baz ∷ Boolean → String }
cases =
  { foo: show
  , bar: \x → x <> x
  , baz: \x → if x then "TRUE" else "false"
  }

test ∷ Eff (assert ∷ ASSERT) Unit
test = do
  assert' "prj: Foo" $ prj _foo foo == Just 42
  assert' "prj: !Foo" $ prj _foo bar == Nothing ∷ Maybe Int

  assert' "foo case" $ match cases foo == "42"
  assert' "bar case" $ match cases bar == "barbar"
  assert' "baz case" $ match cases baz == "TRUE"

  assert' "mapCase" $ "1212" == mapCase (\x → x <> x) cases $$ (downcast $ variant { foo: 12 })

  assert' "adhoc cases" $ 132 == foo ## {} :+: { foo: add 90 } :+: { bar: add 12 }

  let
    case1 ∷ Variant TestVariants → String
    case1 = case_
      # on _foo (\a → "foo: " <> show a)
      # on _bar (\a → "bar: " <> a)
      # on _baz (\a → "baz: " <> show a)

  assert' "case1: foo" $ case1 foo == "foo: 42"
  assert' "case1: bar" $ case1 bar == "bar: bar"
  assert' "case1: baz" $ case1 baz == "baz: true"

  let
    case2 ∷ Variant TestVariants → String
    case2 = default "no match"
      # on _foo (\a → "foo: " <> show a)
      # on _bar (\a → "bar: " <> a)

  assert' "case2: foo" $ case2 foo == "foo: 42"
  assert' "case2: bar" $ case2 bar == "bar: bar"
  assert' "case2: baz" $ case2 baz == "no match"
