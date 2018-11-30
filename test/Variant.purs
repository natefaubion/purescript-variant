module Test.Variant where

import Prelude

import Data.List as L
import Data.Maybe (Maybe(..), isJust)
import Data.Symbol (reflectSymbol)
import Data.Variant (SProxy(..), Unvariant(..), Variant, case_, contract, default, expand, inj, mapAll, mapSome, mapSomeExpand, match, on, onMatch, prj, revariant, unvariant)
import Effect (Effect)
import Record.Builder (build, modify, Builder)
import Test.Assert (assert')

type TestVariants =
  ( foo ∷ Int
  , bar ∷ String
  , baz ∷ Boolean
  )

type TestVariants' =
  ( foo ∷ String
  , bar ∷ String
  , baz ∷ String
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

modifyRec ∷ Builder (Record TestVariants) (Record TestVariants)
modifyRec = setVariant foo >>> setVariant bar >>> setVariant baz
  where
  setVariant
    ∷ Variant TestVariants
    → Builder (Record TestVariants) (Record TestVariants)
  setVariant var = case unvariant var of
    Unvariant f → f \s v → modify s (const v)

completeness ∷ ∀ r. Variant r → Variant r
completeness = revariant <<< unvariant

recBefore ∷ Record TestVariants
recBefore = { foo: 0, bar: "", baz: false }

recAfter ∷ Record TestVariants
recAfter = build modifyRec recBefore

test ∷ Effect Unit
test = do
  assert' "prj: Foo" $ prj _foo foo == Just 42
  assert' "prj: !Foo" $ prj _foo bar == Nothing ∷ Maybe Int

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

  let
    match' ∷ Variant TestVariants → String
    match' = match
      { foo: \a → "foo: " <> show a
      , bar: \a → "bar: " <> a
      , baz: \a → "baz: " <> show a
      }

  assert' "match: foo" $ match' foo == "foo: 42"
  assert' "match: bar" $ match' bar == "bar: bar"
  assert' "match: baz" $ match' baz == "baz: true"

  let
    mapSome' ∷ Variant TestVariants → Variant TestVariants'
    mapSome' = mapSome
      { foo: \a → show a
      , baz: \a → show a
      } expand

    mapSomeExpand' ∷ forall r.
      Variant ( foo ∷ Int, baz ∷ Boolean | r ) →
      Variant ( foo ∷ String, baz ∷ String | r )
    mapSomeExpand' = mapSomeExpand
      { foo: \a → show a
      , baz: \a → show a
      }

    mapAll' ∷ Variant TestVariants → Variant TestVariants'
    mapAll' = mapAll
      { foo: identity show
      , bar: identity identity
      , baz: identity show
      }

    onMatch' ∷ Variant TestVariants' → String
    onMatch' = case_
      # onMatch
        { foo: \a → "foo: " <> a
        , bar: \a → "bar: " <> a
        }
      # onMatch
        { baz: \a → "baz: " <> a
        }

  assert' "onMatch mapSome: foo" $ onMatch' (mapSome' foo) == "foo: 42"
  assert' "onMatch mapSome: bar" $ onMatch' (mapSome' bar) == "bar: bar"
  assert' "onMatch mapSome: baz" $ onMatch' (mapSome' baz) == "baz: true"

  assert' "onMatch mapSomeExpand: foo" $ onMatch' (mapSomeExpand' foo) == "foo: 42"
  assert' "onMatch mapSomeExpand: bar" $ onMatch' (mapSomeExpand' bar) == "bar: bar"
  assert' "onMatch mapSomeExpand: baz" $ onMatch' (mapSomeExpand' baz) == "baz: true"

  assert' "onMatch mapAll: foo" $ onMatch' (mapAll' foo) == "foo: 42"
  assert' "onMatch mapAll: bar" $ onMatch' (mapAll' bar) == "bar: bar"
  assert' "onMatch mapAll: baz" $ onMatch' (mapAll' baz) == "baz: true"

  assert' "eq: foo" $ (foo ∷ Variant TestVariants) == foo
  assert' "eq: bar" $ (bar ∷ Variant TestVariants) == bar
  assert' "eq: baz" $ (baz ∷ Variant TestVariants) == baz
  assert' "notEq: foo" $ (foo ∷ Variant TestVariants) /= inj _foo 53
  assert' "notEq: bar" $ (foo ∷ Variant TestVariants) /= bar

  assert' "compare: foo EQ" $ compare (foo ∷ Variant TestVariants) foo == EQ
  assert' "compare: foo LT" $ compare (foo ∷ Variant TestVariants) (inj _foo 53) == LT
  assert' "compare: foo GT" $ compare (foo ∷ Variant TestVariants) (inj _foo 12) == GT
  assert' "compare: LT" $ compare bar (foo ∷ Variant TestVariants) == LT
  assert' "compare: GT" $ compare (foo ∷ Variant TestVariants) bar == GT

  assert' "contract: pass"
    $ isJust
    $ contract (foo ∷ Variant TestVariants) ∷ Maybe (Variant (foo ∷ Int))

  assert' "contract: fail"
    $ L.null
    $ contract (bar ∷ Variant TestVariants) ∷ L.List (Variant (foo ∷ Int))

  assert' "show" $ show (foo ∷ Variant TestVariants) ==  """(inj @"foo" 42)"""

  assert' "unvariant: foo" $
    let Unvariant f = unvariant (foo ∷ Variant TestVariants)
    in f \s _ → reflectSymbol s == "foo"

  assert' "unvariant: build record (foo)" $ recAfter.foo == 42
  assert' "unvariant: build record (bar)" $ recAfter.bar == "bar"
  assert' "unvariant: build record (baz)" $ recAfter.baz == true
