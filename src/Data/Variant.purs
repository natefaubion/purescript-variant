module Data.Variant
  ( Variant
  , inj
  , prj
  , on
  , case_
  , match
  , flipMatch
  , (##), ($$), (:+:)
  , mapCase
  , variant
  , record
  , downcast
  , class ToFunc
  , class SingletonRowList
  , default
  , module Exports
  ) where

import Prelude

import Data.Array as A
import Data.Maybe (Maybe(..), fromJust)
import Data.StrMap as SM
import Data.Record (unionMerge)
import Data.Symbol (SProxy, class IsSymbol, reflectSymbol)
import Data.Symbol (SProxy(..)) as Exports
import Data.Tuple (Tuple(..), fst, snd)

import Partial.Unsafe (unsafeCrashWith, unsafePartial)

import Type.Row (class ListToRow, class RowToList, kind RowList, Cons, Nil)

import Unsafe.Coerce (unsafeCoerce)

data Variant (a ∷ # Type)

class SingletonRowList (rl ∷ RowList)

instance singletonRowList ∷ SingletonRowList (Cons s a Nil)

variant
  ∷ ∀ r rl
  . RowToList r rl
  ⇒ SingletonRowList rl
  ⇒ Record r
  → Variant r
variant r = coerceV $ Tuple tag val
  where
  coerceV ∷ ∀ ω. Tuple String ω → Variant r
  coerceV = unsafeCoerce

  tag ∷ String
  tag = unsafePartial fromJust $ A.head $ SM.keys $ toStrMap r

  val ∷ ∀ ω. ω
  val = unsafePartial fromJust $ A.head $ SM.values $ toStrMap r

  toStrMap ∷ ∀ ρ α. Record ρ → SM.StrMap α
  toStrMap = unsafeCoerce

record
  ∷ ∀ r rl
  . RowToList r rl
  ⇒ SingletonRowList rl
  ⇒ Variant r
  → Record r
record v = fromStrMap $ SM.singleton (fst taggedTuple) (snd taggedTuple)
  where
  taggedTuple ∷ ∀ ω. Tuple String ω
  taggedTuple = unsafeCoerce v

  fromStrMap ∷ ∀ ρ α. SM.StrMap α → Record ρ
  fromStrMap = unsafeCoerce


downcast
  ∷ ∀ r mx vr
  . Union r mx vr
  ⇒ Variant r
  → Variant vr
downcast = unsafeCoerce

class ToFunc (inp ∷ RowList) a (out ∷ RowList) | inp a → out, out a → inp

instance
  nilToFunc
  ∷ ToFunc Nil a Nil

instance
  consToFunc
  ∷ ToFunc inptail a outtail
  ⇒ ToFunc (Cons s inp inptail) a (Cons s (inp → a) outtail)

mapCase
  ∷ ∀ vr vl ar al br bl a b
  . RowToList vr vl
  ⇒ ListToRow vl vr
  ⇒ RowToList ar al
  ⇒ ListToRow al ar
  ⇒ RowToList br bl
  ⇒ ListToRow bl br
  ⇒ ToFunc vl a al
  ⇒ ToFunc vl b bl
  ⇒ (a → b)
  → Record ar
  → Record br
mapCase f cases = fromStrMap $ map (f <<< _) $ toStrMap cases
  where
  toStrMap ∷ ∀ ρ α. Record ρ → SM.StrMap α
  toStrMap = unsafeCoerce

  fromStrMap ∷ ∀ ρ α. SM.StrMap α → Record ρ
  fromStrMap = unsafeCoerce



match
  ∷ ∀ vr cr a vl cl
  . RowToList vr vl
  ⇒ RowToList cr cl
  ⇒ ListToRow cl cr
  ⇒ ListToRow vl vr
  ⇒ ToFunc vl a cl
  ⇒ Record cr
  → Variant vr
  → a
match cases var =
  let
    unCoerceV ∷ ∀ ω. Variant vr → Tuple String ω
    unCoerceV = unsafeCoerce

    tagged ∷ ∀ ω. Tuple String ω
    tagged = unCoerceV var

    unsafeGet ∷ ∀ ω. String → (ω → a)
    unsafeGet k = unsafePartial fromJust $ SM.lookup k $ unsafeCoerce cases

    func ∷ ∀ ω. ω → a
    func = unsafeGet $ fst tagged

    res = func $ snd tagged
  in res

flipMatch
  ∷ ∀ vr cr a vl cl
  . RowToList vr vl
  ⇒ RowToList cr cl
  ⇒ ListToRow cl cr
  ⇒ ListToRow vl vr
  ⇒ ToFunc vl a cl
  ⇒ Variant vr
  → Record cr
  → a
flipMatch = flip match

infixl 6 flipMatch as ##
infixr 6 match as $$
infixr 8 unionMerge as :+:


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
  ∷ ∀ sym a r1 r2
  . RowCons sym a r1 r2
  ⇒ IsSymbol sym
  ⇒ SProxy sym
  → Variant r2
  → Maybe a
prj p = on p Just (const Nothing)

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
