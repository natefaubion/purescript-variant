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
  , UnvariantF(..)
  , UnvariantF'
  , unvariantF
  , revariantF
  , class VariantFShows, variantFShows
  , class TraversableVFRL
  , class FoldableVFRL
  , traverseVFRL
  , foldrVFRL
  , foldlVFRL
  , foldMapVFRL
  , module Exports
  ) where

import Prelude

import Control.Alternative (class Alternative, empty)
import Data.List as L
import Data.Symbol (SProxy(..)) as Exports
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Traversable as TF
import Data.Variant.Internal (class Contractable, FProxy(..), class VariantFMatchCases) as Exports
import Data.Variant.Internal (class Contractable, class VariantFMatchCases, class VariantTags, VariantFCase, VariantCase, contractWith, lookup, unsafeGet, unsafeHas, variantTags)
import Partial.Unsafe (unsafeCrashWith)
import Prim.Row as R
import Prim.RowList as RL
import Type.Equality (class TypeEquals)
import Type.Proxy (Proxy(..))
import Type.Proxy (Proxy(..)) as Exports
import Unsafe.Coerce (unsafeCoerce)

newtype VariantFRep f a = VariantFRep
  { type ∷ String
  , value ∷ f a
  , map ∷ ∀ x y. (x → y) → f x → f y
  }

data UnknownF :: Type -> Type
data UnknownF a

data VariantF :: Row (Type -> Type) -> Type -> Type
data VariantF f a

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

class FoldableVFRL :: RL.RowList (Type -> Type) -> Row (Type -> Type) -> Constraint
class FoldableVFRL rl row | rl -> row where
  foldrVFRL :: forall proxy a b. proxy rl -> (a -> b -> b) -> b -> VariantF row a -> b
  foldlVFRL :: forall proxy a b. proxy rl -> (b -> a -> b) -> b -> VariantF row a -> b
  foldMapVFRL :: forall proxy a m. Monoid m => proxy rl -> (a -> m) -> VariantF row a -> m

instance foldableNil :: FoldableVFRL RL.Nil () where
  foldrVFRL _ _ _ = case_
  foldlVFRL _ _ _ = case_
  foldMapVFRL _ _ = case_

instance foldableCons ::
  ( IsSymbol k
  , TF.Foldable f
  , FoldableVFRL rl r
  , R.Cons k f r r'
  ) => FoldableVFRL (RL.Cons k f rl) r' where
  foldrVFRL _ f b = on k (TF.foldr f b) (foldrVFRL (Proxy :: Proxy rl) f b)
    where k = Proxy :: Proxy k
  foldlVFRL _ f b = on k (TF.foldl f b) (foldlVFRL (Proxy :: Proxy rl) f b)
    where k = Proxy :: Proxy k
  foldMapVFRL _ f = on k (TF.foldMap f) (foldMapVFRL (Proxy :: Proxy rl) f)
    where k = Proxy :: Proxy k

class TraversableVFRL :: RL.RowList (Type -> Type) -> Row (Type -> Type) -> Constraint
class FoldableVFRL rl row <= TraversableVFRL rl row | rl -> row where
  traverseVFRL :: forall proxy f a b. Applicative f => proxy rl -> (a -> f b) -> VariantF row a -> f (VariantF row b)

instance traversableNil :: TraversableVFRL RL.Nil () where
  traverseVFRL _ f = case_

instance traversableCons ::
  ( IsSymbol k
  , TF.Traversable f
  , TraversableVFRL rl r
  , R.Cons k f r r'
  , R.Union r rx r'
  ) => TraversableVFRL (RL.Cons k f rl) r' where
  traverseVFRL _ f = on k (TF.traverse f >>> map (inj k))
    (traverseVFRL (Proxy :: Proxy rl) f >>> map expand)
    where k = Proxy :: Proxy k

instance foldableVariantF ::
  (RL.RowToList row rl, FoldableVFRL rl row) =>
  TF.Foldable (VariantF row) where
    foldr = foldrVFRL (Proxy :: Proxy rl)
    foldl = foldlVFRL (Proxy :: Proxy rl)
    foldMap = foldMapVFRL (Proxy :: Proxy rl)

instance traversableVariantF ::
  (RL.RowToList row rl, TraversableVFRL rl row) =>
  TF.Traversable (VariantF row) where
    traverse = traverseVFRL (Proxy :: Proxy rl)
    sequence = TF.sequenceDefault

-- | Inject into the variant at a given label.
-- | ```purescript
-- | maybeAtFoo :: forall r. VariantF (foo :: FProxy Maybe | r) Int
-- | maybeAtFoo = inj (Proxy :: Proxy "foo") (Just 42)
-- | ```
inj
  ∷ ∀ proxy sym f a r1 r2
  . R.Cons sym f r1 r2
  ⇒ IsSymbol sym
  ⇒ Functor f
  ⇒ proxy sym
  → f a
  → VariantF r2 a
inj p value = coerceV $ VariantFRep { type: reflectSymbol p, value, map }
  where
  coerceV ∷ VariantFRep f a → VariantF r2 a
  coerceV = unsafeCoerce

-- | Attempt to read a variant at a given label.
-- | ```purescript
-- | case prj (Proxy :: Proxy "foo") maybeAtFoo of
-- |   Just (Just i) -> i + 1
-- |   _ -> 0
-- | ```
prj
  ∷ ∀ proxy sym f a r1 r2 g
  . R.Cons sym f r1 r2
  ⇒ Alternative g
  ⇒ IsSymbol sym
  ⇒ proxy sym
  → VariantF r2 a
  → g (f a)
prj p = on p pure (const empty)

-- | Attempt to read a variant at a given label by providing branches.
-- | The failure branch receives the provided variant, but with the label
-- | removed.
on
  ∷ ∀ proxy sym f a b r1 r2
  . R.Cons sym f r1 r2
  ⇒ IsSymbol sym
  ⇒ proxy sym
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
  . RL.RowToList r rl
  ⇒ VariantFMatchCases rl r1 a b
  ⇒ R.Union r1 r2 r3
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
-- |  # on (Proxy :: Proxy "foo") (\foo -> "Foo: " <> maybe "nothing" show foo)
-- |  # on (Proxy :: Proxy "bar") (\bar -> "Bar: " <> show (snd bar))
-- |  # on (Proxy :: Proxy "baz") (\baz -> "Baz: " <> either id show baz)
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
  . RL.RowToList r rl
  ⇒ VariantFMatchCases rl r1 a b
  ⇒ R.Union r1 () r2
  ⇒ Record r
  → VariantF r2 a
  → b
match r = case_ # onMatch r

-- | Combinator for partial matching with a default value in case of failure.
-- | ```purescript
-- | caseFn :: forall r. VariantF (foo :: FProxy Maybe, bar :: FProxy (Tuple String) | r) Int -> String
-- | caseFn = default "No match"
-- |  # on (Proxy :: Proxy "foo") (\foo -> "Foo: " <> maybe "nothing" show foo)
-- |  # on (Proxy :: Proxy "bar") (\bar -> "Bar: " <> show (snd bar))
-- | ```
default ∷ ∀ a b r. a → VariantF r b → a
default a _ = a

-- | Every `VariantF lt a` can be cast to some `VariantF gt a` as long as `lt` is a
-- | subset of `gt`.
expand
  ∷ ∀ lt mix gt a
  . R.Union lt mix gt
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
    (Proxy ∷ Proxy gt)
    (Proxy ∷ Proxy lt)
    (case coerceV v of VariantFRep v' → v'.type)
    (coerceR v)
  where
  coerceV ∷ ∀ g. VariantF gt a → VariantFRep g a
  coerceV = unsafeCoerce

  coerceR ∷ VariantF gt a → VariantF lt a
  coerceR = unsafeCoerce

type UnvariantF' r a x =
  ∀ proxy s f o
  . IsSymbol s
  ⇒ R.Cons s f o r
  ⇒ Functor f
  ⇒ proxy s
  → f a
  → x

newtype UnvariantF r a = UnvariantF
  (∀ x. UnvariantF' r a x → x)

-- | A low-level eliminator which reifies the `IsSymbol`, `Cons` and
-- | `Functor` constraints require to reconstruct the Variant. This
-- | lets you work generically with some VariantF at runtime.
unvariantF
  ∷ ∀ r a
  . VariantF r a
  → UnvariantF r a
unvariantF v = case (unsafeCoerce v ∷ VariantFRep UnknownF Unit) of
  VariantFRep o →
    UnvariantF \f →
      coerce f
        { reflectSymbol: const o.type }
        {}
        { map: o.map }
        Proxy
        o.value
  where
  coerce
    ∷ ∀ proxy x
    . UnvariantF' r a x
    → { reflectSymbol ∷ proxy "" → String }
    → {}
    → { map ∷ ∀ a b. (a → b) → UnknownF a → UnknownF b }
    → proxy ""
    → UnknownF Unit
    → x
  coerce = unsafeCoerce

-- | Reconstructs a VariantF given an UnvariantF eliminator.
revariantF ∷ ∀ r a. UnvariantF r a -> VariantF r a
revariantF (UnvariantF f) = f inj

class VariantFShows :: RL.RowList (Type -> Type) -> Type -> Constraint
class VariantFShows rl x where
  variantFShows ∷ forall proxy1 proxy2. proxy1 rl → proxy2 x → L.List (VariantCase → String)

instance showVariantFNil ∷ VariantFShows RL.Nil x where
  variantFShows _ _ = L.Nil

instance showVariantFCons ∷ (VariantFShows rs x, TypeEquals a f, Show (f x), Show x) ⇒ VariantFShows (RL.Cons sym a rs) x where
  variantFShows _ p =
    L.Cons (coerceShow show) (variantFShows (Proxy ∷ Proxy rs) p)
    where
    coerceShow ∷ (f x → String) → VariantCase → String
    coerceShow = unsafeCoerce

instance showVariantF ∷ (RL.RowToList r rl, VariantTags rl, VariantFShows rl a, Show a) ⇒ Show (VariantF r a) where
  show v1 =
    let
      VariantFRep v = unsafeCoerce v1 ∷ VariantFRep VariantFCase a
      tags = variantTags (Proxy ∷ Proxy rl)
      shows = variantFShows (Proxy ∷ Proxy rl) (Proxy ∷ Proxy a)
      body = lookup "show" v.type tags shows (unsafeCoerce v.value ∷ VariantCase)
    in
      "(inj @" <> show v.type <> " " <> body <> ")"
