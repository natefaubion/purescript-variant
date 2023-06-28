module Test.VariantEnums where

import Prelude

import Data.Enum (Cardinality(..), cardinality, succ, pred, toEnum, fromEnum)
import Data.Maybe (Maybe(..))
import Data.Variant (Variant, inj)
import Effect (Effect)
import Test.Assert (assert')

type T = Variant
  ( a ∷ Unit
  , b ∷ Unit
  , c ∷ Unit
  )

type TT = Variant
  ( a ∷ T
  , b ∷ T
  , c ∷ T
  )

test ∷ Effect Unit
test = do
  assert' "bottom: T" $ inj @"a" unit == (bottom ∷ T)
  assert' "top: T" $ inj @"c" unit == (top ∷ T)
  assert' "succ bottom: T" $ Just (inj @"b" unit) == succ (bottom ∷ T)
  assert' "succ: T" $ Just (inj @"c" unit) == succ (inj @"b" unit ∷ T)
  assert' "succ top: T" $ Nothing == succ (inj @"c" unit ∷ T)
  assert' "pred bottom: T" $ Nothing == pred (bottom ∷ T)
  assert' "pred: T" $ Just (inj @"a" unit) == pred (inj @"b" unit ∷ T)
  assert' "pred top: T" $ Just (inj @"b" unit) == pred (top ∷ T)
  assert' "fromEnum bottom: T" $ 0 == fromEnum (bottom ∷ T)
  assert' "fromEnum: T" $ 1 == fromEnum (inj @"b" unit ∷ T)
  assert' "fromEnum top: T" $ 2 == fromEnum (top ∷ T)
  assert' "toEnum: T 0" $ toEnum 0 == Just (inj @"a" unit ∷ T)
  assert' "toEnum: T 1" $ toEnum 1 == Just (inj @"b" unit ∷ T)
  assert' "toEnum: T 2" $ toEnum 2 == Just (inj @"c" unit ∷ T)
  assert' "toEnum: T 3" $ toEnum 3 == (Nothing ∷ Maybe T)
  assert' "cardinality: T" $ Cardinality 3 == (cardinality ∷ Cardinality T)

  assert' "bottom: TT" $ inj @"a" (inj @"a" unit) == (bottom ∷ TT)
  assert' "top: TT" $ inj @"c" (inj @"c" unit) == (top ∷ TT)
  assert' "succ bottom: TT" $ (Just (inj @"a" (inj @"b" unit))) == succ (bottom ∷ TT)
  assert' "succ top: TT" $ Nothing == succ (top ∷ TT)
  assert' "succ: medium top TT" $ Just (inj @"b" bottom) == succ (inj @"a" top ∷ TT)
  assert' "pred: medium bottom TT" $ Just (inj @"a" top) == pred (inj @"b" bottom ∷ TT)
  assert' "cardinality: TT" $ Cardinality 9 == (cardinality ∷ Cardinality TT)
  assert' "fromEnum: TT 0" $ 0 == fromEnum (inj @"a" (inj @"a" unit) ∷ TT)
  assert' "fromEnum: TT 3" $ 3 == fromEnum (inj @"b" (inj @"a" unit) ∷ TT)
  assert' "fromEnum: TT 8" $ 8 == fromEnum (inj @"c" (inj @"c" unit) ∷ TT)
  assert' "fromEnum: TT 4" $ 4 == fromEnum (inj @"b" (inj @"b" unit) ∷ TT)
  assert' "toEnum: TT 0" $ toEnum 0 == Just (inj @"a" (inj @"a" unit) ∷ TT)
  assert' "toEnum: TT 1" $ toEnum 1 == Just (inj @"a" (inj @"b" unit) ∷ TT)
  assert' "toEnum: TT 3" $ toEnum 3 == Just (inj @"b" (inj @"a" unit) ∷ TT)
  assert' "toEnum: TT 5" $ toEnum 5 == Just (inj @"b" (inj @"c" unit) ∷ TT)
  assert' "toEnum: TT 6" $ toEnum 6 == Just (inj @"c" (inj @"a" unit) ∷ TT)
  assert' "toEnum: TT 8" $ toEnum 8 == Just (inj @"c" (inj @"c" unit) ∷ TT)
  assert' "toEnum: TT 9" $ toEnum 9 == (Nothing ∷ Maybe TT)
