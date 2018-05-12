module Test.VariantEnums where

import Prelude

import Data.Enum (Cardinality(..), cardinality, succ, pred, toEnum, fromEnum)
import Data.Maybe (Maybe(..))
import Data.Variant (SProxy(..), Variant, inj)
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

_a = SProxy ∷ SProxy "a"
_b = SProxy ∷ SProxy "b"
_c = SProxy ∷ SProxy "c"

test ∷ Effect Unit
test = do
  assert' "bottom: T" $ inj _a unit == (bottom ∷ T)
  assert' "top: T" $ inj _c unit == (top ∷ T)
  assert' "succ bottom: T" $ Just (inj _b unit) == succ (bottom ∷ T)
  assert' "succ: T" $ Just (inj _c unit) == succ (inj _b unit ∷ T)
  assert' "succ top: T" $ Nothing == succ (inj _c unit ∷ T)
  assert' "pred bottom: T" $ Nothing == pred (bottom ∷ T)
  assert' "pred: T" $ Just (inj _a unit) == pred (inj _b unit ∷ T)
  assert' "pred top: T" $ Just (inj _b unit) == pred (top ∷ T)
  assert' "fromEnum bottom: T" $ 0 == fromEnum (bottom ∷ T)
  assert' "fromEnum: T" $ 1 == fromEnum (inj _b unit ∷ T)
  assert' "fromEnum top: T" $ 2 == fromEnum (top ∷ T)
  assert' "toEnum: T 0" $ toEnum 0 == Just (inj _a unit ∷ T)
  assert' "toEnum: T 1" $ toEnum 1 == Just (inj _b unit ∷ T)
  assert' "toEnum: T 2" $ toEnum 2 == Just (inj _c unit ∷ T)
  assert' "toEnum: T 3" $ toEnum 3 == (Nothing ∷ Maybe T)
  assert' "cardinality: T" $ Cardinality 3 == (cardinality ∷ Cardinality T)

  assert' "bottom: TT" $ inj _a (inj _a unit) == (bottom ∷ TT)
  assert' "top: TT" $ inj _c (inj _c unit) == (top ∷ TT)
  assert' "succ bottom: TT" $ (Just (inj _a (inj _b unit))) == succ (bottom ∷ TT)
  assert' "succ top: TT" $ Nothing == succ (top ∷ TT)
  assert' "succ: medium top TT" $ Just (inj _b bottom) == succ (inj _a top ∷ TT)
  assert' "pred: medium bottom TT" $ Just (inj _a top) == pred (inj _b bottom ∷ TT)
  assert' "cardinality: TT" $ Cardinality 9 == (cardinality ∷ Cardinality TT)
  assert' "fromEnum: TT 0" $ 0 == fromEnum (inj _a (inj _a unit) ∷ TT)
  assert' "fromEnum: TT 3" $ 3 == fromEnum (inj _b (inj _a unit) ∷ TT)
  assert' "fromEnum: TT 8" $ 8 == fromEnum (inj _c (inj _c unit) ∷ TT)
  assert' "fromEnum: TT 4" $ 4 == fromEnum (inj _b (inj _b unit) ∷ TT)
  assert' "toEnum: TT 0" $ toEnum 0 == Just (inj _a (inj _a unit) ∷ TT)
  assert' "toEnum: TT 1" $ toEnum 1 == Just (inj _a (inj _b unit) ∷ TT)
  assert' "toEnum: TT 3" $ toEnum 3 == Just (inj _b (inj _a unit) ∷ TT)
  assert' "toEnum: TT 5" $ toEnum 5 == Just (inj _b (inj _c unit) ∷ TT)
  assert' "toEnum: TT 6" $ toEnum 6 == Just (inj _c (inj _a unit) ∷ TT)
  assert' "toEnum: TT 8" $ toEnum 8 == Just (inj _c (inj _c unit) ∷ TT)
  assert' "toEnum: TT 9" $ toEnum 9 == (Nothing ∷ Maybe TT)
