module Test.Main where

import Prelude

import Effect (Effect)
import Test.Variant as Variant
import Test.VariantEnums as VariantEnums
import Test.VariantF as VariantF

main ∷ Effect Unit
main = do
  Variant.test
  VariantF.test
  VariantEnums.test
