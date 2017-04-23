module Test.Main where

import Prelude
import Control.Monad.Eff (Eff)
import Test.Assert (ASSERT)
import Test.Variant as Variant
import Test.VariantF as VariantF

main ∷ Eff (assert ∷ ASSERT) Unit
main = do
  Variant.test
  VariantF.test
