module Metaprog.ElabId

import Language.Reflection

%language ElabReflection

mkId : Elab ()
mkId = do intro `{{x}}
          fill (Var `{{x}})
          solve

idNat : Nat -> Nat
idNat = %runElab mkId

idUnit : () -> ()
idUnit = %runElab mkId

idString : String -> String
idString = %runElab mkId

idBool : Bool -> Bool
idBool = %runElab mkId

idNat1 : Nat -> Nat
idNat1 = %runElab (do x <- gensym "x"; intro x; fill (Var x); solve)

mkNat : Nat
mkNat = %runElab (do fill (quote (the Nat 25)); solve)
