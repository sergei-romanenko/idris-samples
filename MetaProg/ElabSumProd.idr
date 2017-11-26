module MetaProg.ElabSumProd

import Language.Reflection
import Pruviloj.Core

%language ElabReflection

%default total

autoSumProd : Elab ()
autoSumProd =
  do g <- goalType
     mkProof g
  where

  mkProof : Raw -> Elab ()
  mkProof `(() : Type) =
    exact `(() : ())
  mkProof `((~a, ~b) : Type) =
    do ha <- newHole "ha" a
       hb <- newHole "hb" b
       exact `(MkPair {A=~a} {B=~b} ~(Var ha) ~(Var hb))
       focus ha; mkProof a
       focus hb; mkProof b
  mkProof `(Either ~a ~b) =
    left a b <|> right a b
    where
    left : Raw -> Raw -> Elab ()
    left a b =
      do ha <- newHole "ha" a
         exact `(Left {a=~a} {b=~b} ~(Var ha))
         focus ha; mkProof a

    right : Raw -> Raw -> Elab ()
    right a b =
      do hb <- newHole "hb" b
         exact `(Right {a=~a} {b=~b} ~(Var hb))
         focus hb; mkProof b
  mkProof g =
    fail [ NamePart `{autoSumProd}, TextPart "can't solve the goal", RawPart g ]

test1 : the Type ()
test1 = %runElab autoSumProd

test2 : the Type ((), ())
test2 = %runElab autoSumProd

test3 : Either Void ()
test3 = %runElab autoSumProd

test4 : Either Void (Either Void ())
test4 = %runElab autoSumProd

--test5 : Either Void (Either Void Void)
--test5 = %runElab autoSumProd
