module MetaProg.ElabLang

import Data.Fin
import Data.Vect
import Language.Reflection
import Pruviloj.Core

%language ElabReflection

data Lang : Nat -> Type where
  V : (i : Fin n) -> Lang n
  Ap : (x, y : Lang n) -> Lang n
  Lam : (x : Lang (S n)) -> Lang n
  CstI : (x : Integer) -> Lang n
  FFI : (name : TTName) -> Lang n

exampleFun : Lang 0
exampleFun = Lam $ Lam $
  Ap (Ap (FFI `{prim__addBigInt}) (V 0)) (V 1)

elabLang : (ctxt : Vect k TTName) -> (lang : Lang k) -> Elab ()
elabLang ctxt (V i) =
  do fill (Var (index i ctxt))
     solve
elabLang ctxt (Ap x y) =
  do t1 <- newHole "t1" `(Type)
     t2 <- newHole "t2" `(Type)
     fun <- newHole "fun" `(~(Var t1) -> ~(Var t2))
     arg <- newHole "arg" (Var t1)
     fill (RApp (Var fun) (Var arg))
     solve
     focus fun; elabLang ctxt x
     focus arg; elabLang ctxt y
elabLang ctxt (Lam x) =
  do n <- gensym "argument"
     attack
     intro n
     elabLang (n :: ctxt) x
     solve
elabLang ctxt (CstI x) =
  do fill (quote x)
     solve
elabLang ctxt (FFI name) =
  do fill (Var name)
     solve

compiled : Integer -> Integer -> Integer
compiled = %runElab (elabLang [] exampleFun)

compiled_2_3 : compiled 2 3 = 5
compiled_2_3 = Refl
