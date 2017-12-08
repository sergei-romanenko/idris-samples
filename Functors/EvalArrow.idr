module EvalArrow

import Data.Morphisms
import Control.Category
import Control.Arrow

%default total

----

data Expr
  = Var String
  | Val Int
  | Add Expr Expr

Env : Type
Env = List (String, Int)

fetch : String -> Env -> Maybe Int
fetch x [] = Nothing
fetch x ((y, v) :: xs) =
  if x == y then (Just v) else (fetch x xs)

eval : Expr -> Morphism Env (Maybe Int)
eval (Var x) = Mor (fetch x)
eval (Val i) = pure (Just i)
eval (Add e1 e2) =
  eval e1 &&& eval e2 >>> (Mor $ uncurry $ liftA2 (+))

runEval : Expr -> Env -> Maybe Int
runEval e env = case eval e of
  Mor f => f env

----

Env1 : Env
Env1 = [("x", 2), ("y", 3)]

run1 : runEval (Add (Var "y") (Val 7)) Env1 = Just 10
run1 = Refl

run2 : runEval (Var "z") Env1 = Nothing
run2 = Refl
