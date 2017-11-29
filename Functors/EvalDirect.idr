module EvalDirect

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
  if x == y then (Just v) else fetch x xs

eval : Expr -> Env -> Maybe Int
eval (Var x) = \e => fetch x e
eval (Val i) = \e => Just i
eval (Add e1 e2) = \e => eval e1 e `add` eval e2 e where
  add : (x, y : Maybe Int) -> Maybe Int
  add (Just i) (Just j) = Just (i + j)
  add _ _ = Nothing

----

Env1 : Env
Env1 = [("x", 2), ("y", 3)]

run1_eq : eval (Add (Var "y") (Val 7)) Env1 = Just 10
run1_eq = Refl

run2_eq : eval (Var "z") Env1 = Nothing
run2_eq = Refl
