module EvalMonad

%default total

----

data Expr
  = Var String
  | Val Int
  | Add Expr Expr

Env : Type
Env = List (String, Int)

data Eval : Type -> Type where
  MkEval : (Env -> Maybe a) -> Eval a

implementation Functor Eval where
  map f (MkEval g) = MkEval (\e => map f (g e))

implementation Applicative Eval where
  pure x = MkEval (\e => Just x)
  (MkEval f) <*> (MkEval g) = MkEval (\e => (f e) <*> (g e))

implementation Monad Eval where
  (MkEval f) >>= g = MkEval $ \e =>
    case f e of
      Nothing => Nothing
      Just x => case g x of
                    MkEval h => h e

fetch : String -> Eval Int
fetch x = MkEval fetchVal where
 fetchVal : Env -> Maybe Int
 fetchVal [] = Nothing
 fetchVal ((y, v) :: xs) =
    if x == y then (Just v) else (fetchVal xs)

eval : Expr -> Eval Int
eval (Var x) = fetch x
eval (Val i) = pure i
eval (Add e1 e2) =
  do i1 <- eval e1
     i2 <- eval e2
     pure (i1 + i2)

runEval : Expr -> Env -> Maybe Int
runEval e env = case eval e of
  MkEval f => f env

----

Env1 : Env
Env1 = [("x", 2), ("y", 3)]

run1 : runEval (Add (Var "y") (Val 7)) Env1 = Just 10
run1 = Refl

run2 : runEval (Var "z") Env1 = Nothing
run2 = Refl
