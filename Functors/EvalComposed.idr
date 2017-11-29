module EvalComposed

%default total

----

data Fn : (a, b : Type) -> Type where
  MkFn : (a -> b) -> Fn a b

implementation Functor (Fn a) where
  map f (MkFn g) = MkFn (f . g)

implementation Applicative (Fn a) where
  pure x = MkFn (\z => x)
  (MkFn x) <*> (MkFn y) = MkFn (\z => (x z) (y z))

----

data Comp : (f, g : Type -> Type) -> (a : Type) -> Type where
  MkComp : (f (g a)) -> Comp f g a

implementation (Functor f, Functor g) => Functor (Comp f g) where
  map h (MkComp x) = MkComp (map (map h) x)

implementation (Applicative f, Applicative g) => Applicative (Comp f g) where
  pure x = MkComp (pure (pure x))
  (<*>) (MkComp x) (MkComp y) = MkComp (liftA2 (<*>) x y)
    -- MkComp ((<*>) x <*> y)

----

CLMN : Type
CLMN = Comp List Maybe Nat

Clmn1 : CLMN
Clmn1 = MkComp [Just 3, Nothing, Just 7]

Clmn2 : CLMN
Clmn2 = MkComp [Nothing, Just 2, Nothing, Just 5]

clmn12_eq : liftA2 (+) Clmn1 Clmn2 =
  MkComp [Nothing, Just 5, Nothing, Just 8, Nothing, Nothing,
          Nothing, Nothing, Nothing, Just 9, Nothing, Just 12]
clmn12_eq = Refl

Clmn3 : Comp List Maybe (Nat -> Nat)
Clmn3 = MkComp [Just (plus 2), Just (plus 3)]

clmn3_clmn1_eq : Clmn3 <*> Clmn1 =
  MkComp [Just 5, Nothing, Just 9, Just 6, Nothing, Just 10]
clmn3_clmn1_eq = Refl

----

data Expr
  = Var String
  | Val Int
  | Add Expr Expr

Env : Type
Env = List (String, Int)

Eval : Type -> Type
Eval = Comp (Fn Env) Maybe

fetch : String -> Eval Int
fetch x = MkComp (MkFn fetchVal) where
  fetchVal : Env -> Maybe Int
  fetchVal [] = Nothing
  fetchVal ((y, v) :: xs) =
    if x == y then (Just v) else (fetchVal xs)

eval : Expr -> Eval Int
eval (Var x) = fetch x
eval (Val i) = [| i |] -- pure i
eval (Add e1 e2) = [| eval e1 + eval e2 |]
  -- (+) <$> (eval e1) <*> (eval e2)

runEval : Expr -> Env -> Maybe Int
runEval e env = case eval e of
    MkComp (MkFn f) => f env

----

Env1 : Env
Env1 = [("x", 2), ("y", 3)]

run1 : runEval (Add (Var "y") (Val 7)) Env1 = Just 10
run1 = Refl

run2 : runEval (Var "z") Env1 = Nothing
run2 = Refl
