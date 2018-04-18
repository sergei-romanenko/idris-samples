module ExprDsl

%language DSLNotation
%default total

-- Types.

infixr 1 ->>

data Ty : Type where
  INT : Ty
  BOOL : Ty
  (->>) : (u, v : Ty) -> Ty

Basis : Type
Basis = List Ty

interpTy : Ty -> Type
interpTy INT      = Int
interpTy BOOL     = Bool
interpTy (s ->> t) = interpTy s -> interpTy t

-- Expressions.

data Env : (g : Basis) -> Type where
  Nil  : Env Nil
  (::) : (x : interpTy u) -> (r : Env g) -> Env (u :: g)

data Vr : Basis -> Ty -> Type where
  VZ : Vr (u :: g) u
  VS : (i : Vr g u) -> Vr (v :: g) u

lookup : (i : Vr g u) -> (r : Env g) -> interpTy u
lookup VZ (x :: r) = x
lookup (VS i) (x :: r) = lookup i r

data Expr : (g : Basis) -> (w : Ty) -> Type where
  Var : (i : Vr g u) -> Expr g u
  Val : (n : Int) -> Expr g INT
  Lam : (e0 : Expr (u :: g) w) -> Expr g (u ->> w)
  App : (e1 : Lazy (Expr g (u ->> w))) -> (e2 : Expr g u) -> Expr g w
  Op  : (f : interpTy u -> interpTy v -> interpTy w) ->
        (e1 : Expr g u) -> (e2 : Expr g v) -> Expr g w
  If  : (e0 : Expr g BOOL) -> (e1 : Expr g w) -> (e2 : Expr g w) -> Expr g w
  Bind : (e0 : Expr g u) -> (f : interpTy u -> Expr g v) -> Expr g v

-- Interpreter.

interp : %static (e : Expr g w) -> (r : Env g) -> interpTy w
interp (Var i) r = lookup i r
interp (Val n) r = n
interp (Lam e0) r = \x => interp e0 (x :: r)
interp (App e1 e2) r = (interp e1 r) (interp e2 r)
interp (Op f e1 e2) r = f (interp e1 r) (interp e2 r)
interp (If e0 e1 e2) r = if interp e0 r then interp e1 r else interp e2 r
interp (Bind e0 f) r = interp (f (interp e0 r)) r

-- Syntax.

%static
lam_ : (name : TTName) -> (e : Expr (u :: g) w) -> Expr g (u ->> w)
lam_ name = Lam

dsl expr
    lambda = lam_
    variable = Var
    index_first = VZ
    index_next = VS

(<*>) : Lazy (Expr g (u ->> w)) -> Expr g u -> Expr g w
(<*>) = \f, a => App f a

pure : Expr g a -> Expr g a
pure = id

syntax IF [e0] THEN [e1] ELSE [e2] = If e0 e1 e2

(==) : Expr g INT -> Expr g INT -> Expr g BOOL
(==) = Op (==)

(<) : Expr g INT -> Expr g INT -> Expr g BOOL
(<) = Op (<)

implementation Num (Expr g INT) where
  (+) e1 e2 = Op (+) e1 e2
  (*) e1 e2 = Op (*) e1 e2

  fromInteger = Val . fromInteger

implementation Neg (Expr g INT) where
  (-) e1 e2 = Op (-) e1 e2
  --abs e = IF (e < 0) THEN (-e) ELSE e
  negate e = Op (-) 0 e

-- Examples.

eI : Expr g (w ->> w)
eI = expr (\x => x)

eK : Expr g (u ->> v ->> u)
eK = expr (\x, y => x)

eS : Expr g ((u ->> v ->> w) ->> (u ->> v) ->> u ->> w)
eS = expr (\x, y, z => [| [|x z|] [|y z|] |])

eAdd : Expr g (INT ->> INT ->> INT)
eAdd = expr (\x, y => x + y)

eDouble : Expr [] (INT ->> INT)
eDouble = expr (\x => App (App eAdd x) (Var VZ))

partial
eFac : Expr g (INT ->> INT)
eFac = expr (\x => IF x == 0 THEN 1 ELSE [| eFac (x - 1) |] * x)

partial
testFac : Int
testFac = interp eFac [] 4

partial
eFac' : Expr g (INT ->> INT)
eFac' = expr (\x =>
  If (Op (==) x (Val 0))
     (Val 1)
     (Op (*) (App eFac' (Op (-) x (Val 1))) x))

partial
testFac' : Int
testFac' = interp eFac' [] 4

{-
λΠ> :printdef testFac'
testFac' : Int
testFac' = PE_interp_eba5348f [] (PE_fromInteger_d6648df 4)
λΠ> :printdef PE_interp_eba5348f
PE_interp_eba5348f : Env g -> Int -> Int
PE_interp_eba5348f (3arg) = \x =>
  ifThenElse (PE_==_ba2f651f x (PE_fromInteger_d6648df 0))
    (Delay (PE_fromInteger_d6648df 1))
    (Delay (PE_*_ba2f651f (PE_interp_eba5348f (x :: (3arg))
                          (PE_-_ba2f651f x (PE_fromInteger_d6648df 1))) x))
-}
