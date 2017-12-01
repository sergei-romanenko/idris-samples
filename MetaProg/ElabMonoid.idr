module ElabMonoid

import Syntax.PreorderReasoning

import Language.Reflection
import Language.Reflection.Utils
import Pruviloj.Core

%language ElabReflection

%default total

----

interface IsMonoid a where
  neut : a
  op : a -> a -> a
  neutLeftId : (x : a) -> neut `op` x = x
  neutRightId : (x : a) -> x `op` neut = x
  assoc : (x, y, z : a) -> x `op` (y `op` z) = (x `op` y) `op` z

implementation IsMonoid () where
  neut = ()
  op () () = ()
  neutLeftId () = Refl
  neutRightId () = Refl
  assoc () () () = Refl

implementation [plusMonoid] IsMonoid Nat where
  neut = Z
  op = plus
  neutLeftId = plusZeroLeftNeutral
  neutRightId = plusZeroRightNeutral
  assoc = plusAssociative

implementation [multMonoid] IsMonoid Nat where
  neut = 1
  op = mult
  neutLeftId = multOneLeftNeutral
  neutRightId = multOneRightNeutral
  assoc = multAssociative

implementation IsMonoid (List a) where
  neut = []
  op = (++)
  neutLeftId _ = Refl
  neutRightId = appendNilRightNeutral
  assoc = appendAssociative

----

data MonoidExpr a =
  NEUT | LIT a | OP (MonoidExpr a) (MonoidExpr a)

interpExpr : (IsMonoid a) => MonoidExpr a -> a
interpExpr NEUT = neut
interpExpr (LIT v) = v
interpExpr (OP x y) = interpExpr x `op` interpExpr y

----

expr2 : (x, y : a) -> MonoidExpr a
expr2 x y = (OP (OP NEUT (LIT x)) (OP (LIT y) NEUT))

ie1 : interpExpr (expr2 () ()) = ()
ie1 = Refl

ie2 : interpExpr @{ElabMonoid.plusMonoid} (expr2 3 7) = 10
ie2 = Refl

ie3 : interpExpr @{ElabMonoid.multMonoid} (expr2 3 7) = 21
ie3 = Refl

ie4 : interpExpr (expr2 ["a"] ["b"] ) = ["a", "b"]
ie4 = Refl

----

interpList : (IsMonoid a) => List a -> a
interpList xs = foldr op neut xs

flattenExpr : MonoidExpr a -> List a
flattenExpr NEUT = []
flattenExpr (LIT x) = [x]
flattenExpr (OP x y) = flattenExpr x ++ flattenExpr y

opAppend : (IsMonoid a) => (xs, ys : List a) ->
  interpList xs `op` interpList ys = interpList (xs ++ ys)
opAppend [] ys =
  (interpList [] `op` interpList ys)
    ={ Refl }=
  (neut `op` interpList ys)
    ={ (neutLeftId (interpList ys)) }=
  (interpList ys)
    ={ Refl }=
  (interpList ([] ++ ys))
   QED
opAppend (x :: xs) ys =
  (interpList (x :: xs) `op` interpList ys)
    ={ Refl }=
  ((x `op` interpList xs) `op` interpList ys)
    ={ sym $ (assoc x (interpList xs) (interpList ys)) }=
  (x `op` (interpList xs `op` interpList ys))
    ={ cong {f=op x} (opAppend xs ys) }=
  (x `op` interpList (xs ++ ys))
    ={ Refl }=
  (interpList (x :: (xs ++ ys)))
    ={ Refl }=
  (interpList ((x :: xs) ++ ys))
  QED

-- `flatten` and `interpList` are correct wrt `interpExp`

flattenOk : (IsMonoid a) => (e : MonoidExpr a) ->
  interpExpr e = interpList (flattenExpr e)
flattenOk NEUT = neut QED
flattenOk (LIT v) =
  v ={ sym $ neutRightId v }= (v `op` neut) QED
flattenOk (OP x y) =
  (interpExpr (OP x y))
    ={ Refl }=
  (interpExpr x `op` interpExpr y)
    ={ cong {f=flip op (interpExpr y)} (flattenOk x) }=
  (interpList (flattenExpr x) `op` interpExpr y)
    ={ cong {f=op (interpList (flattenExpr x))} (flattenOk y) }=
  (interpList (flattenExpr x) `op` interpList (flattenExpr y))
    ={ opAppend (flattenExpr x) (flattenExpr y) }=
  (interpList (flattenExpr x ++ flattenExpr y))
    ={ Refl }=
  (interpList (flattenExpr (OP x y)))
  QED

monoidReflection : (IsMonoid a) => (x, y : MonoidExpr a) ->
  interpList (flattenExpr x) = interpList (flattenExpr y) ->
  interpExpr x = interpExpr y
monoidReflection x y prf =
  rewrite flattenOk x in
  rewrite flattenOk y in
  prf

--  Reification of monoid expressions to the custom expression type.

partial
reifyExpr : Raw -> Elab ()
reifyExpr `(op {a=~a} @{~dict} ~x ~y) =
  do [l, r] <- apply `(OP {a=~a}) [False, False]
     solve
     focus l; reifyExpr x
     focus r; reifyExpr y
reifyExpr `(neut {a=~a} @{~dict}) =
  exact `(NEUT {a=~a})
reifyExpr tm =
  do [_, h] <- apply (Var `{LIT}) [True, False]
     solve
     focus h; exact tm

-- A tactic for simplifying equalities of monoid expressions using reflection.

partial
asMonoid : (dict : Raw) -> Elab ()
asMonoid dict =
  case !goalType of
    `((=) {A=~A} {B=~B} ~e1 ~e2) =>
      do l <- gensym "L"
         r <- gensym "R"

         remember l `(MonoidExpr ~A); reifyExpr e1
         remember r `(MonoidExpr ~B); reifyExpr e2

         equiv `((=) {A=~A} {B=~B}
                     (interpExpr {a=~A} @{~dict} ~(Var l))
                     (interpExpr {a=~B} @{~dict} ~(Var r)))

         [h] <- apply `(monoidReflection {a=~A} @{~dict}
                                         ~(Var l) ~(Var r)) [True]
         solve
         focus h

----

test1 : (IsMonoid a) => (w, x, y, z : a) ->
  (( w `op` x) `op` (y `op` z)) =
    (w `op` (x `op` (y `op` (z `op` neut {a=a}))))
test1 @{dict} w x y z =
  %runElab (do asMonoid (Var `{dict}); reflexivity)
