module Partial.Until

%default total

-- We just say to the Idris compiler that `until` is partial.

parameters (p : a -> Bool, f : a -> a)

  mutual

    partial
    pUntil : (x : a) -> a
    pUntil x = pUntil' x (p x)

    partial
    pUntil' : (x : a) -> (px : Bool) -> a
    pUntil' x True = x
    pUntil' x False = pUntil (f x)

-- If we are lucky, `find` terminates (at run-time).
-- λΠ> pUntil ge3 S 0
-- 3 : Nat

-- Applying Bove & Capretta's technique in a straightforward way,
-- we get the following solution.

mutual

  data Until : (p : a -> Bool) -> (f : a -> a) -> (x : a) -> Type where
    A0 : Until' p f x (p x) -> Until p f x

  data Until' : (p : a -> Bool) -> (f : a -> a) -> (x : a) -> Bool -> Type where
    B0 : Until' p f x True
    B1 : Until p f (f x) -> Until' p f x False

parameters (p : a -> Bool , f : a -> a)

  mutual

    until : (x : a) -> (h : Until p f x) -> a
    until x (A0 h) = until' x (p x) h

    until' : (x : a) -> (b : Bool) -> (h : Until' p f x b) -> a
    until' x True B0 = x
    until' x False (B1 h) = until (f x) h

  mutual

    until_correct : (x : a) -> (h : Until p f x) ->
      p (until x h) = True
    until_correct x (A0 h) = until_correct' x h

    until_correct' : (x : a) -> (h : Until' p f x (p x)) ->
      p (until' x (p x) h) = True
    until_correct' x h with (p x) proof px
      until_correct' x B0 | True = sym $ px
      until_correct' x (B1 h) | False = until_correct (f x) h


until_ge3 : Until (3 <=) S 0
until_ge3 = A0 (B1 (A0 (B1 (A0 (B1 (A0 B0))))))

until_ge3_eq_3 : until (3 <=) S 0 Until.until_ge3 = 3
until_ge3_eq_3 = Refl

-- We just say to the Agda compiler that `pdUntil` is partial.

parameters (P : a -> Type , isP : (x : a) -> Dec (P x) , f : a -> a)

  mutual

    partial
    pdUntil : (x : a) -> DPair a P
    pdUntil x = pdUntil' x (isP x)

    partial
    pdUntil' : (x : a) -> (px : Dec (P x)) -> DPair a P
    pdUntil' x (Yes px) = (x ** px)
    pdUntil' x (No npx) = pdUntil (f x)

-- If we are lucky, `until` terminates (here - at compile time).

-- λΠ> pdUntil (LTE 3) (isLTE 3) S 0
-- (3 ** LTESucc (LTESucc (LTESucc LTEZero))) : (z : Nat ** LTE 3 z)

using (a : Type, P : a -> Type)

  mutual

    data DUntil :
         (isP : (x : a) -> Dec (P x)) -> (f : a -> a) -> (x : a) -> Type where
      DA0 : DUntil' isP f x (isP x) -> DUntil isP f x

    data DUntil' :
         (isP : (x : a) -> Dec (P x)) -> (f : a -> a) -> 
         (x : a) -> (px : Dec (P x)) -> Type where
      DB0 : DUntil' isP f x (Yes px)
      DB1 : DUntil isP f (f x) -> DUntil' isP f x (No npn)

mutual

  dUntil : {P : a -> Type} -> (isP : (x : a) -> Dec (P x)) -> (f : a -> a) ->
    (x : a) -> (h : DUntil isP f x) -> DPair a P
  dUntil isP f x (DA0 h) = dUntil' isP f x (isP x) h

  dUntil' : {P : a -> Type} -> (isP : (x : a) -> Dec (P x)) -> (f : a -> a) ->
    (x : a) -> (px : Dec (P x)) -> (h : DUntil' isP f x px) -> DPair a P
  dUntil' isP f x (Yes px) DB0 = (x ** px)
  dUntil' isP f x (No npx) (DB1 h) = dUntil isP f (f x) h

du_ge3 : DUntil (isLTE 3) S 0
du_ge3 = DA0 (DB1 (DA0 (DB1 (DA0 (DB1 (DA0 DB0))))))

du_ge3_eq : dUntil (isLTE 3) S 0 Until.du_ge3 =
  (3 ** (LTESucc (LTESucc (LTESucc LTEZero))))
du_ge3_eq = Refl
