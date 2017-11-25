module MetaProg.ElabEven

import Language.Reflection
import Pruviloj.Core

%language ElabReflection

%default total

data Even : Nat -> Type where
  Even0 : Even 0
  Even2 : Even n -> Even (2 + n)

Ev2 : Even 2
Ev2 = Even2 Even0

Ev4 : Even 4
Ev4 = Even2 (Even2 Even0)

notEven1 : Even 1 -> Void
notEven1 Even0 impossible
notEven1 (Even2 _) impossible

projEven2 : Even (2 + n) -> Even n
projEven2 (Even2 even_n) = even_n

decEven : (n : Nat) -> Dec (Even n)
decEven Z = Yes Even0
decEven (S Z) = No notEven1
decEven (S (S n)) with (decEven n)
  decEven (S (S n)) | Yes even_n = Yes (Even2 even_n)
  decEven (S (S n)) | No not_even_n =
    No (\even_ssn => not_even_n (projEven2 even_ssn))

FromYes : {P : Type} -> (dp : Dec P) -> Type
FromYes {P} (Yes p) = P
FromYes (No not_p) = ()

fromYes : {P : Type} -> (dp : Dec P) -> FromYes dp
fromYes (Yes p) = p
fromYes (No not_p) = ()

Ev8 : Even 8
Ev8 = fromYes (decEven 8)

maybeEven : (n : Nat) -> Maybe (Even n)
maybeEven Z = Just Even0
maybeEven (S Z) = Nothing
maybeEven (S (S n)) with (maybeEven n)
  maybeEven (S (S n)) | Nothing = Nothing
  maybeEven (S (S n)) | (Just even_n) = Just (Even2 even_n)

mbEv8 : maybeEven 8 = Just (Even2 (Even2 (Even2 (Even2 Even0))))
mbEv8 = Refl

elabEven : (k : Nat) -> Elab ()
elabEven Z = exact `(Even0)
elabEven (S Z) = fail [NamePart `{elabEven}, TextPart "Odd arg"]
elabEven (S (S k)) =
  do h <- newHole "h" `(Even ~(quote k))
     exact `(Even2 {n=~(quote k)} ~(Var h))
     focus h; elabEven k

elabEv2 : Even 2
elabEv2 = %runElab (elabEven 2)

autoEven : Elab ()
autoEven =
  do g <- goalType
     case g of
       `(Even ~k) => mkProof k
       _ => fail [NamePart `{autoEven}, TextPart "Not Even", RawPart g]
  where
  mkProof : Raw -> Elab()
  mkProof `(Z) =
    exact `(Even0)
  mkProof `(S Z) =
    fail [NamePart `{autoEven}, TextPart "Odd arg"]
  mkProof `(S (S ~k)) =
    do h <- newHole "h" `(Even ~k)
       exact `(Even2 {n=~k} ~(Var h))
       focus h; mkProof k
  mkProof k =
    fail [NamePart `{autoEven}, TextPart "Not Nat", RawPart k]

autoEv4 : Even 4
autoEv4 = %runElab autoEven
