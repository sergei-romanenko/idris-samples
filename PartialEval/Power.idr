module PartialEval.Power

%default total

-- n^k

pw : (n : Nat) -> %static (k : Nat) -> Nat
pw n Z = S Z
pw n (S k) = mult n (pw n k)

pw3 : (n : Nat) -> Nat
pw3 n = pw n (S (S (S Z)))

{-

λΠ> :printdef pw3
pw3 : Nat -> Nat
pw3 n = PE_pw_4276a3be n
λΠ> :printdef PE_pw_4276a3be
PE_pw_4276a3be : Nat -> Nat
PE_pw_4276a3be (0arg) = mult (0arg) (mult (0arg) (mult (0arg) 1))

-}
