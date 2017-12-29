module PartialEval.TheTrick

--
-- "The trick" amounts to comparing a static value to a dynamic one,
-- followed by using the static one.
-- `... d ...` where `s == d` ===> `... s ...`
--

%default total

oneOf : Eq a => %static (xs : List a) -> (y : a) -> Maybe a
oneOf [] y = Nothing
oneOf (x :: xs) y =
  if x == y then Just x else oneOf xs y

oneOf_ab : (y : String) -> Maybe String
oneOf_ab y = oneOf ["a", "b"] y

{-
λΠ> :printdef oneOf_ab
oneOf_ab : String -> Maybe String
oneOf_ab y = PE_oneOf_5bc5475d y
λΠ> :printdef PE_oneOf_5bc5475d
PE_oneOf_5bc5475d : String -> Maybe String
PE_oneOf_5bc5475d (3arg) =
  ifThenElse ("a" == (3arg))
             (Delay (Just "a"))
             (Delay (ifThenElse ("b" == (3arg))
                                (Delay (Just "b"))
                                (Delay Nothing)))
-}

oneOf_case : Eq a => %static (xs : List a) -> (y : a) -> Maybe a
oneOf_case [] y = Nothing
oneOf_case (x :: xs) y = case x == y of
  True => Just x
  False => oneOf_case xs y

oneOf_case_ab : (y : String) -> Maybe String
oneOf_case_ab y = oneOf_case ["a", "b"] y

-- Now the result of PE is strange.
-- For some reasons, the partial evaluator is afraid of `case`.

{-
λΠ> :printdef oneOf_case_ab
oneOf_case_ab : String -> Maybe String
oneOf_case_ab y = PE_oneOf_case_5bc5475d y
λΠ> :printdef PE_oneOf_case_5bc5475d
PE_oneOf_case_5bc5475d : String -> Maybe String
PE_oneOf_case_5bc5475d (3arg) = case "a" == (3arg) of
  True => Just x
  False => oneOf_case xs y
-}

mutual

  oneOf_aux : Eq a => %static (xs : List a) -> (y : a) -> Maybe a
  oneOf_aux [] y = Nothing
  oneOf_aux (x :: xs) y =
    oneOf_aux' x xs y (x == y)

  %static
  oneOf_aux' : Eq a => %static (x : a) -> %static (xs : List a) ->
    (y : a) -> (x_eq_y : Bool) -> Maybe a
  oneOf_aux' x xs y True = Just x
  oneOf_aux' x xs y False = oneOf_aux xs y

oneOf_aux_ab : (y : String) -> Maybe String
oneOf_aux_ab y = oneOf_aux ["a", "b"] y

-- Again, the partial evaluator won't unfold the calls
-- to oneOf_aux_case.

{-
λΠ> :printdef oneOf_aux_ab
oneOf_aux_ab : String -> Maybe String
oneOf_aux_ab y = PE_oneOf_aux_5bc5475d y
λΠ> :printdef PE_oneOf_aux_5bc5475d
PE_oneOf_aux_5bc5475d : String -> Maybe String
PE_oneOf_aux_5bc5475d (3arg) = oneOf_aux' "a" ["b"] (3arg) ("a" == (3arg))
-}

--
-- The problem is how to compose such functions?
--

ab_bc : (y : String) -> Maybe String
ab_bc y = case oneOf ["a", "b"] y of
  Nothing => Nothing
  Just y' => oneOf ["b", "c"] y'

-- Partial evaluation produces a two-pass algorithm.

{-
λΠ> :printdef ab_bc
ab_bc : String -> Maybe String
ab_bc y = case PE_oneOf_5bc5475d y of
  Nothing => Nothing
  Just y' => PE_oneOf_5c3166b6 y'
-}

-- CPS.

oneOfC : Eq a => %static (xs : List a) -> (y : a) ->
  %static (k : %static a -> Maybe a) -> Maybe a
oneOfC [] y k = Nothing
oneOfC (x :: xs) y k =
  if x == y then k x else oneOfC xs y k

oneOfC_ab : (y : String) -> Maybe String
oneOfC_ab y = oneOfC ["a", "b"] y Just

-- Partial evaluation produces a good result!

{-
λΠ> :printdef PE_oneOfC_2e044ace
PE_oneOfC_2e044ace : String -> Maybe String
PE_oneOfC_2e044ace (3arg) =
  ifThenElse ("a" == (3arg))
             (Delay (Just "a"))
             (Delay (ifThenElse ("b" == (3arg))
                                (Delay (Just "b"))
                                (Delay Nothing)))
-}

oneOfS : Eq a => %static (xs : List a) -> %static (y : a) ->
  %static (k : %static a -> Maybe a) -> Maybe a
oneOfS [] y k = Nothing
oneOfS (x :: xs) y k =
  if x == y then k x else oneOfS xs y k

OneOfS_abc_b : Maybe String
OneOfS_abc_b = oneOfS ["a", "b", "c"] "b" Just

-- No static conditionals are reduced!

{-
λΠ> :printdef OneOfS_abc_b
OneOfS_abc_b : Maybe String
OneOfS_abc_b = PE_oneOfS_603fc336
λΠ> :printdef PE_oneOfS_603fc336
PE_oneOfS_603fc336 : Maybe String
PE_oneOfS_603fc336 =
  ifThenElse ("a" == "b")
             (Delay (Just "a"))
             (Delay (ifThenElse ("b" == "b")
                                (Delay (Just "b"))
                                (Delay (ifThenElse ("c" == "b")
                                                   (Delay (Just "c"))
                                                   (Delay Nothing)))))
-}

-- OK! Let's try to rewrite the conditional in `OneOfC` in CPS.

eqNat : %static (l, r : Nat) -> %static (t, e : Lazy a) -> %static a
eqNat Z Z t e = t
eqNat Z (S r) t e = e
eqNat (S l) Z t e = e
eqNat (S l) (S r) t e = eqNat l r t e

oneOfN : %static (xs : List Nat) -> %static (y : Nat) ->
  %static (k : %static Nat -> Maybe Nat) -> Maybe Nat
oneOfN [] y k = Nothing
oneOfN (x :: xs) y k =
  eqNat x y (k x) (oneOfN xs y k)

OneOfN_012_2 : Maybe Nat
OneOfN_012_2 = oneOfN [Z , S Z, S (S Z)] (S Z) Just

-- Finally, all conditionals have been removed...

{-
λΠ> :printdef OneOfN_012_2
OneOfN_012_2 : Maybe Nat
OneOfN_012_2 = PE_oneOfN_109e83b5
λΠ> :printdef PE_oneOfN_109e83b5
PE_oneOfN_109e83b5 : Maybe Nat
PE_oneOfN_109e83b5 = PE_eqNat_b867e550
λΠ> :printdef PE_eqNat_b867e550
PE_eqNat_b867e550 : Maybe Nat
PE_eqNat_b867e550 = Just 1
-}

oneOf_01_12 : (y : Nat) -> Maybe Nat
oneOf_01_12 y = oneOfC [Z, S Z] y (\z => oneOfN [S Z, S (S Z)] z Just)

-- Finally, the static tests, like `0 = 1`, have been removed.

{-
λΠ> :printdef oneOf_01_12
oneOf_01_12 : Nat -> Maybe Nat
oneOf_01_12 y = PE_oneOfC_2a2660f0 y
λΠ> :printdef PE_oneOfC_2a2660f0
PE_oneOfC_2a2660f0 : Nat -> Maybe Nat
PE_oneOfC_2a2660f0 (3arg) =
  ifThenElse (0 == (3arg))
             (Delay PE_oneOfN_ba593f98)
             (Delay (ifThenElse (1 == (3arg))
                    (Delay PE_oneOfN_b7f8fe4)
                    (Delay Nothing)))
λΠ> :printdef PE_oneOfN_ba593f98
PE_oneOfN_ba593f98 : Maybe Nat
PE_oneOfN_ba593f98 = PE_eqNat_f3b05c95
λΠ> :printdef PE_eqNat_f3b05c95
PE_eqNat_f3b05c95 : Maybe Nat
PE_eqNat_f3b05c95 = Nothing
λΠ> :printdef PE_oneOfN_b7f8fe4
PE_oneOfN_b7f8fe4 : Maybe Nat
PE_oneOfN_b7f8fe4 = PE_eqNat_ffeb9bd8
λΠ> :printdef PE_eqNat_ffeb9bd8
PE_eqNat_ffeb9bd8 : Maybe Nat
PE_eqNat_ffeb9bd8 = Just 1
-}

-- And, upon removing unconditional jumps, we get:

{-
oneOf_01_12 : Nat -> Maybe Nat
oneOf_01_12 y =
  if 0 == y then Nothing
            else if 1 == y then Just 1
                           else Nothing
-}

-- A problem: the string equality tests won't reduce!

eqStr : %static (l, r : String) -> %static (t, e : Lazy a) -> %static a
eqStr l r t e = if l == r then t else e

EqStr_ab : Nat
EqStr_ab = eqStr "a" "b" Z (S Z)

{-
λΠ> :printdef EqStr_ab
EqStr_ab : Nat
EqStr_ab =
  PE_eqStr_e26b6cc1
λΠ> :printdef PE_eqStr_e26b6cc1
PE_eqStr_e26b6cc1 : Nat
PE_eqStr_e26b6cc1 =
  ifThenElse ("a" == "b") (Delay 0) (Delay 1)
-}
