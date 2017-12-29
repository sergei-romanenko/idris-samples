module PartialEval.Cyclic

--
-- How to specialize programs with loops?
--

%default total

partial
loop : Eq a => %static (prog, cs : List a) -> (xs : List a) -> Bool
loop prog [] xs = loop prog prog xs
loop prog (c :: cs) [] = True
loop prog (c :: cs) (x :: xs) =
  if c == x then loop prog cs xs else False

partial
Loop1 : Bool
Loop1 = loop ["a", "b"] [] ["a", "b", "a"]

partial
Loop2 : Bool
Loop2 = loop ["a", "b"] [] ["a", "c", "a"]

partial
loop_ab : (xs : List String) -> Bool
loop_ab xs = loop ["a", "b"] [] xs

{-
λΠ> :printdef loop_ab
loop_ab : List String -> Bool
loop_ab xs = PE_loop_30f6ca4c xs
λΠ> :printdef PE_loop_30f6ca4c
PE_loop_30f6ca4c : List String -> Bool
PE_loop_30f6ca4c [] = PE_loop_4fbeda4f []
PE_loop_30f6ca4c (x :: xs) = PE_loop_4fbeda4f (x :: xs)
λΠ> :printdef PE_loop_4fbeda4f
PE_loop_4fbeda4f : List String -> Bool
PE_loop_4fbeda4f [] = True
PE_loop_4fbeda4f (x :: xs) =
  ifThenElse (PE_==_c1eaf49 "a" x)
             (Delay (PE_loop_927a32f0 xs))
             (Delay False)
λΠ> :printdef PE_loop_927a32f0
PE_loop_927a32f0 : List String -> Bool
PE_loop_927a32f0 [] = True
PE_loop_927a32f0 (x :: xs) =
  ifThenElse (PE_==_c1eaf49 "b" x)
             (Delay (PE_loop_30f6ca4c xs))
             (Delay False)
λΠ> :printdef PE_loop_30f6ca4c
PE_loop_30f6ca4c : List String -> Bool
PE_loop_30f6ca4c [] = PE_loop_4fbeda4f []
PE_loop_30f6ca4c (x :: xs) = PE_loop_4fbeda4f (x :: xs)
-}

partial
loop_nil : (xs : List String) -> Bool
loop_nil xs = loop [] [] xs

-- An infinite loop. Partial evaluation produces a reasonable result.

{-
λΠ> :printdef loop_nil
loop_nil : List String -> Bool
loop_nil xs = PE_loop_d9b4b978 xs
λΠ> :printdef PE_loop_d9b4b978
PE_loop_d9b4b978 : List String -> Bool
PE_loop_d9b4b978 [] = PE_loop_d9b4b978 []
PE_loop_d9b4b978 (x :: xs) = PE_loop_d9b4b978 (x :: xs)
-}
