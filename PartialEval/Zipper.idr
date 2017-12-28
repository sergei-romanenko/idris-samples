module PartialEval.Zipper

%default total

zipper : %static(xs : List a) -> (ys : List a) -> List a
zipper [] ys = ys
zipper (x :: xs) [] = x :: xs
zipper (x :: xs) (y :: ys) = x :: (y :: zipper xs ys)

zipper_abc : (ys : List String) -> List String
zipper_abc ys = zipper ["a", "b" , "c"] ys

{-

λΠ> :printdef zipper_abc
zipper_abc : List String -> List String
zipper_abc ys = PE_zipper_223717fa ys
λΠ> :printdef PE_zipper_223717fa
PE_zipper_223717fa : List String -> List String
PE_zipper_223717fa [] = ["a", "b", "c"]
PE_zipper_223717fa (y :: ys) = "a" :: y :: PE_zipper_5b3ba559 ys
λΠ> :printdef PE_zipper_5b3ba559
PE_zipper_5b3ba559 : List String -> List String
PE_zipper_5b3ba559 [] = ["b", "c"]
PE_zipper_5b3ba559 (y :: ys) = "b" :: y :: PE_zipper_99464ab7 ys
λΠ> :printdef PE_zipper_99464ab7
PE_zipper_99464ab7 : List String -> List String
PE_zipper_99464ab7 [] = ["c"]
PE_zipper_99464ab7 (y :: ys) = "c" :: y :: ys

λΠ> zipper_abc ["1", "2"]
["a", "1", "b", "2", "c"] : List String

-}
