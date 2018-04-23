--
-- Small-step operational semantics
-- making use of dependent types
--

{-
This (slightly modified) code is from

  Proof by Smugness
  by Conor on August 7, 2007.
  http://fplab.bitbucket.org/posts/2007-08-07-proof-by-smugness.html
-}

module StackMachine

import Syntax.PreorderReasoning
import Data.Vect

%hide Seq

%default total

--
-- A Toy Language
--

infixl 8 +

data Tm : Type where
  Val : (n : Nat) -> Tm
  (+) : (t1, t2 : Tm) -> Tm

-- Big-step evaluator

eval : Tm -> Nat
eval (Val n) = n
eval (t1 + t2) = eval t1 + eval t2

--
-- Virtual machine
--

-- Program

-- The idea is to index code by initial and final stack depth
-- in order to ensure stack safety. 

data Code : (i, j : Nat) -> Type where
  Seq  : (c1 : Code i j) -> (c2 : Code j k) -> Code i k
  Push : (n : Nat) -> Code i (1 + i)
  Add  : Code (2 + i) (1 + i)

-- State

Stack : Nat -> Type
Stack i = Vect i Nat

-- Interpreter

exec : (c : Code i j) -> (s : Stack i) -> Stack j
exec (Seq c1 c2) s = exec c2 (exec c1 s)
exec (Push n) s = n :: s
exec Add (n2 :: (n1 :: s)) = (n1 + n2) :: s

-- Compiler

compile : (t : Tm) -> Code i (1 + i)
compile (Val n) = Push n
compile (t1 + t2) = Seq (Seq (compile t1) (compile t2)) Add

-- `Seq` is associative with respect to `exec`.

seq_assoc : exec (Seq (Seq c1 c2) c3) s = exec (Seq c1 (Seq c2 c3)) s
seq_assoc {c1} {c2} {c3} {s} =
  (exec (Seq (Seq c1 c2) c3) s)
    ={ Refl }=
  (exec c3 (exec (Seq c1 c2) s))
    ={ Refl }=
  (exec c3 (exec c2 (exec c1 s)))
    ={ Refl }=
  (exec (Seq c2 c3) (exec c1 s))
    ={ Refl }=
  (exec (Seq c1 (Seq c2 c3)) s)
  QED

-- Here is another proof, which is shorter, but is more mysterious.

seq_assoc' : exec (Seq (Seq c1 c2) c3) s = exec (Seq c1 (Seq c2 c3)) s
seq_assoc' = Refl

-- `compile` is correct with respect to `exec`.

correct : (t : Tm) -> (s : Stack i) ->
  exec (compile t) s = eval t :: s
correct (Val n) s = -- Refl
  (exec (compile (Val n)) s)
    ={ Refl }=
  (exec (Push n) s)
    ={ Refl }=
  (n :: s)
    ={ Refl }=
  (eval (Val n) :: s)
  QED
correct (t1 + t2) s =
  let n1 = eval t1; c1 = compile t1 in
  let n2 = eval t2; c2 = compile t2 in
    (exec (compile (t1 + t2)) s)
      ={ Refl }=
    (exec (Seq (Seq c1 c2) Add) s)
      ={ Refl }=
    (exec Add (exec c2 (exec c1 s)))
      ={ cong {f= exec Add . exec c2} (correct t1 s) }=
    (exec Add (exec c2 (n1 :: s)))
      ={ cong {f= exec Add} (correct t2 (n1 :: s)) }=
    (exec Add (n2 :: (n1 :: s)))
      ={ Refl }=
    ((n1 + n2) :: s)
      ={ Refl }=
    (eval (t1 + t2) :: s)
    QED

-- Here is another proof, which is shorter, but is more mysterious.

correct' : (t : Tm) -> (s : Stack i) ->
  exec (compile t) s = eval t :: s
correct' (Val n) s = Refl
correct' (t1 + t2) s =
  rewrite correct' t1 s in
  rewrite correct' t2 (eval t1 :: s) in
  Refl

--
-- A compiler that is correct "by construction".
--

ex_code : {i : Nat} -> (t : Tm) ->
  (c : Code i (1 + i) ** (s : Stack i) -> exec c s = eval t :: s)
ex_code (Val n) =
  (Push n ** (\s => (n :: s) QED))
ex_code {i} (t1 + t2) =
  let (c1 ** p1) = ex_code {i=i} t1 in
  let (c2 ** p2) = ex_code {i=1+i} t2 in
  let n1 = eval t1 in
  let n2 = eval t2 in
    (Seq (Seq c1 c2) Add ** \s =>
      (exec (Seq (Seq c1 c2) Add) s)
        ={ Refl }=
      (exec Add (exec c2 (exec c1 s)))
        ={ cong {f= exec Add . exec c2} (p1 s) }=
      (exec Add (exec c2 (n1 :: s)))
        ={ cong {f= exec Add} (p2 (n1 :: s)) }=
      (exec Add (n2 :: n1 :: s))
        ={ Refl }=
      (n1 + n2 :: s)
      QED)

--
-- `ex_code` produces the same code as `compile`.
-- But Agda is not capable of automatically extracting
-- `compile` from `ex_code` (unlike Coq).
--

correct'' : {i : Nat} -> (t : Tm) ->
   compile {i} t = fst (ex_code {i} t)
correct'' (Val n) = Refl
correct'' {i} (t1 + t2) with (ex_code {i=i} t1) proof eq1
  | (c1 ** p1) with (ex_code {i=1+i} t2) proof eq2
    | (c2 ** p2) =
      rewrite correct'' {i=i} t1 in
      rewrite correct'' {i=1+i} t2 in
      rewrite sym eq1 in
      rewrite sym eq2 in
      Refl

--
-- Compiling to a list of instructions
--

-- Instructions

data Inst : (i, j : Nat) -> Type where
  IPush : (n : Nat) -> Inst i (1 + i)
  IAdd  : Inst (2 + i) (1 + i)

-- Programs

infixr 5 #

data Prog : (i, j : Nat) -> Type where
  EOP : Prog i i
  (#) : (c : Inst i j) -> (p : Prog j k) -> Prog i k

-- Interpreter

p_exec : (p : Prog i j) -> (s : Stack i) -> Stack j
p_exec EOP s = s
p_exec (IPush n # p) s = p_exec p (n :: s)
p_exec (IAdd # p) (n2 :: n1 :: s) = p_exec p ((n1 + n2) :: s)

-- Compiler

p_compile : (t : Tm) -> (p : Prog (1 + i) j) -> Prog i j
p_compile (Val n) p = IPush n # p
p_compile (t1 + t2) p =
  p_compile t1 (p_compile t2 (IAdd # p))

-- Code -> Prog

flatten : (c : Code i j) -> (p : Prog j k) -> Prog i k
flatten (Seq c1 c2) p = flatten c1 (flatten c2 p)
flatten (Push n) p = IPush n # p
flatten Add p = IAdd # p

-- `flatten` is correct.

flatten_correct' : (c : Code i j) -> (p : Prog j k) -> (s : Stack i) ->
  p_exec p (exec c s) = p_exec (flatten c p) s
flatten_correct' (Seq c1 c2) p s =
  (p_exec p (exec (Seq c1 c2) s))
    ={ Refl }=
  (p_exec p (exec c2 (exec c1 s)))
    ={ flatten_correct' c2 p (exec c1 s) }=
  (p_exec (flatten c2 p) (exec c1 s))
    ={ flatten_correct' c1 (flatten c2 p) s }=
  (p_exec (flatten c1 (flatten c2 p)) s)
    ={ Refl }=
  (p_exec (flatten (Seq c1 c2) p) s)
  QED
flatten_correct' (Push n) p s =
  (p_exec p (n :: s)) QED
flatten_correct' Add p (n2 :: n1 :: s) =
  (p_exec p (n1 + n2 :: s)) QED

flatten_correct : (c : Code i j) -> (s : Stack i) ->
  exec c s = p_exec (flatten c EOP) s
flatten_correct c s = flatten_correct' c EOP s

-- compile ~ p_compile

compile_p_compile : (t : Tm) -> (p : Prog (1 + i) j) ->
  flatten (compile t) p = p_compile t p
compile_p_compile (Val n) p =
  (IPush n # p) QED
compile_p_compile (t1 + t2) p =
  (flatten (compile (t1 + t2)) p)
    ={ Refl }=
  (flatten (compile t1) (flatten (compile t2) (IAdd # p)))
    ={ compile_p_compile t1 (flatten (compile t2) (IAdd # p)) }=
  (p_compile t1 (flatten (compile t2) (IAdd # p)))
    ={ cong {f= p_compile t1} (compile_p_compile t2 (IAdd # p)) }=
  (p_compile t1 (p_compile t2 (IAdd # p)))
    ={ Refl }=
  (p_compile (t1 + t2) p)
  QED
