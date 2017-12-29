module PartialEval.TuringMachine

--
-- An interpreter for Turing's machines.
--

%default total

data Stmt : Type where
  Right : Stmt
  Left  : Stmt
  Write : (a : String) -> Stmt
  Goto  : (i : Nat) -> Stmt
  If    : (a : String) -> (i : Nat) -> Stmt

Prog : Type
Prog = List Stmt

Tape : Type
Tape = (List String, String, List String)

move_right : (t : Tape) -> Tape
move_right (l, c, []) = (c :: l, "" , [])
move_right (l, c, c' :: r) = (c :: l, c' , r)

move_left : (t : Tape) -> Tape
move_left ([], c, r) = ([] , "", c :: r)
move_left (c' :: l, c, r) = (l , c', c :: r)

write : (a : String) -> (t : Tape) -> Tape
write a (l , _ , r) = (l, a, r)

current_is : (a : String) -> (t : Tape) -> Bool
current_is a (_, c, _) = a == c

mutual

  partial
  exec_stmt : %static (prog : Prog) ->
    %static (stmt : Stmt) -> %static (rest : Prog) ->
    (t : Tape) -> Tape
  exec_stmt prog Right rest t = next prog rest (move_right t)
  exec_stmt prog Left rest t = next prog rest (move_left t)
  exec_stmt prog (Write a) rest t = next prog rest (write a t)
  exec_stmt prog (Goto i) rest t = goto prog i t
  exec_stmt prog (If a i) rest t =
    if current_is a t then goto prog i t
                      else next prog rest t

  partial
  jump : %static (prog : Prog) ->
    %static (i : Nat) -> %static (rest : Prog) ->
    (t : Tape) -> Tape
  jump prog Z [] t = t
  jump prog Z (stmt :: rest) t =
    exec_stmt prog stmt rest t
  jump prog (S i) [] t = t
  jump prog (S i) (stmt :: rest) t =
    jump prog i rest t

  partial
  goto : %static (prog : Prog) -> %static (i : Nat) ->
    (t : Tape) -> Tape
  goto prog i t = jump prog i prog t

  partial
  next : %static (prog : Prog) -> %static (rest : Prog) ->
    (t : Tape) -> Tape
  next prog [] t = t
  next prog (stmt :: rest) t = exec_stmt prog stmt rest t

partial
run : %static (prog : Prog) -> (t : Tape) -> Tape
run prog t = goto prog Z t

run_total : %static (prog : Prog) -> (t : Tape) -> Tape
run_total prog t = assert_total $ run prog t

ExProg1 : Prog
ExProg1 = [
  If "a" (S (S (S Z))), -- 0
  Write "b",            -- 1
  Goto (S (S (S (S (S Z))))), -- 2
  Right,                -- 3
  Goto Z                -- 4
  ]

ExProg2 : Prog
ExProg2 = [
  If "a" 3,  -- 0
  Write "b", -- 1
  Goto 5,    -- 2
  Left,      -- 3
  Goto 0     -- 4
  ]

rt1 : run_total ExProg1 ([], "a", ["a", "x", "y"]) = (["a", "a"], "b", ["y"])
rt1 = Refl

rt2 : run_total ExProg2 (["a", "x", "y"], "a", []) = (["y"], "b", ["a", "a"])
rt2 = Refl

partial
run1 : (t : Tape) -> Tape
run1 t = run ExProg1 t

-- The result of specialization is not satisfactory...

{-
λΠ> :printdef PE_jump_fba95b02
PE_jump_fba95b02 : Tape -> Tape
PE_jump_fba95b02 (3arg) =
  jump [If "a" 3, Write "b", Goto 5, Right, Goto 0] 0 [Right, Goto 0] (3arg)

λΠ> :printdef PE_exec_stmt_5e0f7a4d
PE_exec_stmt_5e0f7a4d : Tape -> Tape
PE_exec_stmt_5e0f7a4d (3arg) =
  goto [If "a" 3, Write "b", Goto 5, Right, Goto 0] 5 (3arg)
-}
