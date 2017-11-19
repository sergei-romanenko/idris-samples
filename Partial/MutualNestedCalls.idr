module Partial.MutualNestedCalls

import Syntax.PreorderReasoning

%default total

-- Here the functions `f` and `g` are total, but Idris is unable to prove it.

mutual

  partial
  fp : Nat -> Nat
  fp Z = Z
  fp (S n) = S (fp (gp n))

  partial
  gp : Nat -> Nat
  gp Z = Z
  gp (S n) = S (gp (fp n))

-- fp5_0 : fp 5 = 5
-- fp5_0 = Refl

-- Let us postulate that `fs n` and `gs n` are smaller that `S n`.
-- Now the termination checker is happy.

mutual

  fs : Nat -> Nat
  fs Z = Z
  fs (S n) = S (fs (assert_smaller (S n) (gs n)))

  gs : Nat -> Nat
  gs Z = Z
  gs (S n) = S (gs (assert_smaller (S n) (fs n)))

fs5_0 : fs 5 = 5
fs5_0 = Refl

-- This proof is not completely formal, since it uses the totality of `fs` that
-- has been just postulated.

mutual

  fsn_n : (n : Nat) -> fs n = n
  fsn_n Z = Z QED
  fsn_n (S n) = cong {f=S} (
    (fs (gs n))
      ={ cong {f=fs} (gsn_n n) }=
    (fs n)
      ={ fsn_n n }=
    n QED)

  gsn_n : (n : Nat) -> gs n = n
  gsn_n Z = Refl
  gsn_n (S n) =
    rewrite fsn_n n in
    rewrite gsn_n n in
    Refl


mutual

  -- Now we specify the domains of `f` and `g` by using
  -- Bove & Capretta's technique.
  -- Note that we have to define `F`, `G`, `f` and `g` simultaneously,
  -- because the definitions of `f` and `g` contain nested function calls.

  data F : (n : Nat) -> Type where
    A0 : F Z
    A1 : (gn' : G n) -> (fgn' : F (g n gn')) -> F (S n)

  f : (n : Nat) -> F n -> Nat
  f Z A0 = Z
  f (S n) (A1 gn' fgn') = S (f (g n gn') fgn')

  data G : (n : Nat) -> Type where
    B0 : G Z
    B1 : (fn' : F n) -> (gfn' : G (f n fn')) -> G (S n)

  g : (n : Nat) -> G n -> Nat
  g Z B0 = Z
  g (S n) (B1 fn' gfn') = S (g (f n fn') gfn')

-- OK. Now we can prove some theorems about `f` and `g`
-- without postulating their totality.
-- The trick is that the theorems say "the statement is true on condition
-- that the argument belongs to the function's domain.

F3' : F 3
F3' = A1 (B1 (A1 B0 A0) (B1 A0 B0)) (A1 (B1 A0 B0) (A1 B0 A0))

f3_3 : f 3 F3' = 3
f3_3 = Refl

mutual

  fn_n : (n : Nat) -> (fn' : F n) -> f n fn' = n
  fn_n Z A0 = Refl
  fn_n (S n) (A1 gn' fgn') = cong {f=S} (
    (f (g n gn') fgn')
      ={ fn_n (g n gn') fgn' }=
    (g n gn')
      ={ gn_n n gn' }=
    n QED)

  gn_n : (n : Nat) -> (gn' : G n) -> g n gn' = n
  gn_n Z B0 = Refl
  gn_n (S n) (B1 fn' gfn') = cong {f=S} (
    (g (f n fn') gfn')
      ={ gn_n (f n fn') gfn' }=
    (f n fn')
      ={ fn_n n fn' }=
    n QED)

-- However, we can (formally) prove that `f` and `g` are total!

mutual

  all_f : (n : Nat) -> F n
  all_f Z = A0
  all_f (S n) = A1 gn' fgn' where
    gn' : G n
    gn' = all_g n
    fgn' : F (g n gn')
    fgn' = rewrite gn_n n gn' in all_f n

  all_g : (n : Nat) -> G n
  all_g Z = B0
  all_g (S n) = B1 fn' gfn' where
    fn' : F n
    fn' = all_f n
    gfn' : G (f n fn')
    gfn' = rewrite fn_n n fn' in all_g n

-- And now we can write down "normal" definition of `f` and `g` that
-- do not take additional arguments.

tf : Nat -> Nat
tf n = f n (all_f n)

tg : Nat -> Nat
tg n = g n (all_g n)

-- And we can prove some theorems about `tf` and `tg`.
-- (Without specifying the domains of `tf` and `tg`.)

tf5_0 : tf 5 = 5
tf5_0 = Refl

tfn_n : (n : Nat) -> tf n = n
tfn_n n = fn_n n (all_f n)
