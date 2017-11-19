module Partial.NestedCalls

import Syntax.PreorderReasoning

%default total

-- Here the function `fp` is total, but Idris is unable to prove it.
-- So we just instruct Idris to treat `fp` as partial.

partial
fp : Nat -> Nat
fp Z = Z
fp (S Z) = S Z
fp (S (S n)) = S (S (fp (fp n)))

-- At compile-time, `fp` is not reduced!

-- fp5_5 : fp 5 = 5
-- fp5_5 = ?r

-- But, at run-time, `fp 5` returns `5`.

-- λΠ> fp 5
-- 5 : Nat

-- Here the function `ft` is total, but Idris is unable to prove it.
-- So we just postulate the totality of `ft (ft n))`.

ft : Nat -> Nat
ft Z = Z
ft (S Z) = S Z
ft (S (S n)) = S (S (assert_total $ ft (ft n)))

ft5_5 : ft 5 = 5
ft5_5 = Refl

-- This proof is not completely formal, since it uses the totality of `ft` that
-- has been just postulated.

ftn_n : (n : Nat) -> ft n = n
ftn_n Z = Z QED
ftn_n (S Z) = (S Z) QED
ftn_n (S (S n)) = cong {f= S . S} (
  (ft (ft n))
    ={ cong {f=ft} (ftn_n n) }=
  (ft n)
    ={ ftn_n n }=
  n QED)

-- Here the function `ft` is total, but Idris is unable to prove it.
-- So we just assert that `fs n` is smaller than `S (S n)`, in order
-- for the termination checker to agree that `ft (ft n))` terminates.

fs : Nat -> Nat
fs Z = Z
fs (S Z) = S Z
fs (S (S n)) = S (S (fs (assert_smaller (S (S n)) (fs n))))

fs5_5 : fs 5 = 5
fs5_5 = Refl

-- This proof is not completely formal, since it uses the totality of `fs` that
-- has been just postulated.

fsn_n : (n : Nat) -> fs n = n
fsn_n Z = Z QED
fsn_n (S Z) = (S Z) QED
fsn_n (S (S n)) = cong {f= S . S} (
  (fs (fs n)) ={ cong {f=fs} (fsn_n n) }= (fs n) ={ fsn_n n }= n QED)

mutual

  -- Now we specify the domain of `f` by using Bove & Capretta's technique.
  -- Note that we have to define `F` and `f` simultaneously,
  -- because the definition of `f` contains a nested function call: f(f n).

  data F : (n : Nat) -> Type where
    F0 : F Z
    F1 : F (S Z)
    F2 : (fn' : F n) -> (ffn' : F (f n fn')) -> F (S (S n))

  f : (n : Nat) -> (fn' : F n) -> Nat
  f Z F0 = Z
  f (S Z) F1 = S Z
  f (S (S n)) (F2 fn' ffn') =
    S (S (f (f n fn') ffn'))

-- OK. Now we can prove some theorems about `f` without postulating its totality.
-- The trick is that the theorems say "the statement is true on condition
-- that the argument belongs to the function's domain.

F5' : F 5
F5' = F2 (F2 F1 F1) (F2 F1 F1)

f5_5 : f 5 F5' = 5
f5_5 = Refl

fn_n : (n : Nat) -> (fn' : F n) -> f n fn' = n
fn_n Z F0 = Refl
fn_n (S Z) F1 = Refl
fn_n (S (S n)) (F2 fn' ffn') = cong {f=S . S} (
  (f (f n fn') ffn')
     ={ fn_n (f n fn') ffn' }=
  (f n fn')
     ={ (fn_n n fn') }=
  n QED)

-- However, we can (formally) prove that the function is total!

all_f : (n : Nat) -> F n
all_f Z = F0
all_f (S Z) = F1
all_f (S (S n)) = F2 fn' ffn' where
  fn' : F n
  fn' = all_f n
  ffn' : F (f n fn')
  --ffn' = rewrite fn_n n fn' in fn'
  ffn' = rewrite (f n fn' = n) <== fn_n ==> F n in fn'
  
-- And now we can wright down a "normal" definition of `f` that
-- does not take an additional argument.

tf : Nat -> Nat
tf n = f n (all_f n)

-- And we can prove some theorems about `total_f`.
-- (Without specifying the domain of `f`.)

tf5_0 : tf 5 = 5
tf5_0 = Refl

tfn_n : (n : Nat) -> tf n = n
tfn_n n = fn_n n (all_f n)
