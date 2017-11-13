module Partial.DomEven

import Syntax.PreorderReasoning

%default total

partial
omega : Nat
omega = omega

partial
hp : Nat -> Nat
hp Z = Z
hp (S Z) = omega
hp (S (S n)) = S (S (hp n))

-- No calls to `h` are unfolded. Hence, `h 2` won't reduce to 2.

--hp2_hp2 : hp 2 = hp 2
--hp2_hp2 = Refl

-- The following theorem is "true", in a sense.
-- But what is the sense? :-)

--hp1_hp1 : hp 1 = hp 1
--hp1_hp1 = Refl

-- Now we specify the domain of `h` following Bove & Capretta's technique.
-- The left-hand sides of the function definition go to the right, while
-- the function calls go to the left.
-- Note that this is a formal procedure, so that no inventiveness
-- is required.

data H : Nat -> Type where
  H0 : H Z
  H2 : (hn_d : H n) -> H (S (S n))

h : (n : Nat) -> (hn_d : H n) -> Nat
h Z H0 = Z
h (S Z) H0 impossible
h (S Z) (H2 _) impossible
h (S (S n)) (H2 hn_d) = S (S (h n hn_d))

h4_d : H 4
h4_d = (H2 (H2 H0))

h4_4 : h 4 DomEven.h4_d = 4
h4_4 = Refl

-- We can prove theorems about partial functions.

hn_n : (n : Nat) -> (hn_d : H n) -> h n hn_d = n
hn_n Z H0 =
  Z QED
hn_n (S Z) H0 impossible
hn_n (S Z) (H2 _) impossible
hn_n (S (S n)) (H2 hn_d) =
  cong {f= S . S} (hn_n n hn_d)


mutual

  partial
  fp : Nat -> Nat
  fp Z = Z
  fp (S n) = S (gp n)

  partial
  gp : Nat -> Nat
  gp Z = omega
  gp (S n) = S (fp n)

-- Here, using Bove & Capretta's technique, we have to specify
-- the domains of two mutually recursive functions, by using
-- two mutually recursive data type definitions.

mutual

  data F : Nat -> Type where
    F0 : F Z
    F1 : (gn_d : G n) -> F (S n)

  data G : Nat -> Type where
    G1 : (fn_d : F n) -> G (S n)

mutual

  f : (n : Nat) -> (fn_d : F n) -> Nat
  f Z F0 = Z
  f (S n) (F1 gn_d) = S (g n gn_d)

  g : (n : Nat) -> (gn_d : G n) -> Nat
  g Z (G1 _) impossible
  g (S n) (G1 fn_d) = S (f n fn_d)

f4_d : F 4
f4_d = F1 (G1 (F1 (G1 F0)))

f4_4 : f 4 DomEven.f4_d = 4
f4_4 = Refl

mutual

  fn_n : (n : Nat) -> (fn_d : F n) -> f n fn_d = n
  fn_n Z F0 = Refl
  fn_n (S n) (F1 gn_d) = cong {f=S} (gn_n n gn_d)

  gn_n : (n : Nat) -> (gn_d : G n) -> g n gn_d = n
  gn_n Z (G1 _) impossible
  gn_n (S n) (G1 fn_d) = cong {f=S} (fn_n n fn_d)
