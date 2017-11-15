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

-- No calls to `hp` are unfolded. Hence, `hp 2` won't reduce to 2.

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
  H2 : (hn' : H n) -> H (S (S n))

h : (n : Nat) -> (hn' : H n) -> Nat
h Z H0 = Z
h (S Z) H0 impossible
h (S Z) (H2 _) impossible
h (S (S n)) (H2 hn') = S (S (h n hn'))

h4' : H 4
h4' = (H2 (H2 H0))

h4_4 : h 4 DomEven.h4' = 4
h4_4 = Refl

-- We can prove theorems about partial functions.

hn_n : (n : Nat) -> (hn' : H n) -> h n hn' = n
hn_n Z H0 =
  Z QED
hn_n (S Z) H0 impossible
hn_n (S Z) (H2 _) impossible
hn_n (S (S n)) (H2 hn') =
  cong {f= S . S} (hn_n n hn')


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
    F1 : (gn' : G n) -> F (S n)

  data G : Nat -> Type where
    G1 : (fn' : F n) -> G (S n)

mutual

  f : (n : Nat) -> (fn' : F n) -> Nat
  f Z F0 = Z
  f (S n) (F1 gn') = S (g n gn')

  g : (n : Nat) -> (gn' : G n) -> Nat
  g Z (G1 _) impossible
  g (S n) (G1 fn') = S (f n fn')

f4' : F 4
f4' = F1 (G1 (F1 (G1 F0)))

f4_4 : f 4 DomEven.f4' = 4
f4_4 = Refl

mutual

  fn_n : (n : Nat) -> (fn' : F n) -> f n fn' = n
  fn_n Z F0 = Refl
  fn_n (S n) (F1 gn') = cong {f=S} (gn_n n gn')

  gn_n : (n : Nat) -> (gn' : G n) -> g n gn' = n
  gn_n Z (G1 _) impossible
  gn_n (S n) (G1 fn') = cong {f=S} (fn_n n fn')
