module Termination

%default total

-- The termination checker of Idris is basicly the same as that of Foetus:
--
--   Andreas Abel. 1998. foetus -- Termination Checker for Simple
--   Functional Programs. Programming Lab Report.
--   http://www2.tcs.ifi.lmu.de/~abel/foetus/

-- The termination checker of Agda inspects the parameters of recursive call.
-- In the third line, (x′ < S x′ & y = y).

add : (x, y : Nat) -> Nat
add Z y = y
add (S x') y = S (add x' y)

-- The dependency relation is defined as follows:
--
--  * Constructor elimination: if cons is a constructor,
--      x < cons a1 ... an x b1 ... bn
--  * Application: if y < x then
--       y a1 ... an < x

data Bin : Type where
  BN  : Bin
  B0 : Bin -> Bin
  B1 : Bin -> Bin

-- Here B0 x < B0 (B1 x) .

-- Alas! This is OK in Agda, but doesn't work in Idris. :-(

partial
foo1 : Bin -> Nat
foo1 BN = Z
foo1 (B0 BN) = Z
foo1 (B0 (B1 x)) = S (foo1 (B0 x))
foo1 (B0 (B0 x)) = S (foo1 (B0 x))
foo1 (B1 x)      = S (foo1 x)

-- This is OK neither in Agda nor in Idris.

-- Here B1 x < B0 (C0 x) doesn't hold!

partial
foo2 : Bin -> Nat
foo2 BN = Z
foo2 (B0 BN) = Z
foo2 (B0 (B1 x)) = S (foo2 (B0 x))
foo2 (B0 (B0 x)) = S (foo2 (B1 x))
foo2 (B1 x)      = S (foo2 x)

-- Agda can find termination orders across mutually recursive functions.
-- Agda can find lexicographic termination orders.

-- There is a lexicographic order on parameters with respect
-- to the dependency order:
--   (x , y) << (x’, y’) ⇔ (x < x’ or (x ≤ x’ & y < y’))

ack : Nat -> Nat -> Nat
ack Z n = S Z
ack (S m) Z = ack m (S Z)
ack (S m) (S n) = ack m (ack (S m) n)

-- And what about the application rule:
--  y < x ⇒ y a1 ... an < x ?

--
-- Transfinite addition of ordinal numbers
--

data OrdNat : Type where
  OZ : OrdNat
  OS  : (n : OrdNat) -> OrdNat
  Lim  : (f : Nat -> OrdNat) -> OrdNat

addOrd : (n, m : OrdNat) -> OrdNat
addOrd OZ m = m
addOrd (OS n) m = OS (addOrd n m)
addOrd (Lim f) m = Lim (\u => addOrd (f u) m)

Lim0 : OrdNat
Lim0 = Lim (\u => OZ)

lim00 : addOrd Lim0 OZ = Lim (\_ => OZ)
lim00 = Refl

lim0m : (m : OrdNat) -> addOrd Lim0 m = Lim (\_ => m)
lim0m m = Refl

NatToOrdNat : (n : Nat) -> OrdNat
NatToOrdNat Z = OZ
NatToOrdNat (S n) = OS (NatToOrdNat n)

Branch : OrdNat
Branch = Lim (\u => NatToOrdNat u)

branch_branch : addOrd Branch Branch =
  Lim (\u => addOrd (NatToOrdNat u) (Lim NatToOrdNat))
branch_branch = Refl

--
-- But in some cases all the above is not sufficient.
--

-- Division by 2, rounded downwards.

div2 : Nat -> Nat
div2 Z = Z
div2 (S Z) = Z
div2 (S (S n)) = S (div2 n)

div2LTE : (n : Nat) -> div2 n `LTE` n
div2LTE Z = LTEZero
div2LTE (S Z) = LTEZero
div2LTE (S (S n)) =
  LTESucc (lteSuccRight (div2LTE n))

smaller_sd2_ss : (n : Nat) -> S (div2 n) `LT` S (S n)
smaller_sd2_ss n = LTESucc (LTESucc (div2LTE n))

log2a : Nat -> Nat
log2a Z = Z
log2a (S Z) = Z
log2a (S (S n)) = S (log2a (assert_smaller (S (S n)) (S (div2 n))))

log2a_test : map Termination.log2a [0, 1, 2, 3, 4] = [0, 0, 1, 1, 2]
log2a_test = Refl

--
-- Using the accessibility of all Nat's.
--

%hide log2

log2s' : (n : Nat) -> (acc : SizeAccessible n) -> Nat
log2s' Z acc = Z
log2s' (S Z) acc = Z
log2s' (S (S n)) (Access rec) =
  S (log2s' n' (rec n' lt))
  where n' : Nat
        n' = S (div2 n)
        lt : n' `LT` S (S n)
        lt = smaller_sd2_ss n

log2s : (n : Nat) -> Nat
log2s n = log2s' n (sizeAccessible n)

log2s_test : map Termination.log2s [0, 1, 2, 3, 4] = [0, 0, 1, 1, 2]
log2s_test = Refl

-- We can separate the computational part from the proofs
-- related to ensuring the termination. See the papers:
--
-- Ana Bove. 2001. Simple general recursion in type theory.
-- Nordic J. of Computing 8, 1 (March 2001), 22-42.
--
-- Ana Bove and Venanzio Capretta. 2005.
-- Modelling general recursion in type theory.
-- Mathematical. Structures in Comp. Sci. 15, 4 (August 2005), 671-708.
-- DOI=10.1017/S0960129505004822 http://dx.doi.org/10.1017/S0960129505004822 

data Log2b : Nat -> Type where
  L0 : Log2b Z
  L1 : Log2b (S Z)
  L2 : Log2b (S (div2 n)) -> Log2b (S (S n))

log2b' : (n : Nat) -> (acc : Log2b n) -> Nat
log2b' Z L0 = Z
log2b' (S Z) L1 = Z
log2b' (S (S n)) (L2 acc) =
  S (log2b' (S (div2 n)) acc)

Log2b_3 : Log2b 3
Log2b_3 = L2 L1

Log2b_3_1 : log2b' 3 Log2b_3 = 1
Log2b_3_1 = Refl

-- For all `n`, `Log2b n`!

all_log2b' : (n : Nat) -> (acc : SizeAccessible n) -> Log2b n
all_log2b' Z rec = L0
all_log2b' (S Z) rec = L1
all_log2b' (S (S n)) (Access rec) =
  L2 (all_log2b' n' (rec n' lt))
  where n' : Nat
        n' = S (div2 n)
        lt : n' `LT` S (S n)
        lt = smaller_sd2_ss n

all_log2b : (n : Nat) -> Log2b n
all_log2b n = all_log2b' n (sizeAccessible n)

log2b : Nat -> Nat
log2b n = log2b' n (all_log2b n)

log2b_test : map Termination.log2b [0, 1, 2, 3, 4] = [0, 0, 1, 1, 2]
log2b_test = Refl
