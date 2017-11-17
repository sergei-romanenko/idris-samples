module EquationalReasoning

import Syntax.PreorderReasoning
import Control.Isomorphism

%default total

-- Implication is a preorder relation...

namespace Impl
  using (a, b, c : Type)
  qed : (a : Type) -> (a -> a)
  qed a = id
  step : (a : Type) -> (ab : a -> b) -> (bc : b -> c) -> (a -> c)
  step a ab bc = bc . ab

--
-- Impication is "reflexive" and "transitive".
--

impl_refl : (a -> a)
impl_refl {a} = a QED

impl_trans : {a, b, c : Type} ->
  (a -> b) -> (b -> c) -> (a -> c)
impl_trans {a} {b} {c} ab bc =
  a ={ ab }= b ={ bc }= c QED

--
-- Now, let's prove something by means of equational reasoning.
--

mutual

  data Even : Nat -> Type where
    E0 : Even Z
    E1 : Odd n -> Even (S n)

  data Odd : Nat -> Type where
    O1 : Even n -> Odd (S n)

odd_1 : Odd 1
odd_1 = O1 E0

even_2 : Even 2
even_2 = E1 (O1 E0)

-- Uninhabited...

implementation Uninhabited (Odd Z) where
  uninhabited (O1 _) impossible

-- Inversion.

not_odd_0 : Odd Z -> Void
--not_odd_0 (O1 _) impossible
not_odd_0 odd_0 = absurd odd_0

even_suc : Even (S n) -> Odd n
even_suc (E1 odd_n) = odd_n

odd_suc : Odd (S n) -> Even n
odd_suc (O1 even_n) = even_n

-- Equational reasoning looks natural, when dealing with implications.

mutual

  even_even : Even m -> Even n -> Even (m + n)
  even_even {m=Z} {n=n} E0 =
    (Even n) QED
  even_even {m=S k} {n=n} (E1 odd_k) =
    (Even n)
      ={ odd_even odd_k }=
    (Odd (k + n))
       ={ E1 }=
    (Even (S (k + n)))
    QED

  odd_even : Odd m -> Even n -> Odd (m + n)
  odd_even {m=Z} {n=_} (O1 _) impossible
  odd_even {m=(S k)} {n=n} (O1 even_k) =
    (Even n)
      ={ even_even even_k }=
    (Even (k + n))
      ={ O1 }=
    (Odd (S (k + n)))
    QED

--
-- Injectivity of `dbl`.
--

dbl : Nat -> Nat
dbl Z = Z
dbl (S n) = S (S (dbl n))

-- "Correctness"

dbl_correct : (n : Nat) -> dbl n = n + n
dbl_correct Z = Refl
dbl_correct (S n) =
  (dbl (S n))
    ={ Refl }=
  (S (S (dbl n)))
    ={ cong {f=S . S} (dbl_correct n) }=
  (S (S (n + n)))
    ={ cong {f=S} (plusSuccRightSucc n n) }=
  (S (n + S n))
    ={ Refl }=
  (S n + S n)
  QED

-- Now let us prove this:

dbl_injective : (m, n : Nat) -> dbl m = dbl n -> m = n
dbl_injective Z Z Refl = Refl
dbl_injective Z (S _) Refl impossible
dbl_injective (S _) Z Refl impossible
dbl_injective (S m) (S n) h =
  -- This is short, but looks like a mystery.
  cong {f=S} (dbl_injective m n (cong {f=Nat.pred . Nat.pred} h))

-- Let us try to rewrite the above proof in a more "human-friendly" form
-- by using "equational reasoning.
-- The point is that, in this proof we have to deal with
--  a sequence of equations, rather than expressions.

dbl_injective' : (m, n : Nat) -> dbl m = dbl n -> m = n
dbl_injective' Z Z = (Z = Z) QED
dbl_injective' Z (S n) = \ z_s => absurd z_s
dbl_injective' (S m) Z = \ s_z => absurd (sym s_z)
dbl_injective' (S m) (S n) =
  -- Here ={ } corresponds to implication.
  (dbl (S m) = dbl (S n))
    ={ id }=
  (S (S (dbl m)) = S (S (dbl n)))
    ={ succInjective (S (dbl m)) (S (dbl n)) }=
  (S (dbl m) = S (dbl n))
    ={ succInjective (dbl m) (dbl n)  }=
  (dbl m = dbl n)
    ={ dbl_injective' m n }=
  (m = n)
    ={ cong {f=S} }=
  (S m = S n)
  QED
