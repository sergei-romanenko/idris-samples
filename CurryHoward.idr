module CurryHoward

%default total

-- Implication = `->`.

namespace SKI

  using (P : Type, Q : Type, R : Type)

    I : P -> P
    I x = x

    K : P -> Q -> P
    K x y = x

    S : (P -> Q -> R) -> (P -> Q) -> P -> R
    S x y z = (x z) (y z)

    I' : P -> P
    I' = S K (K {Q = P})

using (P : Type, Q : Type, R : Type)

  mp : (P -> Q) -> P -> Q
  mp f x = f x

  comp : (P -> Q) -> (Q -> R) -> P -> R
  comp f g x = g (f x)

  comp' : (P -> Q) -> (Q -> R) -> P -> R
  comp' f g = g . f

-- Conjunction = `Pair`.
-- A proof of (P , Q) is a proof of P and a proof of Q.

using (P : Type, Q : Type, R : Type)

  -- `Pair` is commutative.

  pair_comm : (P , Q) -> (Q , P)
  pair_comm (x, y) = (y, x)

  infixr 3 &&&

  (&&&) : (P -> Q) -> (P -> R) -> P -> (Q , R)
  f &&& g = \x => (f x, g x)

  pair_comm' : (P , Q) -> (Q , P)
  pair_comm' = snd &&& fst

-- Disjunction = `Either`
-- A proof of `Either P Q` is either a proof of P labeled with `Left` or
-- a proof of Q labeled with `Right`.

using (P : Type, Q : Type, R : Type)

  -- `Either` is commutative.

  either_comm : P `Either` Q -> Q `Either` P
  either_comm (Left p) = Right p
  either_comm (Right q) = Left q

  either_comm' : P `Either` Q -> Q `Either` P
  either_comm' = either Right Left

-- Distributivity of `Pair` over `Either`.

using (P : Type, Q : Type, R : Type)

  distrib_pe_1 :  (P , Either Q R) -> Either (P , Q) (P , R)
  distrib_pe_1 (p, (Left q)) = Left (p, q)
  distrib_pe_1 (p, (Right r)) = Right (p, r)

  distrib_pe_2 :  (P , Either Q R) -> Either (P , Q) (P , R)
  distrib_pe_2 (p, qr) =
    either (Left . MkPair p) (Right . MkPair p) qr

  -- The other direction.

  distrib_ep_1 : Either (P , Q) (P , R) -> (P , (Either Q R))
  distrib_ep_1 (Left (p, q)) = (p , (Left q))
  distrib_ep_1 (Right (p , r)) = (p , (Right r))

  distrib_ep_2 : Either (P , Q) (P , R) -> (P , (Either Q R))
  distrib_ep_2 = either (fst &&& (Left . snd))
                        (fst &&& (Right . snd))

-- True = `()` and has a trivial proof.

triviallyTrue : () -- Unit
triviallyTrue = () -- MkUnit

-- False = `Void` and has no proof.

-- triviallyFalse : Void
-- triviallyFalse = ?r

-- Negation = `Not`.

-- Not : Type -> Type
-- Not a = a -> Void

-- void : Void -> a
-- void _ impossible

-- Some basic facts about negation.

using (P : Type, Q : Type, R : Type)

  contradict : Not (P , Not P)
  contradict (p, np) = void (np p)
  
  contrapos : (P -> Q) -> Not Q -> Not P
  contrapos pq nq p = nq (pq p)

  -- We show that Peirce's law is equivalent to the Law of
  -- Excluded Middle (EM).

em_i_peirce : ((R : Type) -> Either R (Not R)) ->
  (P, Q : Type) -> ((P -> Q) -> P) -> P
em_i_peirce e P Q pq_p with (e P)
  | (Left p) = p
  | (Right np) = pq_p (\p => void (np p))

peirce_i_em : ((P, Q : Type) -> ((P -> Q) -> P) -> P) ->
  ((R : Type) -> Either R (Not R))
peirce_i_em h R =
  h (Either R (Not R)) Void
    (\r_nr => Right (\r => r_nr (Left r)))

-- Universal quantification. Given a type A, and a predicate P : A -> Type
--   (x : A) ->  P x means that (P a) is true (inhabited) for all (a : A).

all_pair_lem_1 : {A : Type} -> {P, Q : A -> Type} -> 
  ((a : A) -> (P a, Q a)) -> (((a : A) -> P a), ((a : A) -> Q a))
all_pair_lem_1 a_pq =
  ((\a => fst (a_pq a)), (\a => snd (a_pq a)))

all_pair_lem_2 : {A : Type} -> {P, Q : A -> Type} -> 
  (((a : A) -> P a) , ((a : A) -> Q a)) -> ((a : A) -> (P a, Q a)) 
all_pair_lem_2 (a_p, a_q) a =
  (a_p a, a_q a)

-- Existence. Given a type A, and a predicate P : A -> Type,
-- `DPair A P` is the type of dependent pairs MkDPair x f, such that
--  then (x : A) and (px : P x).
-- `(a : A ** P)` means `(a : DPair A (\a => P a)`
-- `a ** p` means `MkDPair a (\a => p)`

using (A : Type, P : A -> Type, Q : Type)

  all_ex_lem_1 : ((a : A) -> P a -> Q) -> (a ** P a) -> Q
  all_ex_lem_1 a_pa_q (a ** pa) = a_pa_q a pa

  all_ex_lem_2 : ((a ** P a) -> Q) -> (a : A) -> P a -> Q
  all_ex_lem_2 a'pa_q a pa = a'pa_q (a ** pa)

using (a : Type, P : a -> Type, Q : Type)

  frobenius_to : (x ** (Q, P x)) -> (Q, (x ** P x))
  frobenius_to (x ** (q , px)) = (q, (x ** px))

  frobenius_from : (Q, (x ** P x)) -> (x ** (Q, P x))
  frobenius_from (q, (x ** px)) = (x ** (q, px))
