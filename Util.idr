module Util

%default total

-- Implication is a preorder relation...

namespace Impl
  qed : (a : Type) -> (a -> a)
  qed a = id
  step : (a : Type) -> (p : a -> b) -> (q : b -> c) -> (a -> c)
  step a p q = q . p
