module Util

%default total

-- Implication is a preorder relation...

namespace Impl
  using (a, b, c : Type)
  qed : (a : Type) -> (a -> a)
  qed a = id
  step : (a : Type) -> (ab : a -> b) -> (bc : b -> c) -> (a -> c)
  step a ab bc = bc . ab
