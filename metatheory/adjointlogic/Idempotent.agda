{-
  module IdempotentMonad where
    postulate
      m    : Mode
      T    : m ≥ m
      unit : 1m ⇒ T
      mult : (T ·1 T) ⇒ T 
      -- monad laws for unit and mult
      -- equations that mult and l(unit) are mutually inverse
-}
