
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open LoopSpace
open Int

module homotopy.in-progress.Pi4S3 where

  -- π4(S^3) = Ω3(τ3(Ω(S3)))
  -- so STS τ3(Ω(S3)) = X where π3(X) = 2
  -- since X must agree with Ω(S3) up to 3-truncation, 
  -- it must be that π1(X) = π1(Ω(S3)) = π2(S3) = 1
  --                 π2(X) = π2(Ω(S3)) = π3(S3) = Z

  module X where
    private 
      data X' : Type where
        base' : X'
  
    X : Type
    X = X'

    base : X
    base = base'
  
    postulate 
      loop2  : Loop (S One)     X base
      loop3  : Loop (S (S One)) X base
      order2 : loop3 ∘ loop3 ≃ id

    X-rec : {A : Type}
            (b' : A)
            (loop2' : Loop (S One) A b')
            (loop3' : Loop (S (S One)) A b')
            (order2' : loop3' ∘ loop3' ≃ id)
          → X -> A
    X-rec b' _ _ _ base' = b'

    X-elim : (C : X → Type)
            (b' : C base)
            (loop2' : LoopOver (S One) loop2 C b')
            (loop3' : LoopOver (S (S One)) loop3 C b')
            (order2' : {!coe (LoopOverS≃ (S One) loop3 C b') loop3'!} ≃ id)
          → (x : X) -> C x
    X-elim C b' _ _ _ base' = b'

  open X using (X ; X-rec ; X-elim)
  module S = NSphere1
  open S using (S^ ; S-rec ; S-elim)

  S³ = S^ (S (S One))

  generator : Loop (S (S (S One))) S³ S.base
  generator = {!!}

  order2 : generator ∘ generator ≃ id
  order2 = {!!}

  decode' : X → Path{S³} S.base S.base
  decode' = X-rec id (S.loop (S (S One))) generator order2

  Codes : S³ → Type
  Codes =
    S-rec X (λt (S One) 
      (X-elim _ 
              X.loop2 
              (coe (! (LoopOverS≃ One X.loop2 (Loop (S One) X) X.loop2))
                   (apt One (ap^ (S One) (Loop (S One) X) X.loop2) X.loop2 ≃〈 apt-apS One (Loop (S One) X) X.loop2 X.loop2 〉
                    ap (λ x → transport (Loop (S One) X) x X.loop2) X.loop2 ≃〈 {!!} 〉 
                    adj _ (ap (λ x → rebase (S One) x X.loop2) X.loop2) ≃〈 {!!} 〉 
                    id ∎))
              {!!}
              {!!})) 