-- attempt to do Pi1(S1) by proving that Hfiber loop^ is Contractible directly,
-- using the same template as Blakers-Massey.
-- got very complicated, so I switched to trying to prove that loop^ is 0-connected
-- in the version in the directory above this.  

{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.cubical.Cubical
open Int

module homotopy.blakersmassey.Pi1S1 where

  open S¹ using (S¹-elimo; S¹; S¹-rec)

  loop^ : Int → Path S¹.base S¹.base
  loop^ Zero        = id
  loop^ (Pos One)   = S¹.loop
  loop^ (Pos (S n)) = S¹.loop ∘ loop^ (Pos n)
  loop^ (Neg One)   = ! S¹.loop
  loop^ (Neg (S n)) = ! S¹.loop ∘ loop^ (Neg n)

  Codes-eqv : (p : S¹.base == S¹.base) → (HFiber loop^ p) == (HFiber loop^ (S¹.loop ∘ p))
  Codes-eqv p = apΣ (ua succEquiv) (λ≃ {!!})

  CodesWithDecode : (x : S¹) → S¹.base == x → Type
  CodesWithDecode = S¹-elimo _ (λ p → HFiber loop^ p) 
                               (coe (! PathOverΠ-NDrange) (λ p q s → {!PathOver=.out-PathOver-= s!}))

  encode : (x : S¹) (p : S¹.base == x) → (CodesWithDecode x p)
  encode x p = transport (\ p → CodesWithDecode (fst p) (snd p)) 
                         (pair= p (PathOver=.in-PathOver-= (whisker-square id (! (ap-constant _ p)) (! (ap-id p)) id connection)))
                         (Zero , id)

  encode-loop^ : (k : Int) → Path (encode _ (loop^ k)) (k , id)
  encode-loop^ (Pos One) = {!!}
  encode-loop^ (Pos (S n)) = {!encode-loop^ (Pos n)!}
  encode-loop^ Zero = id
  encode-loop^ (Neg n) = {!!}

  -- Codes-eq : (x : S¹) (p : S¹.base == x) (y : CodesWithDecode x p) 
  --          → Path (Codes-center x p) y
  -- Codes-eq .S¹.base id (x , r) = {!!}

  Codes-eq-base : (p : S¹.base == S¹.base) (c : CodesWithDecode S¹.base p) → Path (encode S¹.base p) c
  Codes-eq-base .(loop^ y) (y , id) = encode-loop^ y

  Codes-eq-loop : ∀ {p q} {α : Path (S¹.loop ∘ p) q}
                  {x : CodesWithDecode S¹.base p} {y : CodesWithDecode S¹.base q}
                  {β : transport (λ v → CodesWithDecode (fst v) (snd v)) (pair= S¹.loop (PathOverPathFrom.in-PathOver-= (whisker-square id id id α ∘-square))) x == y} →
    PathOver
      (λ v → Path (encode (fst (fst v)) (snd (fst v))) (snd v))
      (pair= (pair= S¹.loop (PathOverPathFrom.in-PathOver-= (whisker-square id id id α ∘-square))) (hom-to-over/left _ β)) (Codes-eq-base p x) (Codes-eq-base q y)
  Codes-eq-loop {α = id} {x = (k , id)} {β = id} = {!!}
  Codes-eq : (x : S¹) (p : S¹.base == x) (y : CodesWithDecode x p) 
           → Path (encode x p) y
  Codes-eq = S¹-elimo _ Codes-eq-base
                        (in-PathOverΠ (λ p q α → in-PathOverΠ (λ x y β → {!!}))) 

  Codes-contr : (x : S¹) (p : S¹.base == x) → Contractible (CodesWithDecode x p)
  Codes-contr x p = encode x p , Codes-eq x p

  thm : (α : S¹.base == S¹.base) → Contractible (HFiber loop^ α)
  thm α = Codes-contr S¹.base α
