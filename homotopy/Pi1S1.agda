
{-#  OPTIONS --type-in-type --without-K  #-}

open import lib.Prelude

open S¹
open Int
open LoopSpace
open Truncation

module homotopy.Pi1S1 where

  Cover : S¹ → Type
  Cover x = S¹-rec Int (ua succEquiv) x
  
  transport-Cover-loop : Path (transport Cover loop) succ
  transport-Cover-loop = 
    transport Cover loop                  
      ≃〈 transport-ap-assoc Cover loop 〉
    transport (λ x → x) (ap Cover loop)
      ≃〈 ap   (transport (λ x → x))
              (βloop/rec Int (ua succEquiv)) 〉 
    transport (λ x → x) (ua succEquiv)
      ≃〈 type≃β _ 〉 
    succ ∎
  
  transport-Cover-!loop : Path (transport Cover (! loop)) pred
  transport-Cover-!loop = 
    transport Cover (! loop)                             
      ≃〈 transport-ap-assoc Cover (! loop) 〉
    transport (λ x → x) (ap Cover (! loop))             
      ≃〈 ap (transport (λ x → x)) (ap-! Cover loop)〉
    transport (λ x → x) (! (ap Cover loop)) 
      ≃〈 ap  (λ y → transport (λ x → x) (! y))
             (βloop/rec Int (ua succEquiv)) 〉
    transport (λ x → x) (! (ua succEquiv))                     
      ≃〈 ap (transport (λ x → x)) (!-ua succEquiv) 〉
    transport (λ x → x) (ua (!equiv succEquiv)) 
      ≃〈 type≃β _ 〉
    pred ∎
  
  encode : {x : S¹} →  Path base x  →  Cover x
  encode α = transport Cover α Zero
  
  encode' : Path base base → Int
  encode' α = encode {base} α
  
  loop^ : Int → Path base base
  loop^ Zero        = id
  loop^ (Pos One)   = loop
  loop^ (Pos (S n)) = loop ∘ loop^ (Pos n)
  loop^ (Neg One)   = ! loop
  loop^ (Neg (S n)) = ! loop ∘ loop^ (Neg n)
  
  loop^-preserves-pred 
    : (n : Int) → Path (loop^ (pred n)) (! loop ∘ loop^ n)
  loop^-preserves-pred (Pos One) = ! (!-inv-l loop)
  loop^-preserves-pred (Pos (S y)) = 
       ! (∘-assoc (! loop) loop (loop^ (Pos y))) 
     ∘ ! (ap (λ x → x ∘ loop^ (Pos y)) (!-inv-l loop)) 
     ∘ ! (∘-unit-l (loop^ (Pos y)))
  loop^-preserves-pred Zero = id
  loop^-preserves-pred (Neg One) = id
  loop^-preserves-pred (Neg (S y)) = id

  decode : {x : S¹} → Cover x → Path base x
  decode {x} = 
   S¹-induction 
    (λ x' → Cover x' → Path base x')
    loop^
    loop^-respects-loop 
    x where
     abstract -- prevent Agda from normalizing
      loop^-respects-loop : transport (λ x' →  Cover x' → Path base x') loop loop^ ≃ (λ n → loop^ n) 
      loop^-respects-loop = 
         (transport (λ x' →  Cover x' → Path base x') loop loop^  ≃〈 transport-→ Cover (Path base) loop loop^ 〉
        
            transport (λ x' → Path base x') loop 
          o loop^ 
          o transport Cover (! loop)                              ≃〈 λ≃ (λ y → transport-Path-right loop (loop^ (transport Cover (! loop) y))) 〉
       
            (λ p → loop ∘ p) 
          o loop^ 
          o transport Cover (! loop)                              ≃〈 λ≃ (λ y → ap (λ x' → loop ∘ loop^ x') (ap≃ transport-Cover-!loop)) 〉
       
            (λ p → loop ∘ p)
          o loop^ 
          o pred                                                  ≃〈 id 〉 
       
          (λ n → loop ∘ (loop^ (pred n)))                         ≃〈 λ≃ (λ y → move-left-! _ loop (loop^ y) (loop^-preserves-pred y)) 〉 
       
          (λ n → loop^ n)
          ∎)

  abstract -- prevent Agda from normalizing
    encode-loop^ : (n : Int) → Path (encode (loop^ n)) n
    encode-loop^ Zero = id
    encode-loop^ (Pos One) = ap≃ transport-Cover-loop
    encode-loop^ (Pos (S n)) = 
      encode (loop^ (Pos (S n)))
        ≃〈 id 〉 
      transport Cover (loop ∘ loop^ (Pos n)) Zero
        ≃〈 ap≃ (transport-∘ Cover loop (loop^ (Pos n))) 〉 
      transport  Cover loop 
                 (transport Cover (loop^ (Pos n)) Zero)      
        ≃〈 ap≃ transport-Cover-loop 〉
      succ (transport Cover (loop^ (Pos n)) Zero)                      
        ≃〈 id 〉 
      succ (encode (loop^ (Pos n))) 
        ≃〈 ap succ (encode-loop^ (Pos n)) 〉 
      succ (Pos n) ∎
    encode-loop^ (Neg One) = ap≃ transport-Cover-!loop
    encode-loop^ (Neg (S n)) = 
      transport Cover (! loop ∘ loop^ (Neg n)) Zero                    
        ≃〈 ap≃ (transport-∘ Cover (! loop) (loop^ (Neg n))) 〉
      transport Cover (! loop) (transport Cover (loop^ (Neg n)) Zero)  
        ≃〈 ap≃ transport-Cover-!loop 〉
      pred (transport Cover (loop^ (Neg n)) Zero) 
        ≃〈 ap pred (encode-loop^ (Neg n)) 〉 
      pred (Neg n) ∎

  encode-decode  : {x : S¹} → (c : Cover x)
                 → Path (encode (decode{x} c)) c
  encode-decode {x} = S¹-induction
     (\ (x : S¹) →  (c : Cover x) 
                    → Path (encode{x} (decode{x} c)) c)
     encode-loop^ (λ≃ (λ x' → fst (use-level (use-level (use-level HSet-Int _ _) _ _)))) x 

  decode-encode  : {x : S¹} (α : Path base x)
                 → Path (decode (encode α)) α
  decode-encode {x} α = 
   path-induction 
    (λ  (x' : S¹) (α' : Path base x') 
        → Path (decode (encode α')) α')
    id α

  all-loops : (α : Path base base) → Path α (loop^ (encode α))
  all-loops α = ! (decode-encode α)
  
  
  -- equivalence for loop spaces
  
  Ω₁[S¹]-Equiv-Int : Equiv (Path base base) Int
  Ω₁[S¹]-Equiv-Int = 
     improve (hequiv encode decode decode-encode encode-loop^)

  Ω₁[S¹]-is-Int : (Path base base) ≃ Int
  Ω₁[S¹]-is-Int = ua Ω₁[S¹]-Equiv-Int

  π₁[S¹]-is-Int : π One S¹ base ≃ Int
  π₁[S¹]-is-Int = UnTrunc.path _ _ HSet-Int ∘ ap (Trunc (tl 0)) Ω₁[S¹]-is-Int


  -- fiberwise equivalence

  S¹-Path-Equiv-Cover : (y : S¹) → Equiv (Path base y) (Cover y)
  S¹-Path-Equiv-Cover y = improve (hequiv encode decode decode-encode (encode-decode{y}))

  S¹-Path≃Cover : (y : S¹) → (Path base y) ≃ (Cover y)
  S¹-Path≃Cover y = ua (S¹-Path-Equiv-Cover y)


  -- preserves composition
  
  loop^-preserves-succ : (n : Int) 
                       → Path (loop^ (succ n)) (loop ∘ loop^ n)
  loop^-preserves-succ n = 
      loop^ (succ n) 
        ≃〈 move-right-!  loop (loop^ (succ n)) _ 
                        (! (loop^-preserves-pred (succ n))) 〉 
      loop ∘ (loop^ (pred (succ n))) 
        ≃〈 ap (λ x → loop ∘ loop^ x) (pred-succ n) 〉 
      loop ∘ (loop^ n) ∎
  
  preserves-composition : (n m : Int)
                        → Path (loop^ (n + m)) (loop^ n ∘ loop^ m)
  preserves-composition (Pos One) m = loop^-preserves-succ m
  preserves-composition (Pos (S n)) m =  
      ∘-assoc loop (loop^ (Pos n)) (loop^ m) 
    ∘ ap (λ x → loop ∘ x) (preserves-composition (Pos n) m) 
    ∘ loop^-preserves-succ (Pos n + m)
  preserves-composition Zero m = ! (∘-unit-l _)
  preserves-composition (Neg One) m = loop^-preserves-pred m
  preserves-composition (Neg (S n)) m = 
      ∘-assoc (! loop) (loop^ (Neg n)) (loop^ m) 
    ∘ ap (λ x → ! loop ∘ x) (preserves-composition (Neg n) m) 
    ∘ loop^-preserves-pred (Neg n + m) 



  -- tlevel stuff

  Cover-is-HSet : ∀ y → HSet (Cover y)
  Cover-is-HSet = S¹-elim _ Int.HSet-Int (HProp-unique (NType-is-HProp _) _ _)

  S¹-is-Gpd : NType (tl 1) S¹
  S¹-is-Gpd = ntype hset-path where
    hset-path : (x y : _) → HSet (Path{S¹} x y)
    hset-path = S¹-elim _ 
                (λ y → transport (λ P → HSet (P y)) (! (λ≃ S¹-Path≃Cover)) (Cover-is-HSet y)) 
                (λ≃ (λ x → HProp-unique (NType-is-HProp _) _ _))

