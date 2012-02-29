{-# OPTIONS --type-in-type --without-K #-}
open import lib.Prelude 
open Paths

module applications.Pi1S1 where

  succA : AEq Int Int
  succA = (isoToAdj (succ , isiso pred succ-pred pred-succ))

  predA : AEq Int Int
  predA = isoToAdj (pred , isiso succ pred-succ succ-pred)

  succP : Int ≃ Int
  succP = ua succA

  predP : Int ≃ Int
  predP = ua predA

  succP-! : (! succP) ≃ predP 
  succP-! = !-adj succ (snd succA) (snd predA) 

  C : S¹ -> Set
  C = S¹-rec Int succP

  subst-C-loop : subst C loop ≃ succ
  subst-C-loop = subst C loop                  ≃〈 subst-resp C loop 〉
                 subst (λ x → x) (resp C loop) ≃〈 resp (subst (λ x → x)) (βloop/rec Int succP) 〉 
                 subst (λ x → x) succP         ≃〈 subst-univ _ 〉 
                 succ ∎

  subst-C-!loop : subst C (! loop) ≃ pred
  subst-C-!loop = (subst C (! loop) ≃〈 subst-resp C (! loop) 〉
                   subst (λ x → x) (resp C (! loop)) ≃〈 resp (subst (λ x → x)) (resp-! C loop)〉
                   subst (λ x → x) (! (resp C loop)) ≃〈 resp (λ y → subst (λ x → x) (! y)) (βloop/rec Int succP) 〉
                   subst (λ x → x) (! succP) ≃〈 resp (subst (λ x → x)) succP-! 〉
                   subst (λ x → x) predP ≃〈 subst-univ _ 〉 
                   (pred ∎))

  loop^ : Int -> base ≃ base
  loop^ Zero = Refl
  loop^ (Neg Z) = ! loop
  loop^ (Neg (S n)) = ! loop ∘ loop^ (Neg n)
  loop^ (Pos Z) = loop
  loop^ (Pos (S n)) = loop ∘ loop^ (Pos n)

  encode : ∀ {a} -> base ≃ a -> C a
  encode p = subst C p Zero

  encode-loop^ : (n : Int) -> encode (loop^ n) ≃ n
  encode-loop^ Zero = Refl
  encode-loop^ (Pos Z) = app≃ subst-C-loop
  encode-loop^ (Pos (S y)) = 
    subst C (loop ∘ loop^ (Pos y)) Zero         ≃〈 app≃ (subst-∘ C loop (loop^ (Pos y)) ) 〉
    subst C loop (subst C (loop^ (Pos y)) Zero) ≃〈 app≃ subst-C-loop 〉
    succ (subst C (loop^ (Pos y)) Zero)         ≃〈 resp succ (encode-loop^ (Pos y)) 〉 
    succ (Pos y) ∎
  encode-loop^ (Neg Z) = app≃ subst-C-!loop
  encode-loop^ (Neg (S y)) = 
    subst C (! loop ∘ loop^ (Neg y)) Zero            ≃〈 app≃ (subst-∘ C (! loop) (loop^ (Neg y))) 〉
    subst C (! loop) (subst C (loop^ (Neg y)) Zero) ≃〈 app≃ subst-C-!loop 〉
    pred (subst C (loop^ (Neg y)) Zero)             ≃〈 resp pred (encode-loop^ (Neg y)) 〉 
    pred (Neg y) ∎

  -- stuck : {p : base ≃ base} -> p ≃ loop^ (encode p)
  -- stuck = {!!} no way to use J directly; need to generalize

  shift : (n : Int) -> (loop ∘ (loop^ (pred n))) ≃ loop^ n
  shift (Pos Z) = Refl
  shift (Pos (S y)) = Refl
  shift Zero = !-inv-r loop
  shift (Neg Z) = 
    ∘-unit-l _ ∘
    resp (λ x → x ∘ ! loop) (!-inv-r loop) 
    ∘ ∘-assoc loop (! loop) (! loop) 
  shift (Neg (S y)) = 
    loop ∘ ! loop ∘ ! loop ∘ loop^ (Neg y)    ≃〈 ∘-assoc loop (! loop) (! loop ∘ loop^ (Neg y)) 〉
    (loop ∘ ! loop) ∘ ! loop ∘ loop^ (Neg y)  ≃〈 resp (λ x → x ∘ ! loop ∘ loop^ (Neg y)) (!-inv-r loop) 〉
    Refl ∘ ! loop ∘ loop^ (Neg y)             ≃〈 ∘-unit-l _ 〉
    (! loop ∘ loop^ (Neg y) ∎) 

  decode : ∀ {a} -> C a -> base ≃ a
  decode {a} = S¹-elim {C = \ x -> C x -> base ≃ x} 
                       loop^ 
                       (subst (λ x' → C x' → base ≃ x') loop loop^ 
                        ≃〈 subst-→ C (Id base) loop loop^ 〉
                        (\ y -> subst (Id base) loop (loop^ (subst C (! loop) y))) 
                        ≃〈 λ≃ (λ y → subst-Id-post loop (loop^ (subst C (! loop) y))) 〉
                        (\ y -> loop ∘ (loop^ (subst C (! loop) y)))
                        ≃〈 λ≃ (λ y → resp (λ x' → loop ∘ loop^ x') (app≃ subst-C-!loop)) 〉
                        (\ y -> loop ∘ (loop^ (pred y)))
                        ≃〈 λ≃ shift 〉 
                        (λ y → loop^ y) ∎)
                       a

  decode-encode : ∀ {a} -> (p : base ≃ a) -> decode (encode p) ≃ p
  decode-encode {a} p = jay1 (λ a' p' → decode (encode p') ≃ p') p Refl

  theorem : Id base base ≃ Int
  theorem = ua (isoToAdj (encode , isiso decode encode-loop^ decode-encode))

  -- all paths from base to base are homotopic to loop^n for some n computed from p
  all-loops : (p : base ≃ base) -> p ≃ loop^ (subst C p Zero) 
  all-loops p = ! (decode-encode p)

{- could also prove:
  encode-decode : ∀ {a} -> (n : C a) -> encode{a} (decode n) ≃ n
  encode-decode {a} = S¹-elim {C = λ a' → (n' : C a') → encode {a'} (decode n') ≃ n'} 
                              encode-loop^ 
                              {!!} a
-}

  -- why is it enough to check the composition for Refl?
  -- obviously J says that it is, but what's going on?
  -- viewing it in terms of naturality is helpful

  module Why (A : Set) 
             (a : A) 
             (α : (x : A) -> a ≃ x -> a ≃ x) where

    nat : ∀ {b c} -> (q : b ≃ c) (p : a ≃ b)
        -> (α c (q ∘ p)) ≃ (q ∘ α b p) 
    nat {b}{c}q p = 
      α c (q ∘ p)                                        ≃〈 ! (app≃ (respd α q) {q ∘ p}) 〉                                   
      subst (λ x → a ≃ x → a ≃ x) q (α b) (q ∘ p)        ≃〈 (app≃ (subst-→ (Id a) (Id a) q (α b))) 〉                   
      subst (Id a) q (α b (subst (Id a) (! q) (q ∘ p)))  ≃〈 (subst-Id-post q (α b (subst (Id a) (! q) (q ∘ p))))  〉   
      q ∘ (α b (subst (Id a) (! q) (q ∘ p)))              ≃〈 (resp (λ x → q ∘ (α b x)) (subst-Id-post (! q) (q ∘ p)))  〉 
      q ∘ (α b (! q ∘ (q ∘ p)))                           ≃〈 (resp (λ x → q ∘ α b x) (∘-assoc (! q) q p))  〉
      q ∘ (α b ((! q ∘ q) ∘ p))                           ≃〈 (resp (λ x → q ∘ α b (x ∘ p)) (!-inv-l q))  〉             
      q ∘ (α b (Refl ∘ p))                                ≃〈 (resp (λ x → q ∘ α b x) (∘-unit-l p)) 〉                    
      q ∘ α b p                                          
      ∎

    commute : (loop2 loop1 : a ≃ a) 
             -> (α a (loop2 ∘ loop1)) ≃ (loop2 ∘ (α a loop1))
    commute loop2 loop1 = nat loop2 loop1

    alternate-proof : (α a Refl ≃ Refl) 
                    -> (loop : a ≃ a) -> (α a loop ≃ loop)
    alternate-proof worksForRefl loop = 
      α a loop           ≃〈 resp (λ x → α a x) (∘-unit-r loop) 〉
      α a (loop ∘ Refl)  ≃〈 commute loop Refl 〉
      loop ∘ α a Refl    ≃〈 resp (_∘_ loop) worksForRefl 〉 
      loop ∘ Refl        ≃〈 ∘-unit-r loop 〉 
      loop ∎
             

    