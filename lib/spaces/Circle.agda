{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 

module lib.spaces.Circle where

module S¹ where
  private
    module S where
      private
        data S¹' : Type where
          Base : S¹'

        data S¹'' : Type where
          mkS¹'' : S¹' → (Unit -> Unit) → S¹''
    
      S¹ : Type
      S¹ = S¹''
    
      base : S¹
      base = mkS¹'' Base _
    
      postulate {- HoTT Axiom -}
        loop : Path base base
    
      S¹-rec : {C : Type} 
             -> (c : C)
             -> (α : c ≃ c)
             -> S¹ -> C
      S¹-rec a _ (mkS¹'' Base _) = a
    
      S¹-elim :  (C : S¹ -> Type)
              -> (c : C base) 
                 (α : Path (transport C loop c) c)
              -> (x : S¹) -> C x
      S¹-elim _ x _ (mkS¹'' Base _) = x
  
      S¹-induction :  (C : S¹ -> Type)
              -> (c : C base) 
                 (α : Path (transport C loop c) c)
              -> (x : S¹) -> C x
      S¹-induction = S¹-elim
    
      postulate {- HoTT Axiom -} 
        βloop/rec : {C : Type} 
             -> (c : C)
             -> (α : Path c c)
             -> Path (ap (S¹-rec c α) loop) α
    
        βloop/elim : {C : S¹ -> Type} 
                   -> (c : C base) (α : Path (transport C loop c) c)
                   -> Path (apd (S¹-induction C c α) loop) α

  open S public

  {-
  bad : (p : Path base base) -> Path p id
  bad id = id
   /Users/drl/work/cmu/rsh/progind/code/hott-me/lib/spaces/Circle.agda:57,7-9
   The indices
     .lib.spaces.Circle.S¹.S.S¹''.mkS¹''
     .lib.spaces.Circle.S¹.S.S¹'.Base (λ _ → <>)
   are not constructors (or literals) applied to variables (note that
   parameters count as constructor arguments)
   when checking that the pattern id has type Path base base
  -}

  -- Equivalence between (S¹ -> X) and Σe X (\ x → Id x x)
  η-rec : {C : Type} 
            (M : S¹ -> C)
            (N : S¹)
          -> M N ≃ (S¹-rec (M base) (ap M loop) N)
  η-rec {C} M N = S¹-elim (λ x → M x ≃ S¹-rec (M base) (ap M loop) x)
                          id 
                          (!-inv-r (ap M loop) 
                           ∘ ap (λ x → ap M loop ∘ x) (∘-unit-l (! (ap M loop)))
                           ∘ ap (λ x → x ∘ id ∘ ! (ap M loop)) (βloop/rec {C} (M base) (ap M loop))
                           ∘ transport-Path M (S¹-rec (M base) (ap M loop)) loop id
                          )
                          N 

  η-elim : {C : S¹ -> Type} 
          (M : (x : S¹) -> C x)
          (N : S¹)
        -> M N ≃ (S¹-elim C (M base) (apd M loop) N)
  η-elim {C} M N = S¹-elim (λ x → M x ≃ S¹-elim C (M base) (apd M loop) x)
                          id 
                          (!-inv-r (apd M loop) 
                           ∘ ap (λ x → apd M loop ∘ x) (∘-unit-l (! (apd M loop)))
                           ∘ ap (λ x → x ∘ id ∘ ! (apd M loop)) (βloop/elim {C} (M base) (apd M loop))
                           ∘ transport-Path-d M (S¹-elim _ (M base) (apd M loop)) loop id)
                          N 

  fromgen : {X : Type} -> Σ[ x ∶ X ] (Id x x) -> (S¹ -> X)
  fromgen (fst , snd) = S¹-rec fst snd

  togen : {X : Type} -> (S¹ -> X) -> Σ[ x ∶ X ] (Id x x)
  togen {X} f = f base , ap f loop

  fromto : {X : Type} -> (fromgen o togen) ≃ (λ (f : S¹ -> X) → f)
  fromto {X} = λ≃ (λ f → λ≃ (λ x → ! (η-rec f x)))

  tofrom : {X : Type} -> (togen o fromgen) ≃ (λ (f : Σ[ x ∶ X ] (Id x x)) → f)
  tofrom {X} = λ≃ (λ x → 
    (fst x , ap (S¹-rec (fst x) (snd x)) loop) 
           ≃〈 ap (λ y → fst x , y) (βloop/rec (fst x) (snd x)) 〉
    (fst x , snd x) 
           ≃〈 id 〉
    id)

  ump-eqv : {X : Type} → Equiv (S¹ -> X) (Σ[ x ∶ X ] (Id x x))
  ump-eqv = (improve (hequiv togen 
                              fromgen 
                              (λ x → ap≃ fromto) 
                              (λ y → ap≃ tofrom)))

  ump : {X : Type} -> (S¹ -> X) ≃ (Σ[ x ∶ X ] (Id x x))
  ump {X} = ua ump-eqv


{-
  module Reverse where

    reverse : S¹ → S¹
    reverse = S¹-rec base (! loop)

    P : (x : S¹) -> Path base x -> Type
    P = S¹-induction
        _
        (λ α → ap reverse α ≃ ! α) 
        (λ≃ (λ α → 
         (ap reverse (! loop ∘ α) ≃ ! (! loop ∘ α) ≃〈 {!!} 〉
          ap reverse (! loop ∘ α) ≃ ! α ∘ (! (! loop)) ≃〈 {!!} 〉
          ap reverse (! loop ∘ α) ≃ ! α ∘ loop ≃〈 {!!} 〉
          ap reverse (! loop ∘ α) ∘ ! loop ≃ α ≃〈 {!!} 〉
          ap reverse (! loop) ∘ ap reverse α ∘ ! loop ≃ α ≃〈 {!!} 〉
          loop ∘ ap reverse α ∘ ! loop ≃ α ≃〈 {!!} 〉
          ap reverse α ≃ ! α ∎) ∘
         ap (λ α' → ap reverse α' ≃ ! α') (transport-Path-right (! loop) α) ∘
         ap≃ (transport-constant loop) ∘
         ap≃ (transport-→ (Path base) (λ _ → Type) loop (λ α' → ap reverse α' ≃ ! α'))))

    reverse-is-inverse : (α : base ≃ base) → ap reverse α ≃ ! α 
    reverse-is-inverse α = path-induction P id α
-}

  


