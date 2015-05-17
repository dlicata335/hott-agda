{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 
open import lib.cubical.Cubical
import lib.PrimTrustMe

module lib.spaces.Circle where

module S¹ where
  private
    module S where
      private
        data ##S¹ : Type where
          #base : ##S¹

        data #S¹ : Type where
          #in : (Unit -> ##S¹) → #S¹

        #out : #S¹ -> ##S¹
        #out (#in f) = f <>

        ext : (x : #S¹) (y : ##S¹) → #out x == y → #in (\ _ -> y) == x
        ext (#in f) y p = lib.PrimTrustMe.transport/PId (λ x → #in (λ _ → y) == x) (lib.PrimTrustMe.ap/PId #in (lib.PrimTrustMe.funext/primtrustme {f = λ _ → y} {g = f} (λ _ → transport (λ z → lib.PrimTrustMe.PId y z) (! p) lib.PrimTrustMe.Refl))) id 
    
      S¹ : Type
      S¹ = #S¹
    
      base : S¹
      base = #in(\ _ -> #base)
    
      postulate {- HoTT Axiom -}
        loop : Path base base
    
      S¹-rec : {C : Type} 
             -> (c : C)
             -> (α : c ≃ c)
             -> S¹ -> C
      S¹-rec {C} a α x = S¹-rec' Phantom.phantom (#out x) where
        S¹-rec' : (_ : Phantom α) -> ##S¹ -> C
        S¹-rec' (Phantom.phantom) #base = a

      S¹-elim :  (C : S¹ -> Type)
              -> (c : C base) 
                 (α : Path (transport C loop c) c)
              -> (x : S¹) -> C x
      S¹-elim C c α x = S¹-elim' (Phantom.phantom) (#out x) id where
        S¹-elim' : (_ : Phantom α) -> (x' : ##S¹) -> x' == #out x -> C x
        S¹-elim' (Phantom.phantom) #base p = transport C (ext _ _ (! p)) c
  
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
  without the Unit->A trick, you can prove

  uip-base : (p : Path base base) -> Path p id
  uip-base id = id
  -}

  {- 
  without the Phantom trick, you can prove

  path-irrel : {C : Type} {c : C} {p q : c ≃ c} → S¹-rec c p ≃ S¹-rec c q
  path-irrel = id

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

  -- pathover version of eliminator

  S¹-elimo :  (C : S¹ -> Type)
              -> (c : C base) 
                 (α : PathOver C loop c c)
              -> (x : S¹) -> C x
  S¹-elimo C c α x = S¹-elim C c (over-to-hom/left α) x

  abstract
    βloop/elimo :  (C : S¹ -> Type)
                -> (c : C base) 
                   (α : PathOver C loop c c)
                -> apdo (S¹-elimo C c α) loop == α
    βloop/elimo C c α = (IsEquiv.β (snd hom-to-over/left-eqv) α ∘
                           ap (hom-to-over/left loop) (βloop/elim c (over-to-hom/left α))) ∘ apdo-apd (S¹-elimo C c α) loop

{-
  S¹-rec1 : {C : Type} {c1 c2 : C} (α12 : c1 == c2)
             {α1 : c1 == c1} {α2 : c2 == c2}  (s : Square α1 α12 α12 α2) 
          → {p1 p2 : S¹} → (p1 == p2)
          → S¹-rec c1 α1 p1 == S¹-rec c2 α2 p2
  S¹-rec1 {c1 = c1} id s {p1 = p1} id = ap (λ z → S¹-rec c1 z p1) (horiz-degen-square-to-path s)

  S¹-rec1/βloop : {C : Type} {c1 c2 : C} (α12 : c1 == c2)
             {α1 : c1 == c1} {α2 : c2 == c2}  (s : Square α1 α12 α12 α2) 
          → S¹-rec1 α12 s S¹.loop == diag-square s
  S¹-rec1/βloop = {!!}

  ap-S¹-rec-is-1 : {A C : Type} {a1 a2 : A} (b : A → C) (l : (x : A) → b x == b x) (p : A → S¹)
             (α : a1 == a2) 
          → ap (\ x -> S¹-rec (b x) (l x) (p x)) α == S¹-rec1 (ap b α) (PathOver=.out-PathOver-= (apdo l α)) (ap p α)
  ap-S¹-rec-is-1 b l p id = {!id!}
-}

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


  


