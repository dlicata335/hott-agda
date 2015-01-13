

{-# OPTIONS --type-in-type --copatterns --without-K #-}

open import NoFunextPrelude

module Stream2 where

  record Stream (A : Type) : Type where
    coinductive
    field
      head : A
      tail : Stream A
  open Stream

  {-# NO_TERMINATION_CHECK #-}
  unfold : {A : Type} {X : Type} → (X → A × X) → X → Stream A 
  head (unfold f x) = fst (f x)
  tail (unfold f x) = unfold f (snd (f x))

  {-# NO_TERMINATION_CHECK #-}  
  map : {A B : Type} → (A → B) → (Stream A → Stream B)
  head (map f s) = f (head s)
  tail (map f s) = map f (tail s)

  postulate 
    map-id : {A : Type} → map {A} (\ x -> x) == (\ s -> s)
    map-o  : {A B C : Type} (g : B → C) (f : A → B) (s : Stream A) → map g (map f s) == map (g o f) s

  transport-Stream : {A B : Type} → (p : A == B) → transport Stream p == map (coe p)
  transport-Stream id = ! map-id
  
  Bisim : {A : Type} (xs : Stream A) (ys : Stream A) → Type 
  Bisim {A} xs ys = Σ \(p : Stream (Paths A)) → (map (fst o fst) p == xs) × (map (snd o fst) p == ys)

  Bisim2 : Type → Type
  Bisim2 A = (Σ \ xsys -> Bisim{A} (fst xsys) (snd xsys))
  
  module LastStep (A : Type) where
  
    to : Stream (Paths A) → Bisim2 A
    to s = (map ((λ r → fst r) o (λ r → fst r)) s , map ((λ r → snd r) o (λ r → fst r)) s) , s , id , id
  
    from : Bisim2 A → Stream (Paths A)
    from (_ , s , _) = s
  
    from-to : (p : _) → from (to p) == p
    from-to p = id
  
    to-from : (p : _) → to (from p) == p
    to-from ((._ , ._) , p , id , id) = id
  
    eqv : Equiv (Stream (Paths A)) (Bisim2 A)
    eqv = improve (hequiv to from from-to to-from)
  
  extt : {A : Type} → Equiv (Paths (Stream A)) (Bisim2 A)
  extt {A} =   Paths (Stream A) ≃〈 contract-Paths≃ {Stream A} 〉
               Stream A ≃〈 coe-equiv (ap Stream (! (ua (contract-Paths≃ {A})))) 〉
               Stream (Paths A) ≃〈 LastStep.eqv A 〉
               (Bisim2 A ∎∎)
  
  extt-id : {A : Type} (s : Stream A) → fst (fst extt ((s , s) , id)) == (s , s)
  extt-id s = fst
                (LastStep.to _
                 (coe (ap Stream (! (ua contract-Paths≃)))
                  (fst contract-Paths≃ ((s , s) , id))))
                =〈 id 〉
              fst
                (LastStep.to _
                 (coe (ap Stream (! (ua contract-Paths≃))) s)) =〈 ap (λ f → fst (LastStep.to _ (f s))) (transport-Stream (! (ua contract-Paths≃)) ∘ ! (transport-ap-assoc' (λ X → X) Stream (! (ua contract-Paths≃)))) 〉
              fst
                (LastStep.to _
                 (map (coe (! (ua contract-Paths≃))) s)) =〈 ap (λ f → fst (LastStep.to _ (map f s))) (type=β! contract-Paths≃) 〉
              fst
                (LastStep.to _
                 (map (\ x -> ((x , x) , id)) s)) =〈 ap2 _,_ (ap (λ f → f s) map-id ∘ map-o (fst o fst) (λ x → (x , x) , id) _) (ap (λ f → f s) map-id ∘ map-o (snd o fst) (λ x → (x , x) , id) _) 〉
              ((s , s) ∎)
  
  preserves-fst : ∀ {A} (α : Paths (Stream A)) → fst (fst extt α) == fst α
  preserves-fst ((s , .s) , id) = extt-id s
  
  ext : {A : Type} (s1 s2 : Stream A) → Equiv (s1 == s2) (Bisim s1 s2)
  ext s1 s2 = fiberwise-equiv-from-total≃ extt preserves-fst (s1 , s2)

  Bisim-heads : {A : Type} {xs ys : Stream A} → Bisim xs ys → head xs == head ys
  Bisim-heads (ps , (id , id)) = snd (head ps)

  Bisim-tails : {A : Type} {xs ys : Stream A} → Bisim xs ys → Bisim (tail xs) (tail ys)
  Bisim-tails (ps , (id , id)) = (tail ps , id , id)

  postulate
    Bisim-unfold : {A : Type} (X : Stream A → Stream A → Type)
               → (∀ xs ys → X xs ys → ((head xs) == (head ys)) × X (tail xs) (tail ys))
               → ∀ (xs ys : Stream A) → X xs ys → Bisim xs ys
  
  unfoldη : {A : Type} {X : Type} (f : X → A × X) (s : X → Stream A)
             → ((x : X) → head (s x) == fst (f x))
             → ((x : X) → tail (s x) == s (snd (f x)))
             → (x : X) → s x == unfold f x
  unfoldη f s b1 b2 x = IsEquiv.g (snd (ext _ _)) 
            (Bisim-unfold (λ xs ys → (head xs == head ys) × Unit)
                          (\ { xs ys p → fst p , {!!}})
                          _ _ (b1 x , {!!}))

{-
  Bisim-unfold-stream : {A : Type} (X : Stream A → Stream A → Type)
               → (∀ {xs ys} → X xs ys → ((head xs) == (head ys)) × X (tail xs) (tail ys))
               → ∀ (xs ys : Stream A) → X xs ys → Stream (Paths A)
  Bisim-unfold-stream X f xs ys x = 
    unfold {X = Σ \ xsys → X (fst xsys) (snd xsys)} 
           (λ {((xs , ys) , seed) → (_ , fst (f seed)) , _ , snd (f seed)})
           ((xs , ys) , x)

  Bisim-unfold X f xs ys x = Bisim-unfold-stream X f xs ys x , 
                               (!
                                (unfoldη {X = Σ \ xsys → X (fst xsys) (snd xsys)} 
                                 (λ x' →
                                    head (fst (fst x')) ,
                                    (tail (fst (fst x')) , tail (snd (fst x'))) , snd (f (snd x')))
                                 (fst o fst) (λ _ → id) (λ _ → id) ((xs , ys) , x))) ∘
                               map-unfold (fst o fst)
                               (λ { ((xs , ys) , seed) → (_ , fst (f seed)) , _ , snd (f seed) })
                               _ , 
                             !
                               (unfoldη {X = Σ (λ xsys → X (fst xsys) (snd xsys))} _ (snd o fst)
                                (λ _ → id) (λ _ → id) ((xs , ys) , x))
                               ∘
                               map-unfold (snd o fst)
                               (λ { ((xs , ys) , seed) → (_ , fst (f seed)) , _ , snd (f seed) })
                               _
-}
