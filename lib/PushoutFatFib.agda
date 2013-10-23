{-# OPTIONS --type-in-type --without-K #-}

-- pushout of a predicate P : X → Y → Type
-- includes a constructor for the "middle" space Z = Σ x,y.P(x,y).

open import lib.First
open import lib.NConnected
open import lib.Prods
open import lib.Functions
open import lib.Paths 
open import lib.NType
open import lib.Universe
open import lib.Truncations
open import lib.WEq
open Truncation

module lib.PushoutFatFib where

  module FatPushoutFib where

    module P where
      private
        data Pushout' {X Y : Type} (P : X → Y → Type) : Type where
          inl' : X → Pushout' P 
          inm' : (x : X) (y : Y) → P x y → Pushout' P
          inr' : Y → Pushout' P

      Pushout : {X Y : Type} (P : X → Y → Type) → Type 
      Pushout = Pushout'

      inl : ∀ {X Y}{P : X → Y → Type} → X → Pushout P
      inl = inl'

      inr : ∀ {X Y}{P : X → Y → Type} → Y → Pushout P
      inr = inr'

      inm : ∀ {X Y}{P : X → Y → Type} → (x : X) (y : Y) → P x y → Pushout P
      inm = inm'

      postulate {- HoTT Axiom -}
        gluel : ∀ {X Y} {P : X → Y → Type} (x : X) (y : Y) → (p : P x y) → Path{Pushout P} (inl x) (inm x y p)
        gluer : ∀ {X Y} {P : X → Y → Type} (x : X) (y : Y) → (p : P x y) → Path{Pushout P} (inm x y p) (inr y)

      Pushout-rec : {X Y : Type} {P : X → Y → Type} {C : Type}
                    (b1 : X → C)
                    (b2 : (x : X) (y : Y) (p : P x y) → C)
                    (b3 : Y → C)
                    (gluel' : (x : X) (y : Y) (p : P x y) → (b1 x) ≃ b2 x y p)
                    (gluer' : (x : X) (y : Y) (p : P x y) → (b2 x y p) ≃ b3 y)
                  → Pushout P → C
      Pushout-rec b1 _ _ _ _ (inl' x) = b1 x
      Pushout-rec _ b2 _ _ _ (inm' x y p) = b2 x y p
      Pushout-rec _ _ b3 _ _ (inr' y) = b3 y

{-
      FIXME: TODO: give the beta rules for paths
-}

      Pushout-elim : {X Y : Type} {P : X → Y → Type} (C : Pushout P → Type)
                    (b1 : (x : X) → C (inl x))
                    (b2 : (x : X) (y : Y) (p : P x y) → C (inm x y p))
                    (b3 : (y : Y) → C (inr y))
                    (gluel' : (x : X) (y : Y) (p : P x y) → transport C (gluel x y p) (b1 x) ≃ b2 x y p)
                    (gluer' : (x : X) (y : Y) (p : P x y) → transport C (gluer x y p) (b2 x y p) ≃ b3 y)
                  → (z : Pushout P) → C z
      Pushout-elim _ b1 _ _ _ _ (inl' x) = b1 x
      Pushout-elim _ _ b2 _ _ _ (inm' x y p) = b2 x y p
      Pushout-elim _ _ _ b3 _ _ (inr' y) = b3 y

    open P public

{-

    FIXME: TODO: will need to edit the wedge to prod stuff for this definition

    Wedge : {A B : Type} (a0 : A) (b0 : B) → Type
    Wedge {A}{B} a0 b0 = Pushout {Unit}{A}{B} (\ _ -> a0) (\ _ -> b0)

    wedge-to-prod : ∀ {A B} {a0 : A} {b0 : B} → (Wedge a0 b0) → A × B
    wedge-to-prod {a0 = a0} {b0 = b0} = Pushout-rec (λ a → a , b0) (λ _ → a0 , b0) (λ b → a0 , b) (\ _ -> id) (\ _ -> id)

    module WedgeToProd {A B : Type} {m n : _} (a0 : A) (b0 : B) (cA : Connected (S m) A) (cB : Connected (S n) B) where

      i = wedge-to-prod {A}{B}{a0} {b0}

      i-ump : ConnectedMap.ConnectedMapUMP (plus2 m n) i
      i-ump P br = (λ ab → fst (ext (fst ab)) (snd ab)) ,
                   Pushout-elim _ (λ a → snd (ext a)) 
                                  (λ _ → transport (λ z' → fst (ext (fst (i z'))) (snd (i z')) ≃ br z') (gluel <>) (snd (ext a0)))
                                  (λ b → ap≃ (fst≃ ext-a0) {b})
                                  (λ _ → id)
                                  (λ _ → ext-a0-coh ∘
                                           ap≃
                                           (!
                                            (transport-∘ (λ z → fst (ext (fst (i z))) (snd (i z)) ≃ br z)
                                             (gluer _) (gluel _)))) where
        postulate
          br-glue-adj : (transport (λ z → fst (P (i z))) (gluer <> ∘ gluel <>)) ≃ (\ x -> x)
          --br-glue-adj = {!!}

        br-glue : br (inr b0) ≃ br (inl a0)
        br-glue = ap≃ br-glue-adj ∘ ! (apd br (gluer <> ∘ gluel <>))

        ext : (a : A) → Extensions.Extensions _ b0 (λ b → fst (P (a , b))) (br (inl a)) 
        ext = ConnectedFib.everywhere m {_}{a0} cA 
              (\ a -> (Extensions.Extensions-ntype cB b0 (λ b → (P (a , b))) (br (inl a))))
              ((λ b → br (inr b)) , br-glue)

        ext-a0 : (ext a0) ≃ ((λ b → br (inr b)) , br-glue)
        ext-a0 = (ConnectedFib.β m {_}{a0} cA 
                     (\ a -> (Extensions.Extensions-ntype cB b0 (λ b → (P (a , b))) (br (inl a))))
                     _)
        postulate
          ext-a0-coh : (transport (λ z → fst (ext (fst (i z))) (snd (i z)) ≃ br z)
                       (gluer <> ∘ gluel <>) (snd (ext a0)))
                       ≃ (ap≃ (fst≃ ext-a0) {b0})
        {-
        ext-a0-coh = move-left _ _ _
                       (move-right-right-! _ (ap≃ (fst≃ ext-a0)) _
                        (snd≃ ext-a0 ∘ ! (transport-Path-pre' (λ f → f b0) (fst≃ ext-a0) (snd (ext a0)))))
                       ∘ (transport (λ z → fst (ext (fst (i z))) (snd (i z)) ≃ br z) (gluer <> ∘ gluel <>) (snd (ext a0)) ≃〈 transport-Path-d (λ z → fst (ext (fst (i z))) (snd (i z))) (λ z → br z) (gluer _ ∘ gluel _) (snd (ext a0)) 〉

                          apd br (gluer <> ∘ gluel <>) 
                          ∘ ap (transport (λ z → fst (P (i z))) (gluer <> ∘ gluel <>)) (snd (ext a0))
                          ∘ ! (apd (λ z → fst (ext (fst (i z))) (snd (i z))) (gluer <> ∘ gluel <>))        ≃〈 {!apd (λ z → br z) (gluer <> ∘ gluel <>)!} 〉 

                          apd br (gluer <> ∘ gluel <>) 
                          ∘ (! (ap≃ br-glue-adj)
                             ∘ (snd (ext a0))
                             ∘ (ap≃ br-glue-adj))
                          ∘ ! (apd (λ z → fst (ext (fst (i z))) (snd (i z))) (gluer <> ∘ gluel <>))        ≃〈 {!(ap≃ br-glue-adj) ∘ ! (apd (λ z → fst (ext (fst (i z))) (snd (i z))) (gluer <> ∘ gluel <>))!} 〉 

                          (apd br (gluer <> ∘ gluel <>) 
                           ∘ ! (ap≃ br-glue-adj))
                          ∘ (snd (ext a0))
                          ∘ ((ap≃ br-glue-adj)
                             ∘ ! (apd (λ z → fst (ext (fst (i z))) (snd (i z))) (gluer <> ∘ gluel <>)))        ≃〈 {!!} 〉 

                          (! br-glue)
                          ∘ (snd (ext a0))
                          ∘ ((ap≃ br-glue-adj)
                             ∘ ! (apd (λ z → fst (ext (fst (i z))) (snd (i z))) (gluer <> ∘ gluel <>)))        ≃〈 {!!} 〉 

                          ! br-glue ∘ snd (ext a0) ∎) where
                    fact1 : (ap≃ br-glue-adj {fst (ext a0) b0}) ≃ (apd (λ z → fst (ext (fst (i z))) (snd (i z))) (gluer <> ∘ gluel <>))
                    fact1 = {!!}
        -}
{-
        ext2-for-b0 = transport (λ z' → fst (ext (fst (i z'))) (snd (i z')) ≃ br z')
                              (gluer <>)
                              (transport (λ z' → fst (ext (fst (i z'))) (snd (i z')) ≃ br z')
                                         (gluel <>)
                                         (snd (ext a0)))
    
        ext2 : Extensions.Extensions _ b0 (λ b → fst (ext a0) b ≃ br (inr b)) ext2-for-b0
        ext2 = ConnectedFib.everywhere n {_} {b0} cB
                 (λ b →
                    Extensions.Extensions-ntype cB b0
                    (λ b' → fst (ext a0) b' ≃ br (inr b') , {!fst (ext a0) b'!})
                    ext2-for-b0)
                 {!!} {!!}
-}
      ci : ConnectedMap.ConnectedMap (plus2 m n) i
      ci = ConnectedMap.ConnectedMap-from-UMP (plus2 m n) i i-ump 
{-
      first attempt:
      -- problem 1: doing it directly from truncation, rather than UMP; could maybe get around this?
      -- problem 2: not defining the cases in a way that makes the proofs easy;
      --            e.g. case2 and case1 can be defined to make the goal trivial

      -- FIXME move
      split×≃ : ∀ {A B} {a a' : A} {b b' : B} 
                 (C : (a , b) ≃ (a' , b') -> Type)
              -> ((α : a ≃ a') (β : b ≃ b') -> C (pair×≃ α β))
              -> (p : (a , b) ≃ (a' , b')) -> C p
      split×≃ C b id = b id id

      ci : ConnectedMap.ConnectedMap (plus2 m n) i
      ci (a , b) = ntype (fst (v a) b , Trunc-elim _ (λ _ → path-preserves-level Trunc-level) 
                                                     (λ {(w , α) → Pushout-elim
                                                                    (λ w' → (α' : _) → fst (v a) b ≃ [ w' , α' ])
                                                                    (λ a' → split×≃ _ case1)
                                                                    (λ z → split×≃ _ case2)
                                                                    (λ b' → split×≃ _ case3)
                                                                    (λ _ → λ≃ (split×≃ _ agree12) ∘
                                                                            transport-Π (λ w' → Path (i w') (a , b)) (λ w' α' → fst (v a) b ≃ [ w' , α' ]) (gluel _) (split×≃ _ case1))
                                                                    {!!}
                                                                    w
                                                                    α})) 
         where 
           v : (a : A) → ConnectedMap.Extensions _ b0 (λ b → (Trunc (plus2 m n) (HFiber i (a , b)))) [ inl a , id ]
           v = ConnectedFib.everywhere m {_} {a0} cA
                            (λ a' →
                               ConnectedMap.Extensions _ b0 (λ b' → (Trunc (plus2 m n) (HFiber i (a' , b'))))
                                               [ inl a' , id ]
                               , ConnectedMap.Extensions-level cB b0 (λ b' → Trunc (plus2 m n) (HFiber i (a' , b')) , Trunc-level) _)
                            ((λ b' → [ inr b' , id ]) , ap [_] (pair≃ (! (gluer <> ∘ gluel <>))
                                                               (transport (λ x → Path (i x) (a0 , b0)) (! (gluer <> ∘ gluel <>)) id ≃〈 transport-Path-pre' i (! (gluer <> ∘ gluel <>)) id 〉 
                                                                id ∘ ! (ap i (! (gluer <> ∘ gluel <>))) ≃〈 ∘-unit-l (! (ap i (! (gluer <> ∘ gluel <>)))) 〉 
                                                                ! (ap i (! (gluer <> ∘ gluel <>))) ≃〈 ! (ap-! i (! (gluer <> ∘ gluel <>))) 〉 
                                                                ap i (! (! (gluer <> ∘ gluel <>))) ≃〈 ap (ap i) (!-invol (gluer <> ∘ gluel <>)) 〉 
                                                                ap i (gluer <> ∘ gluel <>) ≃〈 ap-∘ i (gluer <>) (gluel <>) 〉 
                                                                ap i (gluer <>) ∘ ap i (gluel <>) ≃〈 {!β!} 〉 
                                                                ap i (gluer <>) ≃〈 {!β!} 〉 
                                                                id ∎)))

           -- FIXME: a little messy what these get abstracted over for path induction

           case1 : ∀ {a a' b'} (α' : a' ≃ a) (β : b0 ≃ b') → fst (v a) b' ≃ [ inl a' , pair×≃ α' β ]
           case1 {a} id id = snd (v a)


           case2-adjustment-0 : (transport (λ w' → Path (i w') (a0 , b0)) (! (gluel <>)) id) ≃ id
           case2-adjustment-0 = {!!}

           case2-adjustment-1 : (transport (λ w' → Path (i w') (a0 , b0)) (gluel <>) id) ≃ id
           case2-adjustment-1 = (transport (λ x → Path (i x) (a0 , b0)) (gluel <>) id ≃〈 ap≃ (transport-ap-assoc' (λ x' → Path x' (a0 , b0)) i (gluel <>)) 〉
                                        transport (λ x' → Path x' (a0 , b0)) (ap i (gluel <>)) id ≃〈 {!β!} 〉 
                                        transport (λ x' → Path x' (a0 , b0)) id id ≃〈 id 〉 
                                        id ∎)

           case2-adjustment = ap [_] (pair≃ (gluel _) case2-adjustment-1)

           case2 : ∀ {z a b} (α' : a0 ≃ a) (β' : b0 ≃ b) → fst (v a) b ≃ [ inm z , pair×≃ α' β' ]
           case2 id id = case2-adjustment ∘ snd (v a0)   


           case3 : ∀ {a' b'} (α' : a0 ≃ a') (β' : b' ≃ b) → fst (v a') b ≃ [ inr b' , pair×≃ α' β' ]
           case3 id id = ap (λ x → fst x b)
                           (ConnectedFib.β m cA
                            (λ a' →
                               ConnectedMap.Extensions _ b0 (λ b' → Trunc (plus2 m n) (HFiber i (a' , b'))) [ inl a' , id ] ,
                               ConnectedMap.Extensions-level cB b0 (λ b' → Trunc (plus2 m n) (HFiber i (a' , b')) , Trunc-level) _)
                            ((λ b' → [ inr b' , id ]) , ap [_] (pair≃ (! (gluer <> ∘ gluel <>)) _)))


           agree12 : ∀ {a b} → (α' : a0 ≃ a) (β : b0 ≃ b) →
                   Path (transport (λ p → fst (v a) b ≃ [ p ]) (pair≃⁻ (gluel <>) id)
                                  (split×≃ (λ z → fst (v a) b ≃ [ inl a0 , z ])
                                           case1 
                                           (transport (λ w' → Path (i w') (a , b)) (! (gluel <>)) (pair×≃ α' β))))
                        (split×≃ (λ z → fst (v a) b ≃ [ inm _ , z ]) case2 (pair×≃ α' β))
           agree12 id id = transport (λ p → fst (v a0) b0 ≃ [ p ]) (pair≃⁻ (gluel <>) id)
                                     (split×≃ (λ z → fst (v a0) b0 ≃ [ inl a0 , z ])
                                              case1
                                              (transport (λ w' → Path (i w') (a0 , b0)) (! (gluel <>)) id)) ≃〈 ap (transport (λ p → fst (v a0) b0 ≃ [ p ]) (pair≃⁻ (gluel <>) id)) (! (apd (split×≃ (λ z → fst (v a0) b0 ≃ [ inl a0 , z ]) case1) (! case2-adjustment-0))) 〉
                           transport (λ p → fst (v a0) b0 ≃ [ p ]) (pair≃⁻ (gluel <>) id)
                                     (transport (λ z → fst (v a0) b0 ≃ [ inl a0 , z ]) (! case2-adjustment-0)
                                       (split×≃ (λ z → fst (v a0) b0 ≃ [ inl a0 , z ])
                                                case1
                                                id)) ≃〈 id 〉 
                           transport (λ p → fst (v a0) b0 ≃ [ p ]) (pair≃⁻ (gluel <>) id)
                                     (transport (λ z → fst (v a0) b0 ≃ [ inl a0 , z ]) (! case2-adjustment-0)
                                       (snd (v a0))) ≃〈 {!!} 〉 
                           ap [_] (pair≃⁻ (gluel <>) id) ∘
                                     (transport (λ z → fst (v a0) b0 ≃ [ inl a0 , z ]) (! case2-adjustment-0)
                                       (snd (v a0))) ≃〈 {!!} 〉 
                           ap [_] (pair≃⁻ (gluel <>) id) ∘
                            ap (\ z -> [ inl a0 , z ]) (! case2-adjustment-0) ∘ 
                            (snd (v a0)) ≃〈 {!!} 〉 
                           (ap [_] (pair≃⁻ (gluel <>) id) ∘
                             ap (\ z -> [ inl a0 , z ]) (! case2-adjustment-0)) ∘ 
                            (snd (v a0)) ≃〈 ap (λ x → x ∘ snd (v a0)) STS 〉 
                           case2-adjustment ∘ snd (v a0) ∎  where
                   STS : (ap [_] (pair≃⁻ (gluel <>) id) ∘ ap (\ z -> [ inl a0 , z ]) (! case2-adjustment-0))
                       ≃ case2-adjustment
                   STS = ap [_] (pair≃⁻ (gluel <>) id) ∘ ap (λ z → [ inl a0 , z ]) (! case2-adjustment-0) ≃〈 {!!} 〉
                         ap [_] (pair≃⁻ (gluel <>) id) ∘ ap [_] (ap (λ z → ( inl a0 , z )) (! case2-adjustment-0)) ≃〈 {!!} 〉
                         ap [_] (pair≃⁻ (gluel <>) id ∘  (ap (λ z → ( inl a0 , z )) (! case2-adjustment-0))) ≃〈 ap {M = (pair≃⁻ (gluel <>) id ∘  (ap (λ z → ( inl a0 , z )) (! case2-adjustment-0)))}(ap [_]) STS2 〉
                         (case2-adjustment ∎) where
                     STS2 : (pair≃⁻{B = λ v' → Path (i v') (a0 , b0)} (gluel <>) id ∘  (ap (λ z → ( inl a0 , z )) (! case2-adjustment-0))) 
                          ≃ (pair≃ (gluel _) case2-adjustment-1)
                     STS2 = pair≃⁻ (gluel <>) id ∘ ap (λ z → inl a0 , z) (! case2-adjustment-0) ≃〈 {!!} 〉
                            pair≃⁻ (gluel <>) id ∘ pair≃⁻{B = λ v' → Path (i v') (a0 , b0)} id (! case2-adjustment-0) ≃〈 {!!} 〉
                            pair≃ (gluel _) case2-adjustment-1 ∎

           {-
           wrap1 : (α : Path a a) → Path{(HFiber i (a , b0))}(inl a , id) (inl a , pair×≃ α id)
           wrap1 α = pair≃ (ap inl α) (transport (λ x → Path (i x) (a , b0)) (ap inl α) id ≃〈 ! (ap≃ (transport-ap-assoc' (λ x → Path (i x) (a , b0)) inl α)) 〉
                                       transport (λ a' → Path (i (inl a')) (a , b0)) α id ≃〈 id 〉
                                       transport (λ a' → Path (a' , b0) (a , b0)) α id ≃〈 transport-Path-pre' (λ a' → a' , b0) α id 〉
                                       id ∘ ! (ap (λ a' → a' , b0) α) ≃〈 {!!} 〉
                                       pair×≃ α id ∎)
           -}

      -}
-}
