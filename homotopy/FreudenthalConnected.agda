-- Peter Lumsdaine and Dan Licata

{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Suspension
open Truncation
open Int
open ConnectedProduct

module homotopy.FreudenthalConnected where

  -- FIXME move
  transport-HFiber-arg : {A B : Type} -> (f : A -> B) -> {b1 b2 : B}
                             (β : b1 ≃ b2)
                           -> transport (HFiber f) β ≃ \ p → (fst p , β ∘ snd p)
  transport-HFiber-arg f id = λ≃ \ p -> pair≃ id (! (∘-unit-l (snd p)))

  transport-Trunc-HFiber-arg : {A B : Type} {k : _} -> (f : A -> B) -> {b1 b2 : B}
                             (β : b1 ≃ b2)
                           -> transport (Trunc k o HFiber f) β ≃ Trunc-func (\ p → (fst p , β ∘ snd p))
  transport-Trunc-HFiber-arg f id = λ≃ (Trunc-elim _ (λ _ → path-preserves-level Trunc-level) (λ p → ap [_] (pair≃ id (! (∘-unit-l (snd p))))))
 
  !-inv-l-front : {A : Type} {M N P : A} (p : Path N P) (q : Path M N) → Path (! p ∘ p ∘ q) q
  !-inv-l-front id id = id
  
  move-transport-right≃ : ∀ {A : Type} {M M' : A} (B : A → Type)
                          (α : M ≃ M') {b : B M} {b' : B M'}
                       -> (transport B α b ≃ b')
                        ≃ (b ≃ transport B (! α) b')
  move-transport-right≃ B id = id

  move-transport-left-!≃ : ∀ {A : Type} {M M' : A} (B : A → Type)
                          (α : M ≃ M') {b : B M} {b' : B M'}
                       -> (b ≃ transport B (! α) b')
                        ≃ (transport B α b ≃ b')
  move-transport-left-!≃ B id = id

    {-
    transport-Path-right-∘ : ∀ {A} {a b c : A} (β : b ≃ c) (α : a ≃ b)
                           → transport-Path-right (β ∘ α) id ≃ 
                             ap (λ x → β ∘ x) (transport-Path-right α id) ∘
                             (transport-Path-right β (transport (Path a) α id) ∘
                              ap≃ (transport-∘ (Path a) β α))
    transport-Path-right-∘ id id = id

    ∘-Σ : ∀ {A} {B : A → Type} {p q r : Σ B}
        → (α1 : fst p ≃ fst q) (α2 : fst q ≃ fst r)
        → (β1 : transport B α1 (snd p) ≃ (snd q)) (β2 : transport B α2 (snd q) ≃ (snd r))
        → (pair≃{B = B} α2 β2) ∘ (pair≃ α1 β1) ≃ pair≃ (α2 ∘ α1) (β2 ∘ ap (transport B α2) β1 ∘ ap≃ (transport-∘ B α2 α1))
    ∘-Σ {p = (p1 , p2)} {q = (.p1 , .p2)} {r = (.p1 , .p2)} id id id id = id
    -}


  module Freudenthal
    (n' : TLevel)
    (-2<n' : -2 <tl n')
    (X : Type) (x0 : X) (nX : Connected (S n') X) where

    n : TLevel
    n = S n'

    2n = plus2 n' n'

    loop : X → Path {Susp X} No No
    loop x = ! (mer x0) ∘ mer x

    module CodesMer where
      private
        coh : ∀ {A} {a b : A} (α : a ≃ b) -> !-inv-r-front α α ≃ !-inv-l-back α α
        coh id = id

      Codes-mer' : (x1 x2 : X) -> Trunc 2n (HFiber mer ((mer x1) ∘ (! (mer x0)) ∘ (mer x2)))
      Codes-mer' = wedge-elim nX nX (λ x1 x2 → Trunc 2n (HFiber mer ((mer x1) ∘ (! (mer x0)) ∘ (mer x2))) , Trunc-level)
                                 (Inr id) {x0}{x0}
                                 (λ x2 → [ x2 , ! (!-inv-r-front (mer x0) (mer x2)) ])
                                 (λ x1 → [ x1 , ! (!-inv-l-back (mer x1) (mer x0)) ])
                                 (ap [_] (pair≃ id (ap ! (coh (mer x0)))))
  
      Codes-mer'-β1 : ∀ {x2} → Codes-mer' x0 x2 ≃ [ x2 , ! (!-inv-r-front (mer x0) (mer x2)) ]
      Codes-mer'-β1 = ap≃
                        (wedge-elim-βa nX nX
                         (λ x1 x2 →
                            Trunc 2n (HFiber mer (mer x1 ∘ ! (mer x0) ∘ mer x2)) , Trunc-level)
                         (Inr id) {x0} {x0}
                         (λ x2 → [ x2 , ! (!-inv-r-front (mer x0) (mer x2)) ])
                         (λ x1 → [ x1 , ! (!-inv-l-back (mer x1) (mer x0)) ])
                         (ap [_] (pair≃ id (ap ! (coh (mer x0))))))

      Codes-mer'-β2 : ∀ {x1} → Codes-mer' x1 x0 ≃ [ x1 , ! (!-inv-l-back (mer x1) (mer x0)) ]
      Codes-mer'-β2 = ap≃
                        (wedge-elim-βb nX nX
                         (λ x1 x2 →
                            Trunc 2n (HFiber mer (mer x1 ∘ ! (mer x0) ∘ mer x2)) , Trunc-level)
                         (Inr id) {x0} {x0}
                         (λ x2 → [ x2 , ! (!-inv-r-front (mer x0) (mer x2)) ])
                         (λ x1 → [ x1 , ! (!-inv-l-back (mer x1) (mer x0)) ])
                         (ap [_] (pair≃ id (ap ! (coh (mer x0))))))
  
      Codes-mer'' : (x1 : X) {p : Path No So}
                 → (x2 : X) (q : Id (mer x1 ∘ ! (mer x0) ∘ mer x2) p)
                 → Trunc 2n (HFiber mer p)
      Codes-mer'' x1 x2 q = transport (Trunc 2n o HFiber mer) q (Codes-mer' x1 x2)
      
      Codes-mer : (x1 : X) (p : Path No So)
                 → Trunc 2n (HFiber loop (! (mer x1) ∘ p)) -> Trunc 2n (HFiber mer p)
      Codes-mer x1 p = Trunc-rec Trunc-level (λ {(x2 , q) → Codes-mer'' x1 x2 (move-left-! (loop x2) (mer x1) p q)})  
  
      Codes-mer-back0 : ∀ {p} → Trunc 2n (HFiber mer p) → Trunc 2n (HFiber loop (! (mer x0) ∘ p))
      Codes-mer-back0 = Trunc-func λ {(x2 , q) → x2 , ap (λ x → ! (mer x0) ∘ x) q}
  
      Codes-mer-is-equiv0 : (p : Path No So) → IsEquiv (Codes-mer x0 p)
      Codes-mer-is-equiv0 p = 
        snd (improve (hequiv (Codes-mer x0 p) 
            Codes-mer-back0
            (Trunc-elim _ (λ _ → path-preserves-level Trunc-level)
              (λ {(x2 , q) → back (Codes-mer x0 p [ x2 , q ]) ≃〈 id 〉
                             back (Codes-mer'' x0 x2 (move-left-! (loop x2) (mer x0) p q)) ≃〈 id 〉
                             back (transport (Trunc 2n o HFiber mer) (move-left-! (loop x2) (mer x0) p q) (Codes-mer' x0 x2)) ≃〈 ap (λ x → back (transport (Trunc 2n o HFiber mer) (move-left-! (loop x2) (mer x0) p q) x)) Codes-mer'-β1 〉
                             back (transport (Trunc 2n o HFiber mer) (move-left-! (loop x2) (mer x0) p q)
                                   [ x2 , ! (!-inv-r-front (mer x0) (mer x2)) ]) ≃〈 ap back (transport-Trunc' (HFiber mer) (move-left-! (loop x2) (mer x0) p q) [ x2 , ! (!-inv-r-front (mer x0) (mer x2)) ]) 〉
                             back [ (transport (HFiber mer) 
                                               (move-left-! (! (mer x0) ∘ mer x2) (mer x0) p q))
                                    (x2 , ! (!-inv-r-front (mer x0) (mer x2))) ] ≃〈 ap (back o [_]) (ap≃ (transport-HFiber-arg mer (move-left-! (! (mer x0) ∘ mer x2) (mer x0) p q))) 〉 
                             back [ (x2 , (move-left-! (! (mer x0) ∘ mer x2) (mer x0) p q) ∘ ! (!-inv-r-front (mer x0) (mer x2))) ] ≃〈 id 〉 
                             [ x2 , ap (λ x → ! (mer x0) ∘ x) ((move-left-! (! (mer x0) ∘ mer x2) (mer x0) p q) ∘ ! (!-inv-r-front (mer x0) (mer x2))) ] ≃〈 ap [_] (pair≃ id (coh1 (mer x2) p q)) 〉 
                             [ x2 , q ] ∎}))
            (Trunc-elim _ (λ _ → path-preserves-level Trunc-level)
              (λ {(x2 , q) → Codes-mer'' x0 x2 (move-left-! (loop x2) (mer x0) p (ap (λ x → ! (mer x0) ∘ x) q)) ≃〈 id 〉 
                             transport (Trunc 2n o HFiber mer) (move-left-! (loop x2) (mer x0) p (ap (λ x → ! (mer x0) ∘ x) q)) (Codes-mer' x0 x2) ≃〈 ap (transport (Trunc 2n o HFiber mer) (move-left-! (loop x2) (mer x0) p (ap (λ x → ! (mer x0) ∘ x) q))) Codes-mer'-β1 〉
                             transport (Trunc 2n o HFiber mer) (move-left-! (loop x2) (mer x0) p (ap (λ x → ! (mer x0) ∘ x) q)) [ x2 , ! (!-inv-r-front (mer x0) (mer x2)) ] ≃〈 ap≃ (transport-Trunc-HFiber-arg mer (move-left-! (loop x2) (mer x0) p (ap (λ x → ! (mer x0) ∘ x) q))) 〉
                             [ x2 , (move-left-! (loop x2) (mer x0) p (ap (λ x → ! (mer x0) ∘ x) q)) ∘ ! (!-inv-r-front (mer x0) (mer x2)) ] ≃〈 ap [_] (pair≃ id (coh2 {α1 = mer x0} (mer x2) p q)) 〉
                             [ x2 , q ] ∎}))))
       where back = Codes-mer-back0
  
             coh1 : ∀ {A} {a b c : A} {α1 : a ≃ b} (α2 : c ≃ b) (p : c ≃ b) (q : (! α1 ∘ α2) ≃ (! α1 ∘ p))
                  → Path (ap (_∘_ (! α1)) (move-left-! (! α1 ∘ α2) α1 p q ∘ ! (!-inv-r-front α1 α2))) q
             coh1 {α1 = id} id p q = (!-inv-l-front (∘-unit-l p) q ∘ ap (λ x → ! (∘-unit-l p) ∘ x) (ap-id (∘-unit-l p ∘ q))) ∘ ap-by-equals (λ x → ∘-unit-l x) (∘-unit-l p ∘ q)
      
             coh2 : ∀ {A} {a b c : A} {α1 : a ≃ b} (α2 : c ≃ b) (p : c ≃ b) (q : Id α2 p)
                  → (move-left-! (! α1 ∘ α2) α1 p (ap (λ x → ! α1 ∘ x) q)) ∘ ! (!-inv-r-front α1 α2) ≃ q
             coh2 {α1 = id} id p q = (ap-id q ∘ !-inv-r-front (∘-unit-l p) (ap (λ z → z) q)) ∘ ap (λ z → ∘-unit-l p ∘ z) (ap-by-equals (λ x → ∘-unit-l x) q)

      abstract
        Codes-mer-is-equiv : (x1 : X) (p : Path No So)
                            → IsEquiv (Codes-mer x1 p)
        Codes-mer-is-equiv = ConnectedFib.everywhere -1 {a0 = x0}
                                                     (lower-Connected (<=SCong (-1<= -2<n')) nX)
                                                     (λ x1 → ((p : Path No So) → IsEquiv (Codes-mer x1 p)) , Πlevel (λ _ → IsEquiv-HProp _))
                                                     Codes-mer-is-equiv0

        Codes-mer-is-equiv-β0 : Codes-mer-is-equiv x0 ≃ Codes-mer-is-equiv0
        Codes-mer-is-equiv-β0 = ConnectedFib.β -1 {a0 = x0}
                                               (lower-Connected (<=SCong (-1<= -2<n')) nX)
                                               (λ x1 → ((p : Path No So) → IsEquiv (Codes-mer x1 p)) , Πlevel (λ _ → IsEquiv-HProp _))
                                               Codes-mer-is-equiv0

    open CodesMer

    -- CodesFor x α is the Codes for paths to x which decode to α
    CodesFor : (x : Susp X) -> Path No x → Type
    CodesFor = Susp-elim _
                         (\ α → Trunc 2n (HFiber loop α))
                         (λ α → Trunc 2n (HFiber mer α))
                         (λ x1 → λ≃ (λ p → ua (Codes-mer x1 p , Codes-mer-is-equiv x1 p) ∘ 
                                           ap (λ p' → Trunc 2n (HFiber loop p')) (transport-Path-right (! (mer x1)) p) ∘
                                           ap≃ (transport-→-pre' (Path No) (mer x1) (λ α → Trunc 2n (HFiber loop α))))) 

    CodesForC : (Σ \ (x : Susp X) -> Path No x) → Type
    CodesForC p = CodesFor (fst p) (snd p)

    encode : {x : Susp X} → (α : Path No x) → CodesFor x α
    encode {x} α = -- this is really J written out with transport
                   coe
                   (ap CodesForC 
                       (pair≃ {B = Path No} α (transport-Path-right α id)))
                   [ x0 , !-inv-l (mer x0) ] -- includes bit from decode-encode

    -- FIXME
    Susp-elim-β-mer-fst : ∀ {C} {x : X} (B : Susp X → Type) {b1 : B No} {b2 : B So} (β : transport B (mer x) b1 ≃ b2)
                      {n' : B No → C} {s' : B So → C} (mer' : (x : X) → transport (\ x -> B x → C) (mer x) n' ≃ s') →
                        ap (\ (p : Σ B) → Susp-elim (\ x -> B x → C) n' s' mer' (fst p) (snd p)) (pair≃ (mer x) β)
                      ≃ ap≃ (mer' x) {b2}
                      ∘ ! (ap≃ (transport-→-pre' B (mer x) n'))
                      ∘ ap n' (coe (move-transport-right≃ B (mer x)) β)
    Susp-elim-β-mer-fst = {!!} where 


    -- if α = decode c then encode α = c
    encode-decode : {x : Susp X} → (α : Path No x) → (c : CodesFor x α) -> (encode α) ≃ c
    encode-decode id = Trunc-elim _ (λ _ → path-preserves-level Trunc-level) 
                                    (encode-decode' id) where
      -- WEIRD: by path induction, suffices to consider x = No, α = id
      -- but then need to re-generalize to arbitrary loop α?
      encode-decode' : (α : Path No No) → (c : HFiber loop α) → Id (encode α) [ c ]
      encode-decode' ._ (x , id) = STS where
        STS : (encode (! (mer x0) ∘ mer x)) ≃ [ x , id ]
        STS = (encode (! (mer x0) ∘ mer x)) ≃〈 id 〉 
              (coe (ap CodesForC (pair≃ (! (mer x0) ∘ mer x) (transport-Path-right (! (mer x0) ∘ mer x) id)))
                   [ x0 , !-inv-l (mer x0) ])   ≃〈 ap (λ x' → coe (ap CodesForC x') [ x0 , !-inv-l (mer x0) ]) (un∘ (! (mer x0)) (mer x)) 〉 
              (coe (ap CodesForC ((pair≃   (! (mer x0)) (transport-Path-right (! (mer x0)) (mer x))) 
                                  ∘ (pair≃ (mer x) (transport-Path-right (mer x) id))))
                   [ x0 , !-inv-l (mer x0) ])   ≃〈 ap (λ x' → coe x' [ x0 , !-inv-l (mer x0) ]) (ap-∘ CodesForC (pair≃ (! (mer x0)) (transport-Path-right (! (mer x0)) (mer x))) (pair≃ (mer x) (transport-Path-right (mer x) id))) 〉 
              (coe (ap CodesForC ((pair≃   (! (mer x0)) (transport-Path-right (! (mer x0)) (mer x))))
                    ∘ (ap CodesForC (pair≃ (mer x) (transport-Path-right (mer x) id))))
                                     [ x0 , !-inv-l (mer x0) ]) ≃〈 ap≃ (transport-∘ (λ x' → x') (ap CodesForC (pair≃ (! (mer x0)) (transport-Path-right (! (mer x0)) (mer x)))) (ap CodesForC (pair≃ (mer x) (transport-Path-right (mer x) id)))) 〉 
              (coe (ap CodesForC ((pair≃   (! (mer x0)) (transport-Path-right (! (mer x0)) (mer x)))))
                   (coe (ap CodesForC (pair≃ (mer x) (transport-Path-right (mer x) id)))
                        [ x0 , !-inv-l (mer x0) ])) ≃〈 ap (coe (ap CodesForC (pair≃ (! (mer x0)) (transport-Path-right (! (mer x0)) (mer x))))) fact1 〉 
              (coe (ap CodesForC ((pair≃   (! (mer x0)) (transport-Path-right (! (mer x0)) (mer x)))))
                   [ x , id ] ) ≃〈 fact2 〉 
              [ x , id ] ∎ where
         un∘ : ∀ {x y z} (α2 : Path{Susp X} y z) (α1 : Path{Susp X} x y)
               ->  (pair≃ {B = Path x} (α2 ∘ α1) (transport-Path-right (α2 ∘ α1) id))
                 ≃   pair≃ α2 (transport-Path-right α2 α1) 
                   ∘ pair≃ α1 (transport-Path-right α1 id)
         un∘ id id = id

         coh0 : ∀ {A} {a b c d e : A} (p1 : d ≃ e) (p2 : c ≃ d) (p3 : b ≃ c) (p4 : a ≃ c) 
                      → (p1 ∘ p2 ∘ p3) ∘ (! p3) ∘ p4 ≃ p1 ∘ p2 ∘ p4
         coh0 id id id id = id

         fact1 : (coe (ap CodesForC (pair≃ (mer x) (transport-Path-right (mer x) id))) [ x0 , !-inv-l (mer x0) ]) ≃ [ x , id ]
         fact1 = (coe (ap CodesForC (pair≃ (mer x) (transport-Path-right (mer x) id))) [ x0 , !-inv-l (mer x0) ]) ≃〈 ap (λ x' → coe x' [ x0 , !-inv-l (mer x0) ]) (Susp-elim-β-mer-fst (Path No) (transport-Path-right (mer x) id) (λ x1 → λ≃ (λ p → ua (Codes-mer x1 p , Codes-mer-is-equiv x1 p) ∘ ap (λ p' → Trunc 2n (HFiber loop p')) (transport-Path-right (! (mer x1)) p) ∘ ap≃ (transport-→-pre' (Path No) (mer x1) (λ α → Trunc 2n (HFiber loop α)))))) 〉 
                 coe
                   (ap≃
                      (λ≃ (λ p → ua (Codes-mer x p , Codes-mer-is-equiv x p) ∘ ap (λ p' → Trunc 2n (HFiber loop p')) (transport-Path-right (! (mer x)) p)
                               ∘ ap≃ (transport-→-pre' (Path No) (mer x) (λ α → Trunc 2n (HFiber loop α)))))
                      {mer x}
                    ∘ ! (ap≃ (transport-→-pre' (Path No) (mer x) (λ α → Trunc 2n (HFiber loop α))){mer x})
                    ∘ ap (λ α → Trunc 2n (HFiber loop α)) (coe (move-transport-right≃ (Path No) (mer x)) (transport-Path-right (mer x) id)))
                   [ x0 , !-inv-l (mer x0) ] ≃〈 ap (λ z → coe (z ∘ ! (ap≃ (transport-→-pre' (Path No) (mer x) (λ α → Trunc 2n (HFiber loop α))) {mer x}) ∘ ap (λ α → Trunc 2n (HFiber loop α)) (coe (move-transport-right≃ (Path No) (mer x)) (transport-Path-right (mer x) id))) [ x0 , !-inv-l (mer x0) ]) (Π≃β (λ p → ua (Codes-mer x p , Codes-mer-is-equiv x p) ∘ ap (λ p' → Trunc 2n (HFiber loop p')) (transport-Path-right (! (mer x)) p) ∘ ap≃ (transport-→-pre' (Path No) (mer x) (λ α → Trunc 2n (HFiber loop α))))) 〉 
                 coe(
                    (  ua (Codes-mer x (mer x) , Codes-mer-is-equiv x (mer x))
                    ∘ ap (λ p' → Trunc 2n (HFiber loop p')) (transport-Path-right (! (mer x)) (mer x))
                    ∘ ap≃ (transport-→-pre' (Path No) (mer x) (λ α → Trunc 2n (HFiber loop α))) {mer x})
                    ∘ ! (ap≃ (transport-→-pre' (Path No) (mer x) (λ α → Trunc 2n (HFiber loop α))){mer x})
                    ∘ ap (λ α → Trunc 2n (HFiber loop α)) (coe (move-transport-right≃ (Path No) (mer x)) (transport-Path-right (mer x) id)))
                   [ x0 , !-inv-l (mer x0) ] ≃〈 ap (λ x' → coe x' [ x0 , !-inv-l (mer x0) ]) (coh0 (ua (Codes-mer x (mer x) , Codes-mer-is-equiv x (mer x))) (ap (λ p' → Trunc 2n (HFiber loop p')) (transport-Path-right (! (mer x)) (mer x))) (ap≃ (transport-→-pre' (Path No) (mer x) (λ α → Trunc 2n (HFiber loop α))) {mer x}) (ap (λ α → Trunc 2n (HFiber loop α)) (coe (move-transport-right≃ (Path No) (mer x)) (transport-Path-right (mer x) id)))) 〉 
                 coe(
                      ua (Codes-mer x (mer x) , Codes-mer-is-equiv x (mer x))
                    ∘ ap (λ p' → Trunc 2n (HFiber loop p')) (transport-Path-right (! (mer x)) (mer x))
                    ∘ ap (λ α → Trunc 2n (HFiber loop α)) (coe (move-transport-right≃ (Path No) (mer x)) (transport-Path-right (mer x) id)))
                   [ x0 , !-inv-l (mer x0) ] ≃〈 ap (λ z → coe (ua (Codes-mer x (mer x) , Codes-mer-is-equiv x (mer x)) ∘ z) [ x0 , !-inv-l (mer x0) ]) (! (ap-∘ (λ p' → Trunc 2n (HFiber loop p')) (transport-Path-right (! (mer x)) (mer x)) (coe (move-transport-right≃ (Path No) (mer x)) (transport-Path-right (mer x) id)))) 〉 
                 coe(
                      ua (Codes-mer x (mer x) , Codes-mer-is-equiv x (mer x))
                    ∘ ap (λ p' → Trunc 2n (HFiber loop p')) ((transport-Path-right (! (mer x)) (mer x))
                                                             ∘ (coe (move-transport-right≃ (Path No) (mer x)) (transport-Path-right (mer x) id))))
                   [ x0 , !-inv-l (mer x0) ] ≃〈 ap (λ z → coe (ua (Codes-mer x (mer x) , Codes-mer-is-equiv x (mer x)) ∘ ap (λ p' → Trunc 2n (HFiber loop p')) z) [ x0 , !-inv-l (mer x0) ]) (coh2 (mer x)) 〉 
                 coe(
                      ua (Codes-mer x (mer x) , Codes-mer-is-equiv x (mer x))
                    ∘ ap (λ p' → Trunc 2n (HFiber loop p')) (! (!-inv-l (mer x))))
                   [ x0 , !-inv-l (mer x0) ] ≃〈 ap≃ (transport-∘ (λ x' → x') (ua (Codes-mer x (mer x) , Codes-mer-is-equiv x (mer x))) (ap (λ p' → Trunc 2n (HFiber loop p')) (! (!-inv-l (mer x))))) 〉 
                 coe(ua (Codes-mer x (mer x) , Codes-mer-is-equiv x (mer x)))
                    (coe (ap (λ p' → Trunc 2n (HFiber loop p')) (! (!-inv-l (mer x))))
                         [ x0 , !-inv-l (mer x0) ]) ≃〈 ap (coe (ua (Codes-mer x (mer x) , Codes-mer-is-equiv x (mer x)))) (! (ap≃ (transport-ap-assoc (λ p' → Trunc 2n (HFiber loop p')) (! (!-inv-l (mer x)))))) 〉 
                 coe(ua (Codes-mer x (mer x) , Codes-mer-is-equiv x (mer x)))
                    (transport (λ p' → Trunc 2n (HFiber loop p'))
                               (! (!-inv-l (mer x)))
                               [ x0 , !-inv-l (mer x0) ]) ≃〈 ap (coe (ua (Codes-mer x (mer x) , Codes-mer-is-equiv x (mer x)))) (ap≃ (transport-Trunc-HFiber-arg loop (! (!-inv-l (mer x))))) 〉 
                 coe(ua (Codes-mer x (mer x) , Codes-mer-is-equiv x (mer x)))
                    [ x0 , (! (!-inv-l (mer x))) ∘ !-inv-l (mer x0) ] ≃〈 ap≃ (type≃β (Codes-mer x (mer x) , Codes-mer-is-equiv x (mer x))) 〉 
                 (Codes-mer x (mer x)) [ x0 , (! (!-inv-l (mer x))) ∘ !-inv-l (mer x0) ] ≃〈 id 〉 
                 Codes-mer'' x x0 (move-left-! (loop x0) (mer x) (mer x) ((! (!-inv-l (mer x))) ∘ !-inv-l (mer x0))) ≃〈 ap (Codes-mer'' x x0) (coh3 (mer x0) (mer x)) 〉 
                 Codes-mer'' x x0 (!-inv-l-back (mer x) (mer x0)) ≃〈 id 〉 
                 transport (Trunc 2n o HFiber mer) (!-inv-l-back (mer x) (mer x0)) (Codes-mer' x x0) ≃〈 ap (transport (Trunc 2n o HFiber mer) (!-inv-l-back (mer x) (mer x0))) Codes-mer'-β2 〉 
                 transport (Trunc 2n o HFiber mer) (!-inv-l-back (mer x) (mer x0)) [ x , ! (!-inv-l-back (mer x) (mer x0)) ] ≃〈 ap≃ (transport-Trunc-HFiber-arg mer (!-inv-l-back (mer x) (mer x0))) 〉 
                 [ x , (!-inv-l-back (mer x) (mer x0)) ∘ ! (!-inv-l-back (mer x) (mer x0)) ] ≃〈 ap (λ y → [ x , y ]) (!-inv-r (!-inv-l-back (mer x) (mer x0))) 〉 
                 [ x , id ] ∎ where
               coh2 :  ∀ {A} {a b : A} (α : a ≃ b) →
                         (transport-Path-right (! α) α)
                       ∘ (coe (move-transport-right≃ (Path a) α) (transport-Path-right α id))
                    ≃ ! (!-inv-l α)
               coh2 id = id

               coh3 : ∀ {A} {a b c : A} (α : a ≃ b) (β : a ≃ c) →
                      (move-left-! (! α ∘ α) β β ((! (!-inv-l β)) ∘ !-inv-l α))
                    ≃ !-inv-l-back β α
               coh3 id id = id

         fact2 : (coe (ap CodesForC ((pair≃ (! (mer x0)) (transport-Path-right (! (mer x0)) (mer x))))) [ x , id ] ) ≃ [ x , id ]
         fact2 = coe (ap CodesForC (pair≃ (! (mer x0)) (transport-Path-right (! (mer x0)) (mer x)))) [ x , id ] ≃〈 ap (λ z → coe (ap CodesForC z) [ x , id ]) (coh2 (mer x0) (transport-Path-right (! (mer x0)) (mer x))) 〉 coe (ap CodesForC (! (pair≃ (mer x0) (coe (move-transport-left-!≃ (Path No) (mer x0)) (! (transport-Path-right (! (mer x0)) (mer x))))))) [ x , id ] ≃〈 ap (λ z → coe z [ x , id ]) (ap-! CodesForC (pair≃ (mer x0) (coe (move-transport-left-!≃ (Path No) (mer x0))
                                                                                                                                                                               (! (transport-Path-right (! (mer x0)) (mer x)))))) 〉
                 coe (! (ap CodesForC (pair≃ (mer x0) (coe (move-transport-left-!≃ (Path No) (mer x0)) (! (transport-Path-right (! (mer x0)) (mer x))))))) [ x , id ] ≃〈 ap (λ z → coe (! z) [ x , id ]) (Susp-elim-β-mer-fst (Path No) (coe (move-transport-left-!≃ (Path No) (mer x0)) (! (transport-Path-right (! (mer x0)) (mer x)))) (λ x1 → λ≃ (λ p → ua (Codes-mer x1 p , Codes-mer-is-equiv x1 p) ∘ ap (λ p' → Trunc 2n (HFiber loop p')) (transport-Path-right (! (mer x1)) p) ∘ ap≃ (transport-→-pre' (Path No) (mer x1) (λ α → Trunc 2n (HFiber loop α)))))) 〉
                 coe
                   (! (ap≃ (λ≃ (λ p → ua (Codes-mer x0 p , Codes-mer-is-equiv x0 p) ∘ ap (λ p' → Trunc 2n (HFiber loop p')) (transport-Path-right (! (mer x0)) p)
                               ∘ ap≃ (transport-→-pre' (Path No) (mer x0) (λ α → Trunc 2n (HFiber loop α))))){mer x}
                       ∘ ! (ap≃ (transport-→-pre' (Path No) (mer x0) (λ α → Trunc 2n (HFiber loop α))))
                       ∘ ap (λ α → Trunc 2n (HFiber loop α)) 
                            (coe (move-transport-right≃ (Path No) (mer x0)) (coe (move-transport-left-!≃ (Path No) (mer x0)) (! (transport-Path-right (! (mer x0)) (mer x)))))))
                   [ x , id ] ≃〈 ap (λ z → coe (! (z ∘ ! (ap≃ (transport-→-pre' (Path No) (mer x0) (λ α → Trunc 2n (HFiber loop α)))) ∘ ap (λ α → Trunc 2n (HFiber loop α)) (coe (move-transport-right≃ (Path No) (mer x0)) (coe (move-transport-left-!≃ (Path No) (mer x0)) (! (transport-Path-right (! (mer x0)) (mer x))))))) [ x , id ]) (Π≃β (λ p → ua (Codes-mer x0 p , Codes-mer-is-equiv x0 p) ∘ ap (λ p' → Trunc 2n (HFiber loop p')) (transport-Path-right (! (mer x0)) p) ∘ ap≃ (transport-→-pre' (Path No) (mer x0) (λ α → Trunc 2n (HFiber loop α))))) 〉
                  coe
                   (! ((  ua (Codes-mer x0 (mer x) , Codes-mer-is-equiv x0 (mer x))
                        ∘ ap (λ p' → Trunc 2n (HFiber loop p')) (transport-Path-right (! (mer x0)) (mer x))
                        ∘ ap≃ (transport-→-pre' (Path No) (mer x0) (λ α → Trunc 2n (HFiber loop α))){mer x})
                       ∘ ! (ap≃ (transport-→-pre' (Path No) (mer x0) (λ α → Trunc 2n (HFiber loop α))){mer x})
                       ∘ ap (λ α → Trunc 2n (HFiber loop α)) (coe (move-transport-right≃ (Path No) (mer x0)) (coe (move-transport-left-!≃ (Path No) (mer x0)) (! (transport-Path-right (! (mer x0)) (mer x)))))))
                   [ x , id ] ≃〈 ap (λ z → coe (! z) [ x , id ]) (coh0 (ua (Codes-mer x0 (mer x) , Codes-mer-is-equiv x0 (mer x))) (ap (λ p' → Trunc 2n (HFiber loop p')) (transport-Path-right (! (mer x0)) (mer x))) (ap≃ (transport-→-pre' (Path No) (mer x0) (λ α → Trunc 2n (HFiber loop α)))) (ap (λ α → Trunc 2n (HFiber loop α)) (coe (move-transport-right≃ (Path No) (mer x0)) (coe (move-transport-left-!≃ (Path No) (mer x0)) (! (transport-Path-right (! (mer x0)) (mer x))))))) 〉
                  coe
                   (! (ua (Codes-mer x0 (mer x) , Codes-mer-is-equiv x0 (mer x))
                       ∘ ap (λ p' → Trunc 2n (HFiber loop p')) (transport-Path-right (! (mer x0)) (mer x))
                       ∘ ap (λ α → Trunc 2n (HFiber loop α)) 
                            (coe (move-transport-right≃ (Path No) (mer x0)) (coe (move-transport-left-!≃ (Path No) (mer x0)) (! (transport-Path-right (! (mer x0)) (mer x)))))))
                   [ x , id ] ≃〈 ap (λ z → coe (! (ua (Codes-mer x0 (mer x) , Codes-mer-is-equiv x0 (mer x)) ∘ z)) [ x , id ]) (! (ap-∘ (λ p' → Trunc 2n (HFiber loop p')) (transport-Path-right (! (mer x0)) (mer x)) (coe (move-transport-right≃ (Path No) (mer x0)) (coe (move-transport-left-!≃ (Path No) (mer x0)) (! (transport-Path-right (! (mer x0)) (mer x))))))) 〉
                  coe
                   (! (ua (Codes-mer x0 (mer x) , Codes-mer-is-equiv x0 (mer x))
                       ∘ ap (λ α → Trunc 2n (HFiber loop α)) 
                            ((transport-Path-right (! (mer x0)) (mer x)) ∘ 
                             (coe (move-transport-right≃ (Path No) (mer x0)) (coe (move-transport-left-!≃ (Path No) (mer x0)) (! (transport-Path-right (! (mer x0)) (mer x))))))))
                   [ x , id ] ≃〈 ap (λ z → coe (! (ua (Codes-mer x0 (mer x) , Codes-mer-is-equiv x0 (mer x)) ∘ ap (λ α → Trunc 2n (HFiber loop α)) z)) [ x , id ]) (coh1 (mer x0) (mer x)) 〉
                  coe (! (ua (Codes-mer x0 (mer x) , Codes-mer-is-equiv x0 (mer x)))) [ x , id ] ≃〈 ap≃ (type≃β! (Codes-mer x0 (mer x) , Codes-mer-is-equiv x0 (mer x))) 〉
                  IsEquiv.g (Codes-mer-is-equiv x0 (mer x)) [ x , id ] ≃〈 ap (λ f → IsEquiv.g (f (mer x)) [ x , id ]) Codes-mer-is-equiv-β0 〉
                  Codes-mer-back0 {(mer x)} [ x , id ] ≃〈 id 〉
                  [ x , id ] ∎ where
               coh1 : ∀ {A} {a b : A} (α : a ≃ b) (β : a ≃ b) →
                      ((transport-Path-right (! α) β) ∘ 
                            (coe (move-transport-right≃ (Path a) α) (coe (move-transport-left-!≃ (Path a) α) (! (transport-Path-right (! α) β)))))
                      ≃ id
               coh1 id β = !-inv-r (transport-Path-right id β)

               coh2 : ∀ {A} {B : A → Type} {a1 a2 : A} {b1 : B a1} {b2 : B a2} (α : a2 ≃ a1) (β : transport B (! α) b1 ≃ b2)
                    -> (pair≃ (! α) β) ≃ ! (pair≃ α (coe (move-transport-left-!≃ B α) (! β)))
               coh2 id id = id
    
    thm : ConnectedMap.ConnectedMap 2n {X}{(Path {(Susp X)} No No)} loop
    thm α = ntype (encode α , encode-decode α)

  

