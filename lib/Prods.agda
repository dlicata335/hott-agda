
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Paths
open Paths

module lib.Prods where

  record Unit : Set where
    constructor <> 
  
  record Σe (A : Set) (B : A -> Set) : Set where
     constructor _,_
     field
       fst : A
       snd : B fst
  open Σe public

  Σ : {A : Set} -> (B : A -> Set) -> Set
  Σ {A} B = Σe A B

  infixr 0 _,_
  
  _×_ : Set -> Set -> Set
  a × b = Σ (\ (_ : a) -> b)

  infixr 10 _×_

  syntax Σe A (\ x  -> B) = Σ[ x ∶ A ] B

  fst≃ : {A : Set} {B : A -> Set} {p q : Σ[ x ∶ A ] B x} -> p ≃ q -> (fst p) ≃ (fst q)
  fst≃ Refl = Refl
  
  snd≃ : {A : Set} {B : A -> Set} {p q : Σ B} -> (c : p ≃ q) -> (subst B (fst≃ c) (snd p)) ≃ (snd q)
  snd≃ {A}{B} Refl = Refl

  pair≃ : {A : Set} {B : A -> Set} {p q : Σ B} -> (α : (fst p) ≃ (fst q)) -> (subst B α (snd p)) ≃ (snd q) -> p ≃ q
  pair≃ {p = x , y} {q = .x , .y} Refl Refl = Refl

  Σ≃η : {A : Set} {B : A -> Set} {p q : Σ B} -> (α : p ≃ q) -> (pair≃ (fst≃ α) (snd≃ α)) ≃ α
  Σ≃η {p = x , y} {q = .x , .y} Refl = Refl

  Σ≃β1 : {A : Set} {B : A -> Set} {p q : Σ B} 
       (α : Id (fst p) (fst q)) 
       (β : Id (subst B α (snd p)) (snd q))
       -> Id (fst≃{B = B} (pair≃ α β)) α
  Σ≃β1 {p = x , y} {q = .x , .y} Refl Refl = Refl

  Σ≃β2 : {A : Set} {B : A -> Set} {p q : Σ B} 
         (α : (fst p) ≃ (fst q))
         (β : (subst B α (snd p)) ≃ (snd q))
      -> (snd≃{B = B} (pair≃ α β)) ≃ (trans (resp (λ x → subst B x (snd p)) (Σ≃β1 {B = B} α β)) β)
  Σ≃β2 {p = x , y} {q = .x , .y} Refl Refl = Refl
 
  -- done out with J
  private
   module ProdsOfficial where
    fstPath : {A : Set} {B : A -> Set} {p q : Σ[ x ∶ A ] B x} -> Id p q -> Id (fst p) (fst q)
    fstPath = resp fst
  
    sndPath : {A : Set} {B : A -> Set} {p q : Σ B} -> (c : Id p q) -> Id (subst B (fstPath c) (snd p)) (snd q)
    sndPath {A}{B} c = jay (λ p q c → Id (subst B (fstPath c) (snd p)) (snd q)) c (\ _ -> Refl)
  
    pairPath : {A : Set} {B : A -> Set} {p q : Σ B} -> (α : Id (fst p) (fst q)) -> Id (subst B α (snd p)) (snd q) -> Id p q
--    pairPath {p = (px , py)} {q = (.px , .py)} Refl Refl = Refl -- FIXME do with J
    pairPath {A}{B} {px , py}{qx , qy} α β = (jay (\ px' qx' α' -> 
                                                   (py' : _) (qy' : _) -> Id (subst B α' py') qy'
                                                   -> Id{Σ B} (px' , py') (qx' , qy')) 
                                                   α
                                                   (λ x py' qy' → resp (λ y → x , y))) py qy β 


    pairPathη : {A : Set} {B : A -> Set} {p q : Σ B} -> (α : Id p q) -> Id (pairPath (fstPath α) (sndPath α)) α
    pairPathη {A}{B} α = jay (λ p' q' α' → Id (pairPath (fstPath α') (sndPath α')) α') α lemma where
      lemma : (p : Σ B) -> Id{Id p p } (pairPath Refl Refl) Refl
      lemma (_ , _) = Refl

    pairPathβ1 : {A : Set} {B : A -> Set} {p q : Σ B} -> (α : Id (fst p) (fst q)) (β : Id (subst B α (snd p)) (snd q))
               -> Id (fstPath{A}{B}{p}{q} (pairPath α β)) α
    pairPathβ1 {A}{B} {px , py}{qx , qy} α β = jay (λ px' qx' α' → 
                                                   (py' : _) (qy' : _) (β' : Id (subst B α' py') qy') 
                                                   -> Id (fstPath{A}{B}{px' , py'}{qx' , qy'} (pairPath α' β')) α') 
                                               α 
                                               (λ x py' qy' β' → 
                                                jay (λ py0 qy0 β0 → Id (resp (fst{A}{B}) (resp (_,_ x) β0)) Refl)
                                                    β' (λ _ → Refl)) 
                                               py qy β

    -- FIXME: account for the adjustment
    pairPathβ2 : {A : Set} {B : A -> Set} {p q : Σ B} -> (α : Id (fst p) (fst q)) (β : Id (subst B α (snd p)) (snd q))
               -> Id (sndPath{A}{B}{p}{q} (pairPath α β)) (trans (resp (λ x → subst B x (snd p)) (pairPathβ1 {A} {B} {p} {q} α β)) β)
    pairPathβ2 {A}{B} {px , py}{qx , qy} α β = jay
                                                 (λ px' qx' α' →
                                                    (py' : _) (qy' : _) (β' : Id (subst B α' py') qy') →
                                                    Id (sndPath {A} {B} {px' , py'} {qx' , qy'} (pairPath α' β'))
                                                    (trans
                                                     (resp (λ x → subst B x py')
                                                      (pairPathβ1 {A} {B} {px' , py'} {qx' , qy'} α' β'))
                                                     β'))
                                                 α (λ x py' qy' β' → jay
                                                                       (λ py0 qy0 β0 →
                                                                          Id
                                                                          (jay{_} (λ p q c → Id (subst B (resp (fst{A}{B}) c) (snd{A}{B} p)) (snd{A}{B} q)) {_}{_}
                                                                           (resp (_,_ x) β0) (λ _ → Refl))
                                                                          (trans
                                                                           (resp (λ x' → subst B x' py0)
                                                                            (jay (λ py1 qy1 β1 → Id (resp (fst{A}{B}) (resp (_,_ x) β1)) Refl) β0
                                                                             (λ _ → Refl)))
                                                                           β0))
                                                                       β' (λ _ → Refl)) py qy β
