
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Paths
open S¹

module misc.CircleResp where

  module NonDep where
  
    step1 : {Γ : Set} {θ1 θ2 : Γ} 
            {C : Γ -> Set} {b' : (θ : Γ) -> C θ} {l' : (θ : Γ) -> (b' θ) ≃ (b' θ)}
            {δ : θ1 ≃ θ2} 
          -> respd (\ (e : Γ × S¹) -> S¹-rec (b' (fst e)) (l' (fst e)) (snd e)) 
                   (NDPair.nondep-pair≃{Γ}{S¹} δ (Refl {_} {base}))
          ≃ respd b' δ ∘ 
            -- next line is definitional in 2tt
            resp (λ x → subst C x (b' θ1)) (NDPair.×≃β1 δ Refl) ∘ app≃ (! (subst-resp' C fst (NDPair.nondep-pair≃ δ Refl)))
    step1 = {!!}
  
    step2 : {Γ : Set} {θ1 θ2 : Γ} 
            {C : Γ -> Set} {b' : (θ : Γ) -> C θ} {l' : (θ : Γ) -> (b' θ) ≃ (b' θ)}
            {δ : θ1 ≃ θ2} 
          -> respd (\ (e : Γ × S¹) -> S¹-rec (b' (fst e)) (l' (fst e)) (snd e)) 
                   (NDPair.nondep-pair≃{Γ}{S¹} δ loop)
           ≃ app≃2 (λ≃ l') δ ∘
             -- next line is definitional in 2tt
             resp (λ x → subst C x (b' θ1)) (NDPair.×≃β1 δ loop) ∘ app≃ (! (subst-resp' C fst (NDPair.nondep-pair≃ δ loop)))
    step2 = {!!}
            
    step3 : {Γ : Set} {θ1 θ2 : Γ} 
            {C : Γ -> Set} {b' : (θ : Γ) -> C θ} {l' : (θ : Γ) -> (b' θ) ≃ (b' θ)}
            {δ : θ1 ≃ θ2} {p1 p2 : S¹} {α : p1 ≃ p2} 
          -> respd (\ (e : Γ × S¹) -> S¹-rec (b' (fst e)) (l' (fst e)) (snd e)) 
                   (NDPair.nondep-pair≃{Γ}{S¹} δ (! α))
           ≃ {!!} ∘
               resp (subst (C o fst) (NDPair.nondep-pair≃ δ (! α)))
               (!
                (respd (λ (e : Γ × S¹) → S¹-rec (b' (fst e)) (l' (fst e)) (snd e))
                 (NDPair.nondep-pair≃ {Γ} {S¹} (! δ) α)))
    step3 = {!!}
  
    step4 : {Γ : Set} {θ1 θ2 : Γ} 
            {C : Γ -> Set} {b' : (θ : Γ) -> C θ} {l' : (θ : Γ) -> (b' θ) ≃ (b' θ)}
            {δ : θ1 ≃ θ2} {p1 p2 p3 : S¹} {α : p1 ≃ p2} {β : p2 ≃ p3}
          -> respd (\ (e : Γ × S¹) -> S¹-rec (b' (fst e)) (l' (fst e)) (snd e)) 
                   (NDPair.nondep-pair≃{Γ}{S¹} δ (β ∘ α))
           ≃ respd (λ (e : Γ × S¹) → S¹-rec (b' (fst e)) (l' (fst e)) (snd e))
               (NDPair.nondep-pair≃ Refl β) ∘
               resp (subst (λ z → C (fst z)) (resp2 _,_ Refl β))
               (respd (λ (e : Γ × S¹) → S¹-rec (b' (fst e)) (l' (fst e)) (snd e))
                (NDPair.nondep-pair≃ {Γ} {S¹} δ α))
               ∘ {!!}
    step4 = {!!}

  module Dep where
  
    step1 : {Γ : Set} {θ1 θ2 : Γ} 
            {C : Γ → S¹ -> Set} {b' : (θ : Γ) -> C θ base} {l' : (θ : Γ) -> subst (C θ) loop (b' θ) ≃ (b' θ)}
            {δ : θ1 ≃ θ2} 
          -> respd (\ (e : Γ × S¹) -> S¹-elim {C (fst e)} (b' (fst e)) (l' (fst e)) (snd e)) 
                   (NDPair.nondep-pair≃{Γ}{S¹} δ (Refl {_} {base}))
          ≃ respd b' δ ∘ {!!}
    step1 = {!!}
  
    step2 : {Γ : Set} {θ1 θ2 : Γ} 
            {C : Γ → S¹ -> Set} {b' : (θ : Γ) -> C θ base} {l' : (θ : Γ) -> subst (C θ) loop (b' θ) ≃ (b' θ)}
            {δ : θ1 ≃ θ2} 
          -> respd (\ (e : Γ × S¹) -> S¹-elim {C (fst e)} (b' (fst e)) (l' (fst e)) (snd e)) 
                   (NDPair.nondep-pair≃{Γ}{S¹} δ loop)
           ≃ app≃2 (λ≃ l') δ ∘ {!!}
    step2 = {!!}

    step3 : {Γ : Set} {θ1 θ2 : Γ} 
            {C : Γ → S¹ -> Set} {b' : (θ : Γ) -> C θ base} {l' : (θ : Γ) -> subst (C θ) loop (b' θ) ≃ (b' θ)}
            {δ : θ1 ≃ θ2} 
            {p1 p2 : S¹} {α : p1 ≃ p2} 
          -> respd (\ (e : Γ × S¹) -> S¹-elim {C (fst e)} (b' (fst e)) (l' (fst e)) (snd e)) 
                   (NDPair.nondep-pair≃{Γ}{S¹} δ (! α))
           ≃ {!!} ∘
               resp (subst (\ p -> C (fst p) (snd p)) (NDPair.nondep-pair≃ δ (! α)))
               (!
                (respd (λ (e : Γ × S¹) → S¹-elim {C (fst e)} (b' (fst e)) (l' (fst e)) (snd e))
                 (NDPair.nondep-pair≃ {Γ} {S¹} (! δ) α)))
    step3 = {!!}

    step4 : {Γ : Set} {θ1 θ2 : Γ} 
            {C : Γ → S¹ -> Set} {b' : (θ : Γ) -> C θ base} {l' : (θ : Γ) -> subst (C θ) loop (b' θ) ≃ (b' θ)}
            {δ : θ1 ≃ θ2} 
            {p1 p2 p3 : S¹} {α : p1 ≃ p2} {β : p2 ≃ p3}
          -> respd (\ (e : Γ × S¹) -> S¹-elim {C (fst e)} (b' (fst e)) (l' (fst e)) (snd e)) 
                   (NDPair.nondep-pair≃{Γ}{S¹} δ (β ∘ α))
           ≃ respd (λ (e : Γ × S¹) → S¹-elim {C (fst e)} (b' (fst e)) (l' (fst e)) (snd e))
               (NDPair.nondep-pair≃ Refl β) ∘
               resp (subst (λ z → C (fst z) (snd z)) (resp2 _,_ Refl β))
               (respd (λ (e : Γ × S¹) → S¹-elim {C (fst e)}  (b' (fst e)) (l' (fst e)) (snd e))
                (NDPair.nondep-pair≃ {Γ} {S¹} δ α))
               ∘ {!!}
    step4 = {!!}

