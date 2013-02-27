
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Truncation
open Int
open import homotopy.HStructure
open LoopSpace

module homotopy.KG1 where


  -- reflection of G
  module K (G : Group) where
    open Group G

    private
      data KG1' : Type where
        base' : KG1'
      
    KG1 : Type
    KG1 = KG1'

    base : KG1 
    base = base'

    postulate 
      KG1-level  : NType (tl 1) KG1
      loop       : El -> Path base base
      loop-ident : loop ident  ≃ id
      loop-comp  : ∀ g1 g2 → loop (comp g1 g2) ≃ (loop g2) ∘ (loop g1)

    KG1-rec : ∀ {C} 
            -> (nC : NType (tl 1) C)
            -> (b' : C)
            -> (l' : GroupHom G (PathGroup (C , nC) b'))
            -> KG1 → C
    KG1-rec _ b' _ base' = b'

    KG1-elim : (C : KG1 → NTypes (tl 1))
            -> (b' : fst (C base))
            -> (loop' : (x : El) → transport (fst o C) (loop x) b' ≃ b')
            -> (preserves-ident : (x : El) → {!!} ≃ id {_} {b'})
            -> {!!}
            -> (x : KG1) → fst (C x)
    KG1-elim _ b' _ _ _ base' = b'

  module Pi1 (G : Group) where

    open Group G

    module KG1 = K G
    open KG1 using (KG1 ; KG1-rec ; KG1-elim)

    comp-equiv : ∀ g -> Equiv El El
    comp-equiv a = (improve (hequiv (comp a)
                                    (comp (inv a)) 
                                    (λ x → (unitl x ∘ ap (λ y → comp y x) (invl a)) ∘ ! (assoc (inv a) a x))
                                    (λ x → (unitl x ∘ ap (λ y → comp y x) (invr a)) ∘ ! (assoc a (inv a) x))))

    decode' : El → Path{KG1} KG1.base KG1.base
    decode' = KG1.loop

    Codes : KG1 → NTypes (tl 0)
    Codes = KG1-rec (NTypes-level (tl 0))
                    (El , El-level)
                    (record { f = λ g → coe (! (Path-NTypes (tl 0))) (ua (comp-equiv g));
                              pres-ident = {!!};
                              pres-comp = {!!} })

    encode : {x : KG1} -> Path KG1.base x -> fst (Codes x)
    encode α = transport (fst o Codes) α ident

    encode-decode' : ∀ x -> encode (decode' x) ≃ x
    encode-decode' x = encode (decode' x) ≃〈 id 〉 
                       encode (KG1.loop x) ≃〈 id 〉 
                       transport (fst o Codes) (KG1.loop x) ident ≃〈 {!!} 〉 
                       coe (ap (fst o Codes) (KG1.loop x)) ident ≃〈 {!!} 〉 
                       coe (fst≃ (coe (! (Path-NTypes (tl 0))) (ua (comp-equiv x)))) ident ≃〈 {!!} 〉 
                       coe (ua (comp-equiv x)) ident ≃〈 {!!} 〉 
                       comp x ident ≃〈 {!!} 〉 
                       x ∎
    
    decode : {x : _} -> fst (Codes x) -> Path KG1.base x
    decode {x} = KG1-elim (λ x' → (fst (Codes x') → Path KG1.base x') , Πlevel (λ _ → path-preserves-level KG1.KG1-level))
                          decode'
                          (λ g → transport-→-from-square (fst o Codes) (Path KG1.base) (KG1.loop g) decode' decode'
                                 (λ≃ (\ g' -> 
                                   (transport (Path KG1.base) (KG1.loop g) (decode' g') ≃〈 id 〉
                                    transport (Path KG1.base) (KG1.loop g) (KG1.loop g') ≃〈 {!!} 〉
                                    (KG1.loop g) ∘ (KG1.loop g') ≃〈 {!!} 〉
                                    (KG1.loop (comp g' g)) ≃〈 {!!} 〉
                                    KG1.loop (comp g g') ≃〈 ? 〉 -- oops came out backwards?
                                    KG1.loop (transport (fst o Codes) (KG1.loop g) g') ≃〈 id 〉 
                                    decode' (transport (fst o Codes) (KG1.loop g) g') ∎))))
                          (λ _ → HSet-UIP (Πlevel (λ _ → use-level KG1.KG1-level _ _)) _ _ _ _)
                          {!!}
                          x