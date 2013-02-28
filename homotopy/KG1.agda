
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Truncation
open Int
open import homotopy.HStructure
open LoopSpace

module homotopy.KG1 where

  -- reflection of G
  module K1 (G : Group) where
   private
    module K' where
     open Group G
     
     private
       data KG1' : Type where
         base' : KG1'
       
     KG1 : Type
     KG1 = KG1'
     
     base : KG1 
     base = base'
     
     postulate {- HoTT Axiom -}
       level  : NType (tl 1) KG1
       loop       : El -> Path base base
       loop-ident : loop ident  ≃ id
       loop-comp  : ∀ g1 g2 → loop (comp g1 g2) ≃ (loop g2) ∘ (loop g1)
     
     KG1-rec : ∀ {C} 
             -> (nC : NType (tl 1) C)
             -> (b' : C)
             -> (l' : GroupHom G (PathGroup (C , nC) b'))
             -> KG1 → C
     KG1-rec _ b' _ base' = b'

     postulate {- HoTT Axiom -}
       KG1-rec/βloop : ∀ {C} 
                       -> {nC : NType (tl 1) C}
                       -> {b' : C}
                       -> (l' : GroupHom G (PathGroup (C , nC) b'))
                       -> {g : El} → ap (KG1-rec nC b' l') (loop g) ≃ GroupHom.f l' g

    -- could also have β rules for the other parts of GroupHom, but they're
    -- unique by level reasoning
     
     KG1-elim : (C : KG1 → NTypes (tl 1))
             -> (b' : fst (C base))
             -> (loop' : (x : El) → transport (fst o C) (loop x) b' ≃ b')
             -> (preserves-ident : (x : El) → Path{Path{fst (C base)} _ _}
                                               (transport (λ p → transport (fst o C) p b' ≃ b') loop-ident
                                                         (loop' ident))
                                               (id {_} {b'}))
             -> (preserves-comp  : (g1 g2 : El) → transport (λ p → transport (fst o C) p b' ≃ b') (loop-comp g1 g2) (loop' (comp g1 g2))
                                                   ≃ {! (loop' g1) !})
             -> (x : KG1) → fst (C x)
     KG1-elim _ b' _ _ _ base' = b'
   open K' public
   
   open Group G

   loop-inv : ∀ g -> loop (inv g) ≃ ! (loop g)
   loop-inv g = cancels-is-inverse ((loop-ident ∘ ap loop (invr g)) ∘ ! (loop-comp g (inv g)))
    
  abstract
      1TypeUnique : ∀ {A} (nA : NType (tl 1) A)
               -> { x y : A} {p q : x ≃ y} {r s : p ≃ q} -> r ≃ s
      1TypeUnique nA = HSet-UIP (use-level {tl 1} nA _ _) _ _ _ _

  module H-on-KG1 (A : AbelianGroup) where
    open Group (fst A)
    module KG1 = K1 (fst A)
    open KG1 using (KG1 ; KG1-rec ; KG1-elim)

    mult-loop : (g : El) (x : KG1) → x ≃ x
    mult-loop g = (KG1-elim (λ x → x ≃ x , path-preserves-level KG1.level)
                            (KG1.loop g)
                            loop'
                            (λ _ → 1TypeUnique KG1.level)
                            (λ _ _ → 1TypeUnique KG1.level)) where
      abstract
              loop' : (g' : El) → transport (λ x' → x' ≃ x') (KG1.loop g') (KG1.loop g) ≃ KG1.loop g
              loop' g' = transport (λ x → Id x x) (KG1.loop g') (KG1.loop g) ≃〈 transport-Path (λ x → x) (λ x → x) (KG1.loop g') (KG1.loop g) 〉
                         ap (λ x → x) (KG1.loop g') ∘ KG1.loop g ∘ ! (ap (λ x → x) (KG1.loop g')) ≃〈 ap (λ y → y ∘ KG1.loop g ∘ ! y) (ap-id (KG1.loop g')) 〉 
                         (KG1.loop g') ∘ KG1.loop g ∘ ! (KG1.loop g') ≃〈 ap (λ x → KG1.loop g' ∘ KG1.loop g ∘ x) (! (KG1.loop-inv g')) 〉 
                         (KG1.loop g') ∘ KG1.loop g ∘ (KG1.loop (inv g')) ≃〈 ap (λ x → KG1.loop g' ∘ x) (! (KG1.loop-comp (inv g') g)) 〉 
                         (KG1.loop g') ∘ KG1.loop (comp (inv g') g) ≃〈 ! (KG1.loop-comp (comp (inv g') g) g') 〉 
                         KG1.loop (comp (comp (inv g') g) g') ≃〈 ap KG1.loop (ap (λ x → comp x g') (snd A (inv g') g)) 〉 
                         KG1.loop (comp (comp g (inv g')) g') ≃〈 ap KG1.loop (assoc g (inv g') g') 〉 
                         KG1.loop (comp g (comp (inv g') g')) ≃〈 ap (λ x → KG1.loop (comp g x)) (invl g') 〉 
                         KG1.loop (comp g ident) ≃〈 ap KG1.loop (unitr g) 〉 
                         KG1.loop g ∎


    mutual
      mult : KG1 -> KG1 -> KG1 
      mult = KG1-rec (Πlevel (λ _ → KG1.level)) 
                     (λ x → x)
                     mult-hom
  
      mult-hom = (record { f = λ g → λ≃ (mult-loop g);
                           pres-ident = ! (Π≃η id) ∘ ap λ≃ (λ≃ (KG1-elim (λ x → _ , path-preserves-level (path-preserves-level KG1.level))
                                                                         KG1.loop-ident
                                                                         (λ _ → 1TypeUnique KG1.level)
                                                                         (λ _ → 1TypeUnique (path-preserves-level KG1.level))
                                                                         (λ _ _ → 1TypeUnique (path-preserves-level KG1.level))));
                           pres-comp = λ g1 g2 → ! (∘λ≃ _ _) ∘ ap λ≃ (λ≃ (KG1-elim
                                                                            (λ x → _ , path-preserves-level (path-preserves-level KG1.level)) 
                                                                            (KG1.loop-comp g1 g2)
                                                                            (λ _ → 1TypeUnique KG1.level)
                                                                            (λ _ → 1TypeUnique (path-preserves-level KG1.level))
                                                                            (λ _ _ → 1TypeUnique (path-preserves-level KG1.level)))) })

    mult-isequiv : (x : KG1) → IsEquiv (mult x)
    mult-isequiv = KG1-elim (\ x -> _ , raise-HProp (IsEquiv-HProp _))
                            (snd id-equiv)
                            (λ x → HProp-unique (IsEquiv-HProp _) _ _)
                            (λ _ → HSet-UIP (increment-level (IsEquiv-HProp _)) _ _ _ _)
                            (λ _ _ → HSet-UIP (increment-level (IsEquiv-HProp _)) _ _ _ _)

    H-KG1 : H-Structure KG1 KG1.base
    H-KG1 = record { _⊙_ = mult; 
                     unitl = KG1-elim (λ x → mult KG1.base x ≃ x , path-preserves-level KG1.level)
                                      id
                                      (λ g → (!-inv-r (ap (λ x → x) (KG1.loop g)) ∘ 
                                              ∘-assoc (ap (λ x → x) (KG1.loop g)) id (! (ap (λ x → x) (KG1.loop g)))) ∘
                                              transport-Path (λ x → x) (λ x → x) (KG1.loop g) id) 
                                      (\ _ -> 1TypeUnique KG1.level) 
                                      (\ _ _ -> 1TypeUnique KG1.level);
                     unitr = KG1-elim
                               (λ x → mult x KG1.base ≃ x , path-preserves-level KG1.level)
                               id
                               (λ x → (transport (λ x' → mult x' KG1.base ≃ x') (KG1.loop x) id) ≃〈 transport-Path (λ x' → mult x' KG1.base) (λ x' → x') (KG1.loop x) id 〉 
                                      (ap (\ x -> x) (KG1.loop x) ∘ id ∘ (! (ap (λ x' → mult x' KG1.base) (KG1.loop x)))) ≃〈 ap (λ y → y ∘ id ∘ ! (ap (λ x' → mult x' KG1.base) (KG1.loop x))) (ap-id (KG1.loop x)) 〉 
                                      ((KG1.loop x) ∘ id ∘ ! (ap (λ x' → mult x' KG1.base) (KG1.loop x))) ≃〈 ap (λ y → KG1.loop x ∘ y) (∘-unit-l (! (ap (λ x' → mult x' KG1.base) (KG1.loop x)))) 〉 
                                      ((KG1.loop x) ∘ ! (ap (λ x' → mult x' KG1.base) (KG1.loop x))) ≃〈 ap (λ y → KG1.loop x ∘ ! y) (ap-o (λ f → f KG1.base) mult (KG1.loop x)) 〉
                                      ((KG1.loop x) ∘ ! (ap≃ (ap mult (KG1.loop x)) {KG1.base})) ≃〈 ap (λ y → KG1.loop x ∘ ! (ap≃ y {KG1.base})) (KG1.KG1-rec/βloop mult-hom)  〉 
                                      ((KG1.loop x) ∘ ! (ap≃ (λ≃ (mult-loop x)) {KG1.base})) ≃〈 ap (λ y → KG1.loop x ∘ ! y) (Π≃β (mult-loop x)) 〉 
                                      ((KG1.loop x) ∘ ! (KG1.loop x)) ≃〈 !-inv-r (KG1.loop x)  〉
                                      id ∎)
                               (λ _ → 1TypeUnique KG1.level) (λ _ _ → 1TypeUnique KG1.level); 
                     unitcoh = id;
                     isequivl = mult-isequiv }

  module Pi1 (G : Group) where

    open Group G

    module KG1 = K1 G
    open KG1 using (KG1 ; KG1-rec ; KG1-elim)

    comp-equiv : ∀ g -> Equiv El El
    comp-equiv a = (improve (hequiv (\ x -> comp x a)
                                    (\ x -> comp x (inv a)) 
                                    (λ x → (unitr x ∘ ap (λ y → comp x y) (invr a)) ∘ assoc x a (inv a))
                                    (λ x → (unitr x ∘ ap (λ y → comp x y) (invl a)) ∘ assoc x (inv a) a)))

    decode' : El → Path{KG1} KG1.base KG1.base
    decode' = KG1.loop

    Codes : KG1 → NTypes (tl 0)
    Codes = KG1-rec (NTypes-level (tl 0))
                    (El , El-level)
                    (record { f = f;
                              pres-ident = pri ;
                              pres-comp = prc }) where
        f : ∀ g → (El , El-level) ≃ (El , El-level)
        f =  λ g → coe (Path-NTypes (tl 0)) (ua (comp-equiv g))

        abstract
          pri : f ident ≃ id
          pri = coe (! (Path2-NTypes (tl 0) _ _))
                    (type≃-ext (ua (comp-equiv ident)) id 
                               (λ x → unitr x ∘ ap≃ (type≃β (comp-equiv ident)) {x}) 
                     ∘ Path-NTypesβ (tl 0) (ua (comp-equiv ident)))

          prc : ∀ g1 g2 -> f (comp g1 g2) ≃ f g2 ∘ f g1
          prc g1 g2 = coe (! (Path2-NTypes (tl 0) _ _)) 
                          (! (ap-∘ fst (f g2) (f g1)) ∘ 
                           ! (ap (λ x → x ∘ ap fst (f g1)) (Path-NTypesβ (tl 0) (ua (comp-equiv g2)))) ∘ 
                           ! (ap (λ x → ua (comp-equiv g2) ∘ x) (Path-NTypesβ (tl 0) (ua (comp-equiv g1)))) ∘ 
                           type≃-ext (ua (comp-equiv (comp g1 g2))) (ua (comp-equiv g2) ∘ ua (comp-equiv g1)) 
                                     (λ g → ! (ap≃ (transport-∘ (λ x → x) (ua (comp-equiv g2)) (ua (comp-equiv g1)))) ∘ 
                                            (! (ap≃ (type≃β (comp-equiv g2))) ∘ ! (ap (λ x → fst (comp-equiv g2) x) (ap≃ (type≃β (comp-equiv g1)))) ∘
                                            ! (assoc g g1 g2)) ∘
                                            ap≃ (type≃β (comp-equiv (comp g1 g2)))) 
                           ∘ Path-NTypesβ (tl 0) (ua (comp-equiv (comp g1 g2))))
          

    abstract
      transport-Codes-loop : ∀ g g' -> (transport (fst o Codes) (KG1.loop g) g') ≃ comp g' g
      transport-Codes-loop g g' = transport (fst o Codes) (KG1.loop g) g' ≃〈 ap≃ (transport-ap-assoc' fst Codes (KG1.loop g)) 〉 
                                  transport fst (ap  Codes (KG1.loop g)) g' ≃〈 ap (λ x → transport fst x g') (KG1.KG1-rec/βloop _) 〉 -- might need to fill the _ in new agda
                                  transport fst (coe (Path-NTypes (tl 0)) (ua (comp-equiv g))) g' ≃〈 ap≃ (transport-ap-assoc fst (coe (Path-NTypes (tl 0)) (ua (comp-equiv g)))) 〉 
                                  coe (fst≃ (coe (Path-NTypes (tl 0)) (ua (comp-equiv g)))) g' ≃〈 ap (λ x → coe x g') (Path-NTypesβ (tl 0) (ua (comp-equiv g))) 〉 
                                  coe (ua (comp-equiv g)) g' ≃〈 ap≃ (type≃β (comp-equiv g)) 〉 
                                  comp g' g ∎

    encode : {x : KG1} -> Path KG1.base x -> fst (Codes x)
    encode α = transport (fst o Codes) α ident

    abstract
      encode-decode' : ∀ x -> encode (decode' x) ≃ x
      encode-decode' x = encode (decode' x) ≃〈 id 〉 
                         encode (KG1.loop x) ≃〈 id 〉 
                         transport (fst o Codes) (KG1.loop x) ident ≃〈 transport-Codes-loop x ident 〉 
                         comp ident x ≃〈 unitl x 〉 
                         x ∎
    
    decode : {x : _} -> fst (Codes x) -> Path KG1.base x
    decode {x} = KG1-elim (λ x' → (fst (Codes x') → Path KG1.base x') , Πlevel (λ _ → path-preserves-level KG1.level))
                          decode'
                          loop'
                          (λ _ → HSet-UIP (Πlevel (λ _ → use-level KG1.level _ _)) _ _ _ _)
                          (λ _ _ → HSet-UIP (Πlevel (λ _ → use-level KG1.level _ _)) _ _ _ _)
                          x where
      abstract
         loop' : ∀ g -> transport (\x -> fst (Codes x) -> Path KG1.base x) (KG1.loop g) decode' ≃ decode'
         loop' = (λ g → transport-→-from-square (fst o Codes) (Path KG1.base) (KG1.loop g) decode' decode'
                                      (λ≃ (\ g' -> 
                                        (transport (Path KG1.base) (KG1.loop g) (decode' g') ≃〈 id 〉
                                         transport (Path KG1.base) (KG1.loop g) (KG1.loop g') ≃〈 transport-Path-right (KG1.loop g) (KG1.loop g') 〉
                                         (KG1.loop g) ∘ (KG1.loop g') ≃〈 ! (KG1.loop-comp g' g) 〉
                                         KG1.loop (comp g' g) ≃〈 ap KG1.loop (! (transport-Codes-loop g g')) 〉 
                                         KG1.loop (transport (fst o Codes) (KG1.loop g) g') ≃〈 id 〉 
                                         decode' (transport (fst o Codes) (KG1.loop g) g') ∎))))