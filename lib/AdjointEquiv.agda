{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths 
open import lib.Prods
open import lib.NType
open import lib.WEq
open import lib.Functions

module lib.AdjointEquiv where

 id-equiv : ∀ {A} -> Equiv A A
 id-equiv = ( (\ x -> x) , isequiv (λ x → x) (\ _ -> id) (\ _ -> id) (\ _ -> id))

 snde : ∀ {A B} → Equiv A B → B → A
 snde e = IsEquiv.g (snd e)

 -- NOTE: because this just flips the first four, IsEquiv.γ (!equiv e) works as a name for the other ("sixth") triangle equality for e
 !equiv : ∀ {A B} → Equiv A B → Equiv B A
 !equiv (f , isequiv g α β γ) = 
   equiv g f β α 
    (λ y → α (g y)                                                                       ≃〈 ! (∘-assoc (α (g y)) (ap (λ x → g (f x)) (α (g y))) (! (α (g (f (g y)))))) ∘ move-right-right-! (α (g y)) (! (α (g (f (g y))))) _ (move-right-! (α (g y)) (α (g y) ∘ ! (! (α (g (f (g y)))))) _ (! (ap-by-id (λ x → ! (α x)) (α (g y))))) 〉 
           α (g y) ∘ ap (g o f) (α (g y)) ∘ ! (α (g (f (g y))))                          ≃〈 ap (λ a → α (g y) ∘ a ∘ ! (α (g (f (g y))))) (ap (ap g) (! (γ (g y))) ∘ ap-o g f (α (g y))) 〉 
           α (g y) ∘ ap g (β (f (g y))) ∘ ! (α (g (f (g y))))                            ≃〈 ap (λ a → α (g y) ∘ ap g a ∘ ! (α (g (f (g y))))) (inverses-natural g f β) 〉 
           α (g y) ∘ ap g (ap (f o g) (β y)) ∘ ! (α (g (f (g y))))                      ≃〈 ap (λ a → α (g y) ∘ a ∘ ! (α (g (f (g y))))) (ap-o (g o f) g (β y) ∘ ! (ap-o g (f o g) (β y))) 〉 
           α (g y) ∘ ap (g o f) (ap g (β y)) ∘ ! (α (g (f (g y))))                      ≃〈 ap (λ a → α (g y) ∘ a ∘ ! (α (g (f (g y))))) (ap (λ a → ! (α (g y)) ∘ ap g (β y) ∘ a) (!-invol (α (g (f (g y))))) ∘ ap-by-id (λ x → ! (α x)) (ap g (β y))) 〉 
           α (g y) ∘ (! (α (g y)) ∘ (ap g (β y)) ∘ α (g (f (g y)))) ∘ ! (α (g (f (g y)))) ≃〈 rassoc-1-3-1 (α (g y)) (! (α (g y))) (ap g (β y)) (α (g (f (g y)))) (! (α (g (f (g y)))))〉 
           α (g y) ∘ ! (α (g y)) ∘ (ap g (β y)) ∘ α (g (f (g y))) ∘ ! (α (g (f (g y))))   ≃〈 !-inv-r-front _ _ 〉 
           (ap g (β y)) ∘ α (g (f (g y))) ∘ ! (α (g (f (g y))))                          ≃〈 !-inv-r-back (ap g (β y)) (α (g (f (g y)))) 〉 
           (ap g (β y) ∎))

 -- ENH: can probably do this one without changing α or β too
 _∘equiv_ : ∀ {A B C} -> Equiv B C → Equiv A B -> Equiv A C
 _∘equiv_ (f , isequiv g α β γ) (f' , isequiv g' α' β' γ') = 
    improve (hequiv (f o f') (g' o g) (λ x → α' x ∘ ap g' (α (f' x))) (λ y → β y ∘ ap f (β' (g y))))

 infixr 10 _∘equiv_
 
 IsEquiv-as-tuple≃ : ∀ {A B} (f : A → B)
                  -> IsEquiv f ≃ 
                     (Σe (Σe (B → A) (λ g → (x : B) → Id (f (g x)) x))
                          (λ gβ → Σe ((x : A) → Id (fst gβ (f x)) x)
                                     (λ α → (x : A) → Id (snd gβ (f x)) (ap f (α x)))))
 IsEquiv-as-tuple≃ f = ua (improve (hequiv (λ {(isequiv g α β γ) → (g , β) , α , γ}) (\ {((g , β) , αγ) → isequiv g (fst αγ) β (snd αγ)}) (λ _ → id) (λ _ → id)))

 IsWeq≃IsEquiv : {A B : Type} (f : A → B)
              -> IsWEq f ≃ IsEquiv f
 IsWeq≃IsEquiv{A}{B} f = IsWEq f ≃〈 id 〉 
                  ((y : B) → Contractible (Σ \x -> Path (f x) y)) ≃〈 id 〉 
                  ((y : B) → Σ (\ (p : (Σ \x -> Path (f x) y)) → ((q : (Σ \x -> Path (f x) y)) → Path p q))) ≃〈 ΠΣcommute _ _ _ 〉 
                  Σ (λ (f' : (x : B) → Σ (λ x' → Path (f x') x)) → (x : B) (q : Σ (λ x' → Path (f x') x)) → Path (f' x) q) ≃〈 apΣ' (ΠΣcommuteEquiv _ _ _) (λ x' → id) 〉 
                  Σ (λ (f' : Σ (λ (g : B → A) → (x : B) → Path (f (g x)) x)) 
                     → (y : B) (q : Σ (λ (x : A) → Path (f x) y)) → Path (fst f' y , snd f' y) q) ≃〈 ap (λ t → Σ {A = Σ (λ (g : B → A) → (x : B) → Path (f (g x)) x)} t) (λ≃ STS) 〉 
                  Σ (λ x → Σ (λ α → (x' : A) → snd x (f x') ≃ ap f (α x'))) ≃〈 ! (IsEquiv-as-tuple≃ f) 〉 
                  IsEquiv f ∎ where
   STS : (f' : Σ (λ (g : B → A) → (x : B) → Path (f (g x)) x)) → 
        ((y : B) (q : Σ (λ (x : A) → Path (f x) y)) → Path (fst f' y , snd f' y) q) 
       ≃ Σ (λ α → (x : A) → snd f' (f x) ≃ ap f (α x)) 
   STS f' = ((y : B) (q : Σ (λ (x : A) → Path (f x) y)) → Path (fst f' y , snd f' y) q) ≃〈 ap (λ C → (y : B) → C y) (λ≃ (λ y → uncurry≃ A (λ x → Path (f x) y) _)) 〉
            ((y : B) (x : A) (y' : Path (f x) y) → Path{Σ (λ v → Path (f v) y)} (fst f' y , snd f' y) (x , y')) ≃〈 exchange≃ 〉
            ((x : A) (y : B) (y' : Path (f x) y) → Path{Σ (λ v → Path (f v) y)} (fst f' y , snd f' y) (x , y')) ≃〈 ap (λ B' → (x : A) → B' x) (λ≃ (λ x → path-induction≃)) 〉
            ((x : A) → Path{Σ (λ v → Path (f v) (f x))} (fst f' (f x) , snd f' (f x)) (x , id)) ≃〈 ap (λ C → (x : A) → C x) (λ≃ (λ x → ! ΣPath.path)) 〉
            ((x : A) → Σ (λ α → Path (transport (λ v → Path (f v) (f x)) α (snd f' (f x))) id)) ≃〈 ΠΣcommute _ _ _ 〉 
            Σ (λ (α : (x : A) → Id (fst f' (f x)) x) → (x : A) → Path (transport (λ v → Path (f v) (f x)) (α x) (snd f' (f x))) id) ≃〈 ap (λ C → Σ (λ (α : (x : A) → Id (fst f' (f x)) x) → C α)) (λ≃ (λ α → ap (λ C → (x : A) → C x) (λ≃ (λ x → STS' α x)))) 〉 
            Σ (λ α → (x : A) → snd f' (f x) ≃ ap f (α x)) ∎ where
       STS' : (α : (x : A) → Id (fst f' (f x)) x) → 
              (x : A) 
            → Path (transport (λ v → Path (f v) (f x)) (α x) (snd f' (f x))) id
            ≃ (snd f' (f x) ≃ ap f (α x)) 
       STS' α x = transport (λ v → Path (f v) (f x)) (α x) (snd f' (f x)) ≃ id ≃〈 ap (BackPath _) (transport-Path-pre' f (α x) (snd f' (f x))) 〉
                  (snd f' (f x) ∘ ! (ap f (α x))) ≃ id ≃〈 cancels-inverse-is≃ (snd f' (f x)) (ap f (α x)) 〉 
                  (snd f' (f x)) ≃ (ap f (α x)) ∎

 abstract
   IsEquiv-HProp : {A B : Type} (f : A → B) → HProp (IsEquiv f)
   IsEquiv-HProp f = transport HProp (IsWeq≃IsEquiv f) (IsWEq-HProp f)


 transport-IsEquiv-g : ∀ {A B} {f g : A → B} (α : f ≃ g) (e : IsEquiv f)
                        → IsEquiv.g (transport IsEquiv α e) ≃ IsEquiv.g e
 transport-IsEquiv-g id e = id


 module ApEquiv where
    apPath : {A B : Type} → (α : A == B) → {M N : A} → Path M N == Path (coe α M) (coe α N)
    apPath id = id 

    wrap : {A  B : Type} (f : Equiv A B) → {M N : A} → Equiv (Path M N) (Path (fst f M) (fst f N))
    wrap f {M}{N} = coe-equiv (ap (λ f₁ → Path (f₁ M) (f₁ N)) (type≃β f)) ∘equiv coe-equiv (apPath (ua f) {M} {N})

    calculate-map : {A B : Type} (f : Equiv A B) {M N : A} (α : M == N)
         → fst (wrap f {M}{N}) α == ap (fst f) α
    calculate-map f {M} id = coe (ap (λ f₁ → Path (f₁ M) (f₁ M)) (type≃β f)) (coe (apPath (ua f) {M} {M}) id) ≃〈 ap (λ z → coe (ap (λ f₁ → Path (f₁ M) (f₁ M)) (type≃β f)) (z id)) (apPath-is-ap (ua f)) 〉 
                    coe (ap (λ f₁ → Path (f₁ M) (f₁ M)) (type≃β f)) (ap (coe (ua f)) id) ≃〈 id 〉 
                    coe (ap (λ f₁ → Path (f₁ M) (f₁ M)) (type≃β f)) id ≃〈 reduction (type≃β f) id 〉 
                    (ap≃ (type≃β f)) ∘ ! (ap≃ (type≃β f)) ≃〈 !-inv-r (ap≃ (type≃β f)) 〉 
                    id ∎ where
      apPath-is-ap : {A B : Type} → (α : A == B) → {M N : A} → coe (apPath α {M}{N}) == ap (coe α)
      apPath-is-ap id = λ≃ (λ x → ! (ap-id x))

      reduction : {A B : Type} {M N : A} {f g : A → B} (β : Path f g) (α : Path (f M) (f N))
           →  coe (ap (λ f₁ → Path (f₁ M) (f₁ N)) β) α
           == (ap≃ β {N} ∘ α) ∘ ! (ap≃ β {M})
      reduction id α = ! (∘-unit-l α)
 
    thm : {A B : Type} (f : Equiv A B) {M N : A} → IsEquiv {Path M N} (ap (fst f))
    thm f = transport IsEquiv (λ≃ (calculate-map f)) (snd (wrap f))
               
 elim-along-equiv : {A B : Type} 
               → (P : B → Type) 
               → (e : Equiv A B)
               → ((x : A) → P (fst e x))
               → ((y : B) → P y)
 elim-along-equiv P e b y = transport P (IsEquiv.β (snd e) y) (b (IsEquiv.g (snd e) y))

 ine : {A B : Type} → Equiv A B → B → A
 ine (f , isequiv g _ _ _) = g

 oute : {A B : Type} → Equiv A B → A → B
 oute (f , _ ) = f
 
 grab-point-in-range : ∀ {A B} (f : A → B) → (B → IsEquiv f) → IsEquiv f
 grab-point-in-range f p = coe (IsWeq≃IsEquiv f) (λ b → coe (! (IsWeq≃IsEquiv f)) (p b) b)

 equiv-adjunction : ∀ {A B} (e : Equiv A B) {a : A} {b : B} → Equiv (fst e a == b) (a == snde e b)
 equiv-adjunction e {a}{b} = 
    improve (hequiv (λ p → ap (IsEquiv.g (snd e)) p ∘ ! (IsEquiv.α (snd e) a))
                    (λ p → IsEquiv.β (snd e) b ∘ ap (fst e) p) 
                    -- ENH could write these out more explcitly if we need them
                    (path-induction
                       (λ b₁ x → Path (IsEquiv.β (snd e) b₁ ∘ ap (fst e) (ap (IsEquiv.g (snd e)) x ∘ ! (IsEquiv.α (snd e) a))) x)
                       (coe (! (cancels-inverse-is≃ (IsEquiv.β (snd e) (fst e a)) (ap (fst e) (IsEquiv.α (snd e) a)))) (IsEquiv.γ (snd e) a)
                        ∘ ap (λ x → IsEquiv.β (snd e) (fst e a) ∘ x) (ap-! (fst e) (IsEquiv.α (snd e) a) ∘ ap (ap (fst e)) (∘-unit-l (! (IsEquiv.α (snd e) a))))))
                    (path-induction-l
                       (λ a₁ y → Path (ap (IsEquiv.g (snd e)) (IsEquiv.β (snd e) b ∘ ap (fst e) y) ∘ ! (IsEquiv.α (snd e) a₁)) y)
                       (coe
                          (!
                           (cancels-inverse-is≃
                            (ap (fst (!equiv e)) (IsEquiv.α (snd (!equiv e)) b))
                            (IsEquiv.β (snd (!equiv e)) (fst (!equiv e) b))))
                          (! (IsEquiv.γ (snd (!equiv e)) b)))))

 left-inverse-of-equiv-is-inverse : ∀ {A B} {f : A → B} (e : IsEquiv f) 
                                    (g : B → A) → ( (a : A) → g (f a) == a)
                                    → Σ \ (e : Equiv A B) → (fst e == f) × (IsEquiv.g (snd e) == g)
 left-inverse-of-equiv-is-inverse {f = f} e g li = 
   improve (hequiv f g li (elim-along-equiv (λ y → f (g y) == y) (f , e) (λ x → ap f (li _)))) , id , id

 right-inverse-of-equiv-is-inverse : ∀ {A B} {f : A → B} (e : IsEquiv f) 
                                    (g : B → A) → ( (y : B) → f (g y) == y)
                                    → Σ \ (e : Equiv A B) → (fst e == f) × (IsEquiv.g (snd e) == g)
 right-inverse-of-equiv-is-inverse {f = f} e g ri = 
   improve (hequiv f g (elim-along-equiv (λ y → g (f y) == y) (!equiv (f , e)) (λ x → IsEquiv.α e _ ∘ ap (IsEquiv.g e) lemma ∘ ! (IsEquiv.α e _))) ri) , id , id where
     lemma : ∀ {x} → (f (g (f (IsEquiv.g e x)))) == (f (IsEquiv.g e x))
     lemma = (! (IsEquiv.β e _) ∘ IsEquiv.β e _) ∘ ri _

