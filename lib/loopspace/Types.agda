
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Functions
open import lib.Int
open Int
open import lib.Prods
open import lib.AdjointEquiv
open import lib.NType
open import lib.Truncations
open Truncation
open import lib.WrappedPath

open import lib.loopspace.Basics
open import lib.loopspace.Groupoid
open import lib.loopspace.Truncation

module lib.loopspace.Types where

  module LoopΠ {A : Type} {B : A → Type} {f : (x : A) → B x} where
    mutual  
     λl : ∀ n → ((x : A) → Loop n (B x) (f x)) → Loop n ((x : A) → B x) f
     λl One   α = λ≃ α
     λl (S n) α = adjust (λl-id n) (ap (λl n) (λ≃ α))
  
     λl-id : ∀ n → λl n (\ x -> (id^ n)) ≃ (id^ n)
     λl-id One = ! (Π≃η id)
     λl-id (S n') = !-inv-with-middle-r (λl-id n') (ap (ap (λl n')) (! (Π≃η id)))

    apl : ∀ n → Loop n ((x : A) → B x) f → (x : A) → Loop n (B x) (f x)
    apl n   α x = ap^ n (\ f -> f x) α 
  
    β : ∀ n → (a : (x' : A) → Loop n (B x') (f x')) → (apl n (λl n a)) ≃ a
    β One a = λ≃ (λ x → Π≃β a)
    β (S n) a = λ≃ (λ x → adjust (ap^-id n (\ f -> f x){f}) (ap (\ f -> apl n f x) (adjust (λl-id n) (ap (λl n) (λ≃ a)))) ≃〈 ap (λ y → adjust (ap^-id n (λ f' → f' x) {f}) (ap (ap^ n (λ f' → f' x)) y)) (! (adj-def (λl-id n) _)) 〉
                          adjust (ap^-id n (\ f -> f x){f}) (ap (\ f -> apl n f x) (adj _ (ap (λl n) (λ≃ a)))) ≃〈 ! (adj-def (ap^-id n (\ f -> f x){f}) _) 〉
                          adj _ (ap (\ f -> apl n f x) (adj _ (ap (λl n) (λ≃ a)))) ≃〈 adj-bind (ap-adj (λ f' → apl n f' x) _ _) 〉
                          adj _ (ap (\ f -> apl n f x) (ap (λl n) (λ≃ a))) ≃〈 ap (adj _) (! (ap-o (\ f -> apl n f x) (λl n) _)) 〉
                          adj _ (ap (λ f → apl n (λl n f) x) (λ≃ a)) ≃〈 adj-bind (ap-loop-by-equals {f = λ f → apl n (λl n f) x} {g = λ f → f x} (λ f → ap≃ (! (β n f))) _) 〉
                          adj _ (ap (λ f → f x) (λ≃ a)) ≃〈 ap (adj _) (Π≃β a) 〉
                          adj _ (a x) ≃〈 adj-eq-loop n _ _ _ _ id 〉
                          adj id (a x) ≃〈 ! (adj-id _) 〉
                          a x ∎)

    η : ∀ n → (a : _) → (λl n (apl n a)) ≃ a
    η One a = ! (Π≃η a)
    η (S n) a = adjust (λl-id n) (ap (λl n) (λ≃ (λ x → adjust (ap^-id n (\ f -> f x){f}) (ap (λ f → apl n f x) a)))) ≃〈 ap (λ α → adjust (λl-id n) (ap (λl n) (λ≃ α))) (λ≃ (λ α → ! (adj-def _ _))) 〉
                adjust (λl-id n) (ap (λl n) (λ≃ (λ x → adj (ap^-id n (\ f -> f x){f}) (ap (λ f → apl n f x) a)))) ≃〈 ! (adj-def _ _) 〉
                adj (λl-id n) (ap (λl n) (λ≃ (λ x → adj _ (ap (λ f → apl n f x) a)))) ≃〈 id 〉
                adj _ (ap (λl n) (λ≃ (λ x → adj _ (ap (λ f → apl n f x) a)))) ≃〈 id 〉 
                adj _ (ap (λl n) (λ≃ (λ x → adj _ (ap ((λ f → f x) o (apl n)) a)))) ≃〈 ap (adj _) (ap (λ y → ap (λl n) (λ≃ y)) (λ≃ (\ x -> ap (adj _) (ap-o (λ a' → a' x) (apl n) a)))) 〉 
                adj _ (ap (λl n) (λ≃ (λ x → adj _ (ap≃ (ap (apl n) a)))))     ≃〈 ap (adj _) (ap (λ α → ap (λl n) (λ≃ α)) (λ≃ (λ x → adj-ap≃-pointwise {x = x} (ap (apl n) a) (λ x → ap^-id n (\f -> f x) {f})))) 〉
                adj _ (ap (λl n) (λ≃ (λ x → ap≃ (adj _ (ap (apl n) a)) {x}))) ≃〈 ap (adj _ o ap (λl n)) (! (Π≃η _)) 〉
                adj _ (ap (λl n) (adj _ (ap (apl n) a))) ≃〈 adj-bind (ap-adj (λl n) _ _) 〉
                adj _ (ap (λl n) (ap (apl n) a)) ≃〈 ap (adj _) (! (ap-o (λl n) (apl n) a)) 〉
                adj _ (ap ((λl n) o (apl n)) a) ≃〈 adj-bind (ap-loop-by-equals {f = (λl n) o (apl n)} {g = λ x → x} (λ x → ! (η n x)) a) 〉
                adj _ (ap (λ x → x) a) ≃〈 ap (adj _) (ap-id a) 〉
                adj _ a ≃〈 adj-eq-loop n _ _ _ _ id 〉
                adj id a ≃〈 ! (adj-id _) 〉
                a ∎

    eqv : ∀ n → 
              Equiv ((x : A) → Loop n (B x) (f x))
                    (Loop n ((x : A) -> B x) f)
    eqv n = (improve (hequiv (λl n) (apl n) (β n) (η n)))

    path : ∀ n → 
              ((x : A) → Loop n (B x) (f x))
            ≃ (Loop n ((x : A) -> B x) f)
    path n = ua (eqv n) 

    ext : ∀ n → (α α' : Loop n ((x : A) → B x) f) (p : (x : A) → apl n α x ≃ apl n α' x) → α ≃ α'
    ext n α α' p = η n α' ∘ ap (λl n) (λ≃ p) ∘ ! (η n α)
  open LoopΠ public using (λl ; apl)



  module LoopPathType {A : Type} {p : Path A A} where 
    mutual
      ual : ∀ n → Loop n (A → A) (coe p) → Loop n (Path{Type} A A) p 
      ual One α = adjust (type≃η p) (ap {M = coe-equiv p} {N = coe-equiv p} 
                                             ua 
                                             (pair≃ α (HProp-unique (IsEquiv-HProp (coe p)) _ _)))
      ual (S n) α = adjust (ual-id n) (ap (ual n) α)

      ual-id : ∀ n → ual n (id^ n) ≃ id^ n
      ual-id One = transport
                     (λ β →
                        Id
                        (IsEquiv.α univalence p ∘
                         ap (IsEquiv.g univalence) (pair≃ id β) ∘
                         ! (IsEquiv.α univalence p))
                        id)
                     {id} (HSet-UIP (increment-level (IsEquiv-HProp (coe p))) _ _ _ _) (!-inv-with-middle-r (IsEquiv.α univalence p) id)  
      ual-id (S n) = !-inv-with-middle-r (ual-id n) id 

    coel : ∀ n → Loop n (Path{Type} A A) p → Loop n (A → A) (coe p) 
    coel n α = ap^ n coe α

    -- ENH why do you need to write (type≃η p) explicitly?
    β : ∀ n (l : Loop n (A → A) (coe p)) → coel n (ual n l) ≃ l
    β One l = ap coe (adjust (type≃η p) (ap {M = coe-equiv p} {N = coe-equiv p} ua (pair≃ l _))) ≃〈 ap (ap coe) (! (adj-def (type≃η p) _)) 〉 
              ap coe (adj    (type≃η p) (ap ua (pair≃ l _))) ≃〈 ap-adj coe (ap ua (pair≃ l _)) (type≃η p) 〉
              adj _  (ap coe (ap ua (pair≃ l _))) ≃〈 ap (adj _) (! (ap-o coe ua _)) 〉 
              adj _  (ap (coe o ua) (pair≃ l _)) ≃〈 adj-bind (ap-loop-by-equals {f = coe o ua} {g = fst} (λ x → ! (type≃β x)) _) 〉 
              adj _  (ap fst (pair≃ l _)) ≃〈 ap (adj _) (Σ≃β1 l _) 〉 
              adj _  l ≃〈 ap (λ x → adj x l) (!-inv-r (ap coe (type≃η p)) ∘ ap (λ x → ap coe (type≃η p) ∘ ! x) (! (type≃-coh p))) 〉 
              adj id  l ≃〈 !(adj-id _) 〉 
              (l ∎)
    β (S n) l = coel (S n) (ual (S n) l) ≃〈 id 〉 
                coel (S n) (adjust (ual-id n) (ap (ual n) l)) ≃〈 ap (coel (S n)) (! (adj-def (ual-id n) (ap (ual n) l))) 〉 
                coel (S n) (adj    (ual-id n) (ap (ual n) l)) ≃〈 id 〉 
                adjust (ap^-id n coe{p}) (ap (coel n) (adj    (ual-id n) (ap (ual n) l)))  ≃〈 ! (adj-def (ap^-id n coe{p}) (ap (ap^ n coe) (adj    (ual-id n) (ap (ual n) l)))) 〉 
                adj  (ap^-id n coe{p}) (ap (coel n) (adj    (ual-id n) (ap (ual n) l)))  ≃〈 adj-bind (ap-adj (coel n) (ap (ual n) l) _) 〉 
                adj  _ (ap (coel n) (ap (ual n) l))  ≃〈 ap (adj _) (! (ap-o (coel n) (ual n) l)) 〉 
                adj  _ (ap (coel n o ual n) l)  ≃〈 adj-bind (ap-loop-by-equals {f = coel n o ual n} {g = λ x → x} (λ x → ! (β n x)) l) 〉 
                adj  _ (ap (\ x -> x) l)  ≃〈 ap (adj _) (ap-id l) 〉 
                adj  _ l   ≃〈 adj-eq-loop n _ _ _ _ id 〉 
                adj  id l  ≃〈 ! (adj-id l) 〉 
                l ∎

    η : ∀ n (l : Loop n (Path{Type} A A) p) → (ual n (coel n l)) ≃ l
    η One l = lemma p p l _ where
       -- ENH: way to do this without using J?
       lemma : ∀ {A B : Type} (p q : Path{Type} A B) (l : Path p q)
               (β : transport IsEquiv (ap coe l) (coe-is-equiv p) ≃ coe-is-equiv q)
             -> (type≃η q) ∘ (ap ua (pair≃ (ap coe l) β)) ∘ (! (type≃η p)) ≃ l
       lemma id q l = path-induction (\ q l → 
                                        (β : transport IsEquiv (ap coe l) (coe-is-equiv id) ≃ coe-is-equiv q)
                                      → ((type≃η q) ∘ (ap ua (pair≃ (ap coe l) β)) ∘ (! (type≃η id))) ≃ l)
                                      (λ β' → transport
                                                (λ β0 →
                                                   IsEquiv.α univalence id ∘
                                                   ap (IsEquiv.g univalence) (pair≃ id β0) ∘
                                                   ! (IsEquiv.α univalence id)
                                                   ≃ id) {id}{β'}
                                                (fst (use-level (use-level (path-preserves-level (IsEquiv-HProp (λ x → x))) _ _))) 
                                                (!-inv-with-middle-r (IsEquiv.α univalence id) id))
                                      l
    η (S n) l = ual (S n) (coel (S n) l) ≃〈 id 〉 
                ual (S n) (adjust (ap^-id n coe{p}) (ap (coel n) l)) ≃〈 ap (ual (S n)) (! (adj-def (ap^-id n coe{p}) (ap (coel n) l))) 〉 
                ual (S n) (adj    (ap^-id n coe{p}) (ap (coel n) l)) ≃〈 id 〉 
                adjust (ual-id n) (ap (ual n) (adj    _ (ap (coel n) l)))  ≃〈 ! (adj-def (ual-id n) (ap (ual n) (adj _ (ap (coel n) l)))) 〉 
                adj    (ual-id n) (ap (ual n) (adj    _  (ap (coel n) l)))  ≃〈 adj-bind (ap-adj (ual n) (ap (coel n) l) _) 〉 
                adj  _ (ap (ual n) (ap (coel n) l))  ≃〈 ap (adj _) (! (ap-o (ual n) (coel n) l)) 〉 
                adj  _ (ap (ual n o coel n) l)  ≃〈 adj-bind (ap-loop-by-equals {f = ual n o coel n} {g = λ x → x} (λ x → ! (η n x)) l) 〉 
                adj  _ (ap (\ x -> x) l)  ≃〈 ap (adj _) (ap-id l) 〉 
                adj  _ l   ≃〈 adj-eq-loop n _ _ _ _ id 〉 
                adj  id l  ≃〈 ! (adj-id l) 〉 
                l ∎
  
    eqv : ∀ n → Equiv (Loop n (A → A) (coe p)) (Loop n (Path{Type} A A) p)
    eqv n = (improve (hequiv (ual n) (coel n) (β n) (η n)))

    path : ∀ n → Loop n (A → A) (coe p) ≃ Loop n (Path{Type} A A) p
    path n = ua (eqv n)

  open LoopPathType public using (coel; ual) 
    
  {-
  can get alway without Σ's for now; 
  ENH: define apd and define fstl = ap^ n fst and sndl = apd^ n snd and then
       define pairl recursively and show β η

  abstract
    LoopΣ : ∀ n {A : Type} {B : A → Type} (a : A) (b : B a) → Σ (λ α → LoopOver n α B b) ≃ Loop n (Σ B) (a , b)
    LoopΣ n {A} {B} a b = ua (improve (hequiv (i n) (e n) (βr n) {!ap^ n coe!})) where
  
      mutual
        i : ∀ n → Σ (λ α → LoopOver n α B b) → Loop n (Σ B) (a , b)
        i One (α , β) = pair≃ α β
        i (S n) (α , β) = adjust (i-id n) (ap (i n) (pair≃ α β))
  
        i-id : ∀ n → i n (id^ n , idOver n B b) ≃ id^ n
        i-id One = id
        i-id (S n) = !-inv-with-middle-r (i-id n) id
  
      mutual
        e : ∀ n → Loop n (Σ B) (a , b) → Σ (λ α → LoopOver n α B b)
        e One α = (fst≃ α , snd≃ α)
        e (S n) α = let β = adjust (e-id n) (ap (e n) α) in (fst≃ β , snd≃ β)
  
        e-id : ∀ n → e n (id^ n) ≃ (id^ n , idOver n B b)
        e-id One = id
        e-id (S n) = let β = (!-inv-with-middle-r (e-id n) id) in pair≃ (ap (ap fst) β) (apd (apd snd) β ∘ {!!})

      βr : ∀ n → (a : _) → (e n (i n a)) ≃ a
      βr One (α , β) = pair≃ (Σ≃β1 α β) (otherβ2 α β) where 
        -- FIXME: move to Prods
        otherβ2 : ∀ {M N : A} {M' : B M} {N' : B N}
                     (α : M ≃ N) (β : transport B α M' ≃ N')
                -> Path (transport (λ α' → Id (transport B α' M') N') (Σ≃β1{B = B} α β) (snd≃{B = B} (pair≃ α β))) β
        otherβ2 id id = id
      βr (S n) (α , β) = e (S n) (i (S n) (α , β)) ≃〈 id 〉 
                        let γ = adjust (e-id n) (ap (e n) (i (S n) (α , β))) in (fst≃ γ , snd≃ γ)                         ≃〈 id 〉 
                        let γ = adjust (e-id n) (ap (e n) (adjust (i-id n) (ap (i n) (pair≃ α β)))) in (fst≃ γ , snd≃ γ)  ≃〈 ap (λ x → let γ' = x in fst≃ γ' , snd≃ γ') (! (adj-def _ _)) 〉 
                        let γ = adj (e-id n) (ap (e n) (adjust (i-id n) (ap (i n) (pair≃ α β)))) in (fst≃ γ , snd≃ γ)     ≃〈 ap (\ x -> let γ = adj (e-id n) (ap (e n) x) in (fst≃ γ , snd≃ γ)) (! (adj-def _ _))〉 
                        let γ = adj (e-id n) (ap (e n) (adj (i-id n) (ap (i n) (pair≃ α β)))) in (fst≃ γ , snd≃ γ)        ≃〈 id 〉 
                        let γ = adj _ (ap (e n) (adj _ (ap (i n) (pair≃ α β)))) in (fst≃ γ , snd≃ γ)        ≃〈 ap (\x -> let γ = x in (fst≃ γ , snd≃ γ)) (adj-bind (ap-adj (e n) _ _)) 〉 
                        let γ = adj _ (ap (e n) (ap (i n) (pair≃ α β))) in (fst≃ γ , snd≃ γ)        ≃〈 ap (\x -> let γ = x in (fst≃ γ , snd≃ γ)) (! (ap (adj _ ) (ap-o (e n) (i n) _))) 〉 
                        let γ = adj _ (ap (e n  o  i n) (pair≃ α β)) in (fst≃ γ , snd≃ γ)        ≃〈  ap (\x -> let γ = x in (fst≃ γ , snd≃ γ)) (adj-bind (ap-loop-by-equals {f = (e n  o  i n)} {g = \ x -> x} (λ x → ! (βr n x)) _))〉 
                        let γ = adj _ (ap (\ x -> x)    (pair≃ α β)) in (fst≃ γ , snd≃ γ)        ≃〈 ap (λ x → let γ' = x in fst≃ γ' , snd≃ γ') (ap (adj _) (ap-id (pair≃ α β))) 〉 
                        let γ = adj _ (pair≃ α β) in (fst≃ γ , snd≃ γ)                           ≃〈 ap (\x -> let γ = x in (fst≃ γ , snd≃ γ)) {! !} 〉 
                        let γ = adj id (pair≃ α β) in (fst≃ γ , snd≃ γ)                          ≃〈 {!!} 〉 -- not sure how to finish this
                        ((α , β) ∎)
                        -- pair≃ (fst≃ (adjust (e-id n) (ap (e n) (adjust (i-id n) (ap (i n) (pair≃ α β))))) ≃〈 {!!} 〉 
                        --        fst≃ (adj (e-id n) (ap (e n) (adjust (i-id n) (ap (i n) (pair≃ α β))))) ≃〈 {!!} 〉 
                        --        fst≃ (adj (e-id n) (ap (e n) (adj (i-id n) (ap (i n) (pair≃ α β))))) ≃〈 {!!} 〉 
                        --        fst≃ (adj _ (ap (e n) (adj _ (ap (i n) (pair≃ α β))))) ≃〈 {!!} 〉 
                        --        α ∎)
                        --       {!!}

  pairl : ∀ n {A : Type} {B : A → Type} {a : A} {b : B a} (α : Loop n A a) (β : LoopOver n α B b) → Loop n (Σ B) (a , b)
  pairl n α β = coe (LoopΣ n _ _) (α , β)

  fstl : ∀ n {A : Type} {B : A → Type} {a : A} {b : B a} → Loop n (Σ B) (a , b) → Loop n A a
  fstl n α = fst (coe (! (LoopΣ n _ _)) α)

  sndl : ∀ n {A : Type} {B : A → Type} {a : A} {b : B a} (α : Loop n (Σ B) (a , b)) → LoopOver n (fstl n α) B b
  sndl n α = snd (coe (! (LoopΣ n _ _)) α)
  -}

  module LoopSType where
    eqv : ∀ n {A} -> Equiv ((a : A) -> Loop n A a) (Loop (S n) Type A)
    eqv n = (!equiv (LoopPath.eqv n) ∘equiv LoopPathType.eqv n ∘equiv LoopΠ.eqv n)

    path : ∀ n {A} -> ((a : A) -> Loop n A a) ≃ (Loop (S n) Type A)
    path n = ua (eqv n)

    λt : ∀ n {A} -> ((a : A) -> Loop n A a) -> Loop (S n) Type A
    λt n = fst (eqv n)
    -- λt n f = (loopN1S n (ual n (λl n f)))

    apt : ∀ n {A} -> Loop (S n) Type A → ((a : A) -> Loop n A a)
    apt n = IsEquiv.g (snd (eqv n))
    -- apt n α a = ap^ n (\ x -> f a) (ap^ n coe (loopSN1 n α))

    apt-def : ∀ n {A} (α : Loop (S n) Type A) (a : A) → apt n α a ≃ ap^ n (\ x -> coe x a) (loopSN1 n α)
    apt-def n α a = ! (ap^-o n (λ f → f a) coe (loopSN1 n α))

    β : ∀ n {A} (α : (a : A) -> Loop n A a) (a : A) -> 
      apt n (λt n α) a ≃ α a
    β n α a = ap≃ (IsEquiv.α (snd (eqv n)) α){a}

    η : ∀ n {A} (α : Loop (S n) Type A) → (λt n (\ x -> apt n α x)) ≃ α
    η n α = (IsEquiv.β (snd (eqv n)) α)

    -- useful corollary
    ext : ∀ n {A} {α β : Loop (S n) Type A}
        -> ((x : A) → apt n α x ≃ apt n β x)
        → α ≃ β
    ext n {_} {a} {b} p = η n b ∘ ap (λt n) (λ≃ p) ∘ ! (η n a)

  open LoopSType public using (apt ; λt)

  apt-id : ∀ n {A} (a : A) → apt n id a ≃ id^ n
  apt-id One a = id
  apt-id (S n) {A} a = apt (S n) id a ≃〈 id 〉
                       ap^ (S n) (λ f → f a) (ap^ (S n) coe (loopSN1 (S n) id)) ≃〈 ap (λ x → ap^ (S n) (λ f → f a) (ap^ (S n) coe x)) (loopSN1-id (S n) A) 〉
                       ap^ (S n) (λ f → f a) (ap^ (S n) coe (id^ (S n) {_} {id})) ≃〈 ! (ap^-o (S n) (λ f → f a) coe (id^ (S n) {_} {id})) 〉
                       ap^ (S n) (λ f → coe f a) (id^ (S n) {_} {id}) ≃〈 ap^-id (S n) (λ f → coe f a) {id} 〉
                       id^ (S n) ∎

  apt-! : ∀ n {A} -> (α : Loop (S n) Type A) (a : _) →
              apt n (!^ (S n) α) a
            ≃ !^ n (apt n α a)
  apt-! One α a = ap-! (λ f → f a) (ap coe α) ∘ ap (ap (λ f → f a)) (ap-! coe α)
  apt-! (S n) α a = apt (S n) (! α) a ≃〈 id 〉 
                    ap^ (S n) (\ f -> f a) (ap^ (S n) coe (loopSN1 (S n) (! α))) ≃〈 ap (\ x -> ap^ (S n) (\ f -> f a) (ap^ (S n) coe x)) (loopSN1-! (S n) α) 〉 
                    ap^ (S n) (\ f -> f a) (ap^ (S n) coe (! (loopSN1 (S n) α))) ≃〈 ap (λ x → ap^ (S n) (λ f → f a) x) (ap^-! (S n) coe (loopSN1 (S n) α)) 〉
                    ap^ (S n) (\ f -> f a) (! (ap^ (S n) coe (loopSN1 (S n) α))) ≃〈 ap^-! (S n) (λ f → f a) (ap^ (S n) coe (loopSN1 (S n) α)) 〉
                    ! (ap^ (S n) (\ f -> f a) (ap^ (S n) coe (loopSN1 (S n) α))) ≃〈 id 〉 
                    (! (apt (S n) α a) ∎)


  apt-apS : ∀ n {A} (B : A → Type) {a : A} (α : Loop (S n) A a) (b : B a)
         -> apt n (ap^ (S n) B α) b ≃ ap^ n (λ x → transport B x b) (loopSN1 n α)
  apt-apS n B α b = apt n (ap^ (S n) B α) b ≃〈 ap (λ x → apt n x b) (ap^-S' n B α) 〉 
                   apt n (loopN1S n (ap^ n (ap B) (loopSN1 n α))) b ≃〈 LoopSType.apt-def n (loopN1S n (ap^ n (ap B) (loopSN1 n α))) b 〉
                   ap^ n (λ x → coe x b) (loopSN1 n (loopN1S n (ap^ n (ap B) (loopSN1 n α)))) ≃〈 ap (ap^ n (λ x → coe x b)) (LoopPath.η n (ap^ n (ap B) (loopSN1 n α))) 〉
                   ap^ n (λ x → coe x b) (ap^ n (ap B) (loopSN1 n α)) ≃〈 ! (ap^-o n (λ x → coe x b) (ap B) (loopSN1 n α)) 〉
                   ap^ n (λ x → coe (ap B x) b) (loopSN1 n α) ≃〈 ap^-by-equals n {f = λ x → coe (ap B x) b} {g = λ x → transport B x b} (λ≃ (λ x → ! (ap≃ (transport-ap-assoc B x)))) (loopSN1 n α) 〉
                   rebase n _ (ap^ n (λ x → transport B x b) (loopSN1 n α)) ≃〈 ap
                                                                                  (λ x → rebase n x (ap^ n (λ x' → transport B x' b) (loopSN1 n α)))
                                                                                  ((ap
                                                                                      {M =
                                                                                       ap (λ f → f id)
                                                                                       (λ≃ (λ x → ! (ap (λ f → f b) (transport-ap-assoc B x))))}
                                                                                      {N = id} ! (Π≃β (λ x → ! (ap (λ f → f b) (transport-ap-assoc B x))) {id}) ∘ 
                                                                                     ap-! (λ f → f id)
                                                                                     (λ≃ (λ x → ! (ap (λ f → f b) (transport-ap-assoc B x)))))) 〉
                   rebase n id (ap^ n (λ x → transport B x b) (loopSN1 n α)) ≃〈 ap≃ (rebase-idpath n) 〉
                   ap^ n (λ x → transport B x b) (loopSN1 n α) ∎


  module LoopUnit where

    path : ∀ n → Unit ≃ Loop n Unit <> 
    path n = ! (Contractible≃Unit (use-level (Loop-preserves-level n -2 (ntype Contractible-Unit))))

