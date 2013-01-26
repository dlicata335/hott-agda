
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open Paths
open import lib.Functions
open import lib.Int
open Int
open import lib.Prods
open import lib.AdjointEquiv
open import lib.Univalence
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
                adj _ (ap (λl n) (λ≃ (λ x → adj _ (ap≃ (ap (apl n) a)))))     ≃〈 ap (adj _) (ap (λ α → ap (λl n) (λ≃ α)) (λ≃ (λ x → adj-ap≃ {x = x} (ap (apl n) a) (λ x → ap^-id n (\f -> f x) {f})))) 〉
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
  open LoopΠ public using (λl ; apl) 



  module LoopPathType {A : Type} {p : Path A A} where 
    mutual
      ual : ∀ n → Loop n (A → A) (coe p) → Loop n (Path{Type} A A) p 
      ual One α = adjust (type≃η p) (ap {M = coe-equiv p} {N = coe-equiv p} 
                                             ua 
                                             (pair≃ α (HProp-unique (IsEquiv-HProp (coe p)) _ _)))
      ual (S n) α = adjust (ual-id n) (ap (ual n) α)

      ual-id : ∀ n → ual n (id^ n) ≃ id^ n
      ual-id One = {!!}
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
    β (S n) l = {!!}
  
    path : ∀ n → Loop n (A → A) (coe p) ≃ Loop n (Path{Type} A A) p
    path n = ua (improve (hequiv (ual n) (coel n) {!!} {!!}))

    
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

  postulate
    LoopSType : ∀ n {A} -> ((a : A) -> Loop n A a) ≃ (Loop (S n) Type A)
  {-
  LoopSType n = (! (LoopPath n)) ∘
                ua (improve (hequiv 
                  (λ h → coe (ap (λ (B : Σ (λ A → A))
                                    → Loop n (fst B) (snd B))
                             (! (pair≃ univalence≃ univalence≃-id)))
                         (pairl n (λl n h) 
                                (fst (use-trunc (IsTrunc-LoopOver n -2 
                                                   (λl n h)
                                                   (λ f → IsEquiv-HProp f))))))
                  (λ α y → (ap^ n (λ x → coe x y) α))
                  {!!}
                  {!!}))
  -}

  apt : ∀ n {A} -> Loop (S n) Type A → ((a : A) -> Loop n A a)
  apt n l a = coe (! (LoopSType n)) l a

  postulate
    apt-def : ∀ n {A} -> (l : Loop (S n) Type A) → (a : A) 
            → apt n l a ≃ ap^ n (\ x -> coe x a) (loopSN1 n l) 


  λt : ∀ n {A} -> ((a : A) -> Loop n A a) -> Loop (S n) Type A
  λt n l = coe (LoopSType n) l

  postulate
    apt-! : ∀ n {A} -> (α : Loop (S n) Type A) (a : _) →
              apt n (!^ (S n) α) a
            ≃ !^ n (apt n α a)


