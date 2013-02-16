
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths 
open import lib.AdjointEquiv
open import lib.Functions
open import lib.Prods
open import lib.NType
open import lib.Universe
open import lib.Truncations
open Truncation

module lib.NConnected where

  Connected : TLevel -> Type -> Type
  Connected n A = NType -2 (Trunc n A)

  out-of-contractible : ∀ {A C} (f : A -> C) (cA : NType -2 A) (a b : A)
                      → f a ≃ f b
  out-of-contractible f cA _ _ = ap f (HProp-unique (increment-level cA) _ _ )

  module ConnectedFib where 
   somewhere : (n : TLevel) {A : Type} {a : A}
             -> Connected (S n) A 
             -> (P : A → NTypes n)
             -> ((x : A) → fst (P x)) → (fst (P a))
   somewhere n {A}{a} c P f = f a

   everywhere : (n : TLevel) {A : Type} {a : A}
             -> Connected (S n) A 
             -> (P : A → NTypes n)
             -> (fst (P a)) → ((x : A) → fst (P x))
   everywhere n {A}{a} c P p = λ x → coe (! (ap fst (ap≃ lemma))) p 
     where lemma1 : (Trunc-rec (NTypes-level n) (λ x' → P x')) ≃ (\ _ -> P a)
           lemma1 = λ≃ (λ x → out-of-contractible (Trunc-rec (NTypes-level n) (λ x' → P x')) c x [ a ])
   
           lemma : P ≃ (\ _ -> P a) 
           lemma = P ≃〈 id 〉
                   Trunc-rec (NTypes-level n) (λ x' → P x') o [_] ≃〈 ap (λ f → f o ([_]{S n})) lemma1 〉
                   (\ _ -> P a) o ([_]{S n}) ≃〈 id 〉
                   ((λ _ → P a) ∎)
   postulate
     everywhereβ : (n : TLevel) {A : Type} {a : A}
               -> (cA : Connected (S n) A)
               -> (P : A → NTypes n)
               -> (at-base : fst (P a)) 
               -> everywhere n cA P at-base a ≃ at-base
{-
   eqv : (n : TLevel) {A : Type} {a : A}
        -> Connected (S n) A 
        -> (P : A → NTypes n)
        -> Equiv (fst (P a)) ((x : A) → fst (P x))
   eqv n c P = improve (hequiv (everywhere n c P) (somewhere n c P) {!!} {!!})

   path : (n : TLevel) {A : Type} {a : A}
        -> Connected (S n) A 
        -> (P : A → NTypes n)
        -> Path (fst (P a)) ((x : A) → fst (P x))
   path n c P = ua (eqv n c P)
-}

  module ConnectedProduct where

    Extensions : (A : Type) (a0 : A) (C : A -> Type) (c0 : C a0) -> Type
    Extensions A a0 C c0 = Σ (λ (f : (a : A) → (C a)) → f a0 ≃ c0)
    
    Extensions-Path : {A : Type} {a0 : A} (C : A -> Type) (c0 : C a0) 
                    (e1 e2 : Extensions A a0 C c0)
                    -> Path{(Extensions A a0 C c0)} e1 e2
                     ≃ Extensions A a0 (\ a -> Path{(C a)} (fst e1 a) (fst e2 a)) 
                                       (! (snd e2) ∘ snd e1)
    Extensions-Path {A}{a0}C c0 (f1 , α1) (f2 , α2) = 
      Path (f1 , α1) (f2 , α2)  ≃〈 ! ΣPath.path 〉 
      Σ (λ α → Path (transport (λ f → f a0 ≃ c0) α α1) α2) ≃〈 apΣ' (!equiv ΠPath.eqv) (λ _ → id) 〉 
      Σ (λ (h : (x : A) → Path (f1 x) (f2 x)) →
           Path (transport (λ f → f a0 ≃ c0) (λ≃ h) α1) α2) ≃〈 ap (λ B → Σ B) (λ≃ (λ h → ap (BackPath _) (ap (λ x → α1 ∘ ! x) (Π≃β h) ∘ transport-Path-pre' (λ f → f a0) (λ≃ h) α1))) 〉 
      Σ (λ (h : (x : A) → Path (f1 x) (f2 x)) →
           Path (α1 ∘ ! (h a0)) α2) ≃〈 ap (λ B → Σ B) (λ≃ (λ h → flip≃ ∘ flip-triangle≃ α1 α2 (h a0))) 〉 
      Σ (\ h -> h a0 ≃ ! α2 ∘ α1) ≃〈 id 〉 
      Extensions A a0 (λ a → Path (f1 a) (f2 a)) (! α2 ∘ α1) ∎
      
    Extensions-level : ∀ {m n} {A : Type} (cA : Connected (S m) A)
                         (a0 : A) (C : A -> NTypes (plus2 n m)) (c0 : fst (C a0))
                     -> NType n (Extensions A a0 (fst o C) c0)
    Extensions-level {m}{ -2} cA a0 C c0 = 
     ntype ((ConnectedFib.everywhere m cA C c0 , ConnectedFib.everywhereβ m cA C c0) ,
           (λ {(f , α) → pair≃ (λ≃ 
             (ConnectedFib.everywhere 
                m {_} {a0} cA 
                (λ a → Path (ConnectedFib.everywhere m cA C c0 a) (f a) , path-preserves-level (snd (C a)))
                (! α ∘ ConnectedFib.everywhereβ m cA C c0)))
             FIXME})) where
     postulate FIXME : ∀ {A} -> A
    Extensions-level {m}{S n} cA a0 C c0 =
      ntype (λ e1 e2 → transport (NType n) 
             (! (Extensions-Path (fst o C) c0 e1 e2))
             (Extensions-level {_} {n} cA a0 (\ a -> (Path (fst e1 a) (fst e2 a), use-level (snd (C a)) _ _)) 
                                             (! (snd e2) ∘ snd e1)))
    
    wedge-elim' : ∀ {m n} {A B : Type} 
                   (cA : Connected (S m) A) 
                   (cB : Connected (S n) B)
                   (C : A → B → NTypes (plus2 m n)) 
                   {a0 : A} {b0 : B}
                -> (fa0 : (b' : B) -> fst (C a0 b'))
                -> (fb0 : (a' : A) -> fst (C a' b0))
                -> fa0 b0 ≃ fb0 a0 
                -> (a' : A) -> (b' : B) -> fst (C a' b')
    wedge-elim'{m}{n}{A}{B} cA cB C {a0}{b0} fa0 fb0 agree a = 
      fst
        (ConnectedFib.everywhere m {_} {a0} cA
         (λ a' → Extensions _ _ (fst o (C a')) (fb0 a') , 
                 Extensions-level {n} {m} cB b0 (C a') (fb0 a')) 
         (fa0 , agree)
         a)
    
    wedge-elim : ∀ {m n p} {A B : Type} 
                   (cA : Connected (S m) A) 
                   (cB : Connected (S n) B)
                   (C : A → B → NTypes p) 
                   (app : p <=tl plus2 m n)
                   {a0 : A} {b0 : B}
                -> (fa0 : (b' : B) -> fst (C a0 b'))
                -> (fb0 : (a' : A) -> fst (C a' b0))
                -> fa0 b0 ≃ fb0 a0 
                -> (a' : A) -> (b' : B) -> fst (C a' b')
    wedge-elim{m}{n}{p}{A}{B} cA cB C ap  = 
      wedge-elim' cA cB (λ a b → fst (C a b) , raise-level ap (snd (C a b))) 
    
    {-
    postulate
      wedge-elim-βa : ∀{m}{n}{p} {A B : Type}
                     (cA : Connected m A) (cB : Connected n B) (C : A → B → NTypes p) {a : A} {b : B}
                  -> (fa : (b' : B) -> fst (C a b'))
                  -> (fb : (a' : A) -> fst (C a' b))
                  -> (agree : fa b ≃ fb a)
                  -> (wedge-elim cA cB C app fa fb agree a ≃ fa)
      
      wedge-elim-βb : ∀{m}{n}{p} {A B : Type}
                     (cA : Connected m A) (cB : Connected n B) (C : A → B → NTypes p) {a : A} {b : B}
                  -> (fa : (b' : B) -> fst (C a b'))
                  -> (fb : (a' : A) -> fst (C a' b))
                  -> (agree : fa b ≃ fb a)
                  -> (\ a' -> wedge-elim cA cB C app fa fb agree a' b) ≃ fb
    -}

    wedge-rec : ∀ {m n p} {A B C : Type} 
              -> Connected (S m) A 
              -> Connected (S n) B
              -> NType p C 
              -> p <=tl (plus2 m n)
              -> {a : A} {b : B}
              -> (fa : B -> C)
              -> (fb : A -> C)
              -> fa b ≃ fb a 
              -> A -> B -> C
    wedge-rec cA cB nC = wedge-elim cA cB (\ _ _ -> _ , nC) 
    
    postulate
      wedge-rec-βa : ∀ {m}{n}{p} {A B C : Type} 
                -> (cA : Connected (S m) A)
                -> (cB : Connected (S n) B)
                -> (nC : NType p C)
                -> (ap : p <=tl (plus2 m n))
                   {a : A} {b : B}
                -> (fa : B -> C)
                -> (fb : A -> C)
                -> (agree : fa b ≃ fb a)
                -> (wedge-rec cA cB nC ap fa fb agree a ≃ fa)
    
      wedge-rec-βb : ∀ {m}{n}{p} {A B C : Type}
                -> (cA : Connected (S m) A)
                -> (cB : Connected (S n) B)
                -> (nC : NType p C)
                -> (ap : p <=tl (plus2 m n))
                   {a : A} {b : B}
                -> (fa : B -> C)
                -> (fb : A -> C)
                -> (agree : fa b ≃ fb a)
                -> (\ a' -> wedge-rec cA cB nC ap fa fb agree a' b) ≃ fb



{-
  module LeftBiased where
    wedge-rec : ∀ {A B C : Type} {a : A} {b : B}
              -> (fa : B -> C)
              -> (fb : A -> C)
              -> fa b ≃ fb a 
              -> A -> B -> C
    wedge-rec fa fb agree = λ _ b → fa b
  
    wedge-rec-βa : ∀ {A B C : Type} {a : A} {b : B}
              -> (fa : B -> C)
              -> (fb : A -> C)
              -> (agree : fa b ≃ fb a)
              -> (wedge-rec fa fb agree a ≃ fa)
    wedge-rec-βa fa fb agree = id
  
    wedge-rec-βb : ∀ n {A B C : Type} {a : A} {b : B}
                   (cA : Connected (S n) A)
                   (nC : NType (S n) C)
              -> (fa : B -> C)
              -> (fb : A -> C)
              -> (agree : fa b ≃ fb a)
              -> (\ a -> wedge-rec fa fb agree a b) ≃ fb
    wedge-rec-βb n {C = C}{a}{b} cA nC fa fb agree = 
      λ≃ (\ x -> ConnectedFib.everywhere n 
                 cA
                 (λ x → Path (fa b) (fb x) , use-level nC _ _)
                 agree
                 x)

    wedge-elim : ∀ n {A B : Type} (cA : Connected (S n) A) (C : A → B → NTypes n) {a : A} {b : B}
              -> (fa : (b' : B) -> fst (C a b'))
              -> (fb : (a' : A) -> fst (C a' b))
              -> fa b ≃ fb a 
              -> (a' : A) -> (b' : B) -> fst (C a' b')
    wedge-elim n cA C fa fb agree = λ a' b' → ConnectedFib.everywhere n cA (λ a'' → (C a'' b')) (fa b') a'

    wedge-elim-βa : ∀ n {A B : Type} (cA : Connected (S n) A) (C : A → B → NTypes n) {a : A} {b : B}
              -> (fa : (b' : B) -> fst (C a b'))
              -> (fb : (a' : A) -> fst (C a' b))
              -> (agree : fa b ≃ fb a)
              -> (wedge-elim n cA C fa fb agree a ≃ fa)
    wedge-elim-βa n cA C fa fb agree = λ≃ (\ b' -> ConnectedFib.everywhereβ n cA (λ a' → C a' b') (fa b'))

    wedge-elim-βb : ∀ n {A B : Type} (cA : Connected (S n) A) (C : A → B → NTypes n) {a : A} {b : B}
              -> (fa : (b' : B) -> fst (C a b'))
              -> (fb : (a' : A) -> fst (C a' b))
              -> (agree : fa b ≃ fb a)
              -> (\ a' -> wedge-elim n cA C fa fb agree a' b) ≃ fb
    wedge-elim-βb n cA C{a}{b} fa fb agree = 
      λ≃ (\ x -> ConnectedFib.everywhere n 
                 cA
                 (λ a' → Path (wedge-elim n cA C fa fb agree a' b) (fb a') , use-level (increment-level (snd (C a' b))) _ _)
                 (agree ∘ ConnectedFib.everywhereβ n cA (λ a' → C a' b) (fa b))
                 x)
  
-}

  postulate
    connected-Trunc : ∀ n k A -> Connected n A -> Connected n (Trunc k A)

