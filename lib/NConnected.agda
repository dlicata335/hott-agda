
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

  postulate
    plus2-comm : ∀ m n -> plus2 m n ≃ plus2 n m

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

   everywhere : (n : TLevel) {A : Type} {a0 : A}
             -> Connected (S n) A 
             -> (P : A → NTypes n)
             -> (fst (P a0)) → ((x : A) → fst (P x))
   everywhere n {A}{a0} c P p = λ x → coe (! (ap fst (ap≃ lemma))) p 
     where lemma1 : (Trunc-rec (NTypes-level n) (λ x' → P x')) ≃ (\ _ -> P a0)
           lemma1 = λ≃ (λ x → out-of-contractible (Trunc-rec (NTypes-level n) (λ x' → P x')) c x [ a0 ])
   
           lemma : P ≃ (\ _ -> P a0) 
           lemma = P ≃〈 id 〉
                   Trunc-rec (NTypes-level n) (λ x' → P x') o [_] ≃〈 ap (λ f → f o ([_]{S n})) lemma1 〉
                   (\ _ -> P a0) o ([_]{S n}) ≃〈 id 〉
                   ((λ _ → P a0) ∎)
   postulate
     β : (n : TLevel) {A : Type} {a0 : A}
               -> (cA : Connected (S n) A)
               -> (P : A → NTypes n)
               -> (p0 : fst (P a0)) 
               -> everywhere n cA P p0 a0 ≃ p0

     η : (n : TLevel) {A : Type} {a0 : A}
               -> (cA : Connected (S n) A)
               -> (P : A → NTypes n)
               -> (p0 : fst (P a0))
               -> (f : ((x : A) → fst (P x)))
               -> f a0 ≃ p0
               -> f ≃ everywhere n cA P p0

   ext : (n : TLevel) {A : Type} {a0 : A}
      -> (cA : Connected (S n) A)
      -> (P : A → NTypes n)
      -> (f g : ((x : A) → fst (P x)))
      -> f a0 ≃ g a0 
      -> f ≃ g
   ext n {a0 = a0} cA P f g on-a0 = ! (η n cA P (f a0) g (! on-a0)) ∘ η n cA P (f a0) f id
        
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
     ntype ((ConnectedFib.everywhere m cA C c0 , ConnectedFib.β m cA C c0) ,
           (λ {(f , α) → pair≃ (λ≃ 
             (ConnectedFib.everywhere 
                m {_} {a0} cA 
                (λ a → Path (ConnectedFib.everywhere m cA C c0 a) (f a) , path-preserves-level (snd (C a)))
                (! α ∘ ConnectedFib.β m cA C c0)))
             FIXME})) where
     postulate FIXME : ∀ {A} -> A
    Extensions-level {m}{S n} cA a0 C c0 =
      ntype (λ e1 e2 → transport (NType n) 
             (! (Extensions-Path (fst o C) c0 e1 e2))
             (Extensions-level {_} {n} cA a0 (\ a -> (Path (fst e1 a) (fst e2 a), use-level (snd (C a)) _ _)) 
                                             (! (snd e2) ∘ snd e1)))

    abstract
       wedge-elim1' : ∀ {m n} {A B : Type} 
                      (cA : Connected (S m) A) 
                      (cB : Connected (S n) B)
                      (C : A → B → NTypes (plus2 m n)) 
                      {a0 : A} {b0 : B}
                   -> (fa0 : (b' : B) -> fst (C a0 b'))
                   -> (fb0 : (a' : A) -> fst (C a' b0))
                   -> fa0 b0 ≃ fb0 a0 
                   -> (a' : A) -> Extensions _ b0 (fst o (C a')) (fb0 a')
       wedge-elim1'{m}{n}{A}{B} cA cB C {a0}{b0} fa0 fb0 agree a = 
           (ConnectedFib.everywhere m {_} {a0} cA
            (λ a' → Extensions _ _ (fst o (C a')) (fb0 a') , 
                    Extensions-level {n} {m} cB b0 (C a') (fb0 a')) 
            (fa0 , agree)
            a)

{-
       wedge-elim2' : ∀ {m n} {A B : Type} 
                      (cA : Connected (S m) A) 
                      (cB : Connected (S n) B)
                      (C : A → B → NTypes (plus2 m n)) 
                      {a0 : A} {b0 : B}
                   -> (fa0 : (b' : B) -> fst (C a0 b'))
                   -> (fb0 : (a' : A) -> fst (C a' b0))
                   -> fa0 b0 ≃ fb0 a0 
                   -> (b' : B) -> Extensions _ a0 (\a' -> fst (C a' b')) (fa0 b')
       wedge-elim2'{m}{n}{A}{B} cA cB C {a0}{b0} fa0 fb0 agree b = 
           (ConnectedFib.everywhere n {_} {b0} cB
            (λ b' → Extensions _ _ (\a' -> fst (C a' b')) (fa0 b') , 
                    Extensions-level {m} {n} cA a0 (\ a' -> fst (C a' b') , transport (λ x → NType x (fst (C a' b'))) (plus2-comm m n) (snd (C a' b'))) (fa0 b')) 
            (fb0 , ! agree)
            b)
-}
       
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
       wedge-elim{m}{n}{p}{A}{B} cA cB C app fa0 fb0 agree a' = 
         fst (wedge-elim1' cA cB (λ a b → fst (C a b) , raise-level app (snd (C a b))) fa0 fb0 agree a')

{-
       wedge-elim2 : ∀ {m n p} {A B : Type} 
                      (cA : Connected (S m) A) 
                      (cB : Connected (S n) B)
                      (C : A → B → NTypes p) 
                      (app : p <=tl plus2 m n)
                      {a0 : A} {b0 : B}
                   -> (fa0 : (b' : B) -> fst (C a0 b'))
                   -> (fb0 : (a' : A) -> fst (C a' b0))
                   -> fa0 b0 ≃ fb0 a0 
                   -> (a' : A) -> (b' : B) -> fst (C a' b')
       wedge-elim2{m}{n}{p}{A}{B} cA cB C app fa0 fb0 agree a' b' = 
         fst (wedge-elim2' cA cB (λ a b → fst (C a b) , raise-level app (snd (C a b))) fa0 fb0 agree b') a'

       
       same : ∀ {m n p} {A B : Type} 
                      (cA : Connected (S m) A) 
                      (cB : Connected (S n) B)
                      (C : A → B → NTypes p) 
                      (app : p <=tl plus2 m n)
                      {a0 : A} {b0 : B}
                   -> (fa0 : (b' : B) -> fst (C a0 b'))
                   -> (fb0 : (a' : A) -> fst (C a' b0))
                   -> (agree : fa0 b0 ≃ fb0 a0)
                   -> (a' : A) -> (b' : B) -> (wedge-elim cA cB C app fa0 fb0 agree a' b')
                                            ≃ (wedge-elim2 cA cB C app fa0 fb0 agree a' b')
       same {m}{n}{p} cA cB C app {a0}{b0} fa0 fb0 agree a' b' =
         wedge-elim {m} {n} {p} cA cB
           (λ a b →
              wedge-elim cA cB C app fa0 fb0 agree a b ≃
              wedge-elim2 cA cB C app fa0 fb0 agree a b
              , {!!})
           app{a0}{b0} {!!} {!!} {!!} a' b'
-}       
      
       wedge-elim-βa : ∀{m}{n}{p} {A B : Type}
                        (cA : Connected (S m) A) (cB : Connected (S n) B) (C : A → B → NTypes p) 
                        (app : p <=tl (plus2 m n)){a0 : A} {b0 : B}
                     -> (fa0 : (b : B) -> fst (C a0 b))
                     -> (fb0 : (a : A) -> fst (C a b0))
                     -> (agree : fa0 b0 ≃ fb0 a0)
                     -> (wedge-elim cA cB C app fa0 fb0 agree a0 ≃ fa0)
       wedge-elim-βa{m}{n}{p} cA cB C app{a0}{b0} fa0 fb0 agree = 
        let C = (λ a b → fst (C a b) , raise-level app (snd (C a b))) 
        in 
          ap fst
          (ConnectedFib.β m cA
           (λ a' →
              Extensions _ _ (fst o C a') (fb0 a') ,
              Extensions-level {n} {m} cB b0 (C a') (fb0 a'))
           (fa0 , agree))
         
       wedge-elim-βb : ∀{m}{n}{p} {A B : Type}
                        (cA : Connected (S m) A) (cB : Connected (S n) B) (C : A → B → NTypes p) 
                        (app : p <=tl (plus2 m n)){a0 : A} {b0 : B}
                     -> (fa0 : (b : B) -> fst (C a0 b))
                     -> (fb0 : (a : A) -> fst (C a b0))
                     -> (agree : fa0 b0 ≃ fb0 a0)
                     -> (\ a -> wedge-elim cA cB C app fa0 fb0 agree a b0) ≃ fb0
       wedge-elim-βb {m}{n}{p} cA cB C app{a0}{b0} fa0 fb0 agree = 
        let C = (λ a b → fst (C a b) , raise-level app (snd (C a b))) 
        in 
         λ≃ (\ a -> 
                ap≃
                (fst≃
                 (ConnectedFib.everywhere m {a0 = a0} cA
                  (λ a' →
                     ConnectedFib.everywhere m {_} {a0} cA
                     (λ a1 →
                        Extensions _ _ (fst o C a1) (fb0 a1) ,
                        Extensions-level {n} {m} cB b0 (C a1) (fb0 a1))
                     (fa0 , agree) a'
                     ≃ {!fb0!}
                     , {!!})
                  {!!} a)))
--                                       (agree ∘ ap≃ (wedge-elim-βa cA cB C app fa0 fb0 agree)))

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
       wedge-rec-βa cA cB nC = wedge-elim-βa cA cB (\ _ _ -> _ , nC)
      
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
       wedge-rec-βb cA cB nC = wedge-elim-βb cA cB (\ _ _ -> _ , nC)



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

