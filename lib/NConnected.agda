
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths 
open import lib.AdjointEquiv
open import lib.Functions
open import lib.Prods
open import lib.NType
open import lib.Universe
open import lib.Truncations
open import lib.Sums
open Truncation

module lib.NConnected where

  Connected : TLevel -> Type -> Type
  Connected n A = NType -2 (Trunc n A)

  abstract
    lower-Connected : ∀ {k1 k2} {A} → k1 <=tl k2 → Connected k2 A -> Connected k1 A
    lower-Connected {k1}{k2} lt = lower-Trunc-preserves-level k2 k1 { -2} lt

    connected-Trunc : ∀ n k A -> Connected n A -> Connected n (Trunc k A)
    connected-Trunc n k A cA = transport (NType -2) (! (FuseTrunc.path _ _ _)) (lower-Connected (mintl<=1 n k) cA)

    Connected-Path : ∀ {k} {A} → Connected (S k) A → { x y : A} → Connected k (Path x y)
    Connected-Path {k = k} cA = transport (NType -2) (! (TruncPath.path k)) (path-preserves-level cA)

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
   everywhere n {A}{a0} c P p0 = λ x → coe (! (ap fst (ap≃ lemma {x}))) p0
     where lemma1 : (Trunc-rec (NTypes-level n) (λ x' → P x')) ≃ (\ _ -> P a0)
           lemma1 = λ≃ (λ x → out-of-contractible (Trunc-rec (NTypes-level n) (λ x' → P x')) c x [ a0 ])
   
           lemma : P ≃ (\ _ -> P a0) 
           lemma = ap (λ f → f o ([_]{S n})) lemma1

   β : (n : TLevel) {A : Type} {a0 : A}
     -> (cA : Connected (S n) A)
     -> (P : A → NTypes n)
     -> (p0 : fst (P a0)) 
     -> everywhere n cA P p0 a0 ≃ p0
   β n {A}{a0} cA P p0 = ap (λ x → coe (! (ap fst x)) p0) cancel where
      cancel : (ap≃ (ap (λ f → f o ([_]{S n})) (λ≃ (λ x → out-of-contractible (Trunc-rec (NTypes-level n) (λ x' → P x')) cA x [ a0 ]))) {a0})
               ≃ id
      cancel = ap≃ (ap (λ f → f o [_] {S n}) (λ≃ (λ x → out-of-contractible (Trunc-rec (NTypes-level n) (λ x' → P x')) cA x [ a0 ]))) {a0} ≃〈 id 〉
               ap (\ f' -> f' a0) (ap (λ f → f o [_] {S n}) (λ≃ (λ x → out-of-contractible (Trunc-rec (NTypes-level n) (λ x' → P x')) cA x [ a0 ]))) ≃〈 ! (ap-o (λ f' → f' a0) (λ f → f o [_] {S n}) (λ≃ (λ x → out-of-contractible (Trunc-rec (NTypes-level n) (λ x' → P x')) cA x [ a0 ]))) 〉
               ap ((\ f' -> f' a0) o (λ f → f o [_] {S n})) (λ≃ (λ x → out-of-contractible (Trunc-rec (NTypes-level n) (λ x' → P x')) cA x [ a0 ])) ≃〈 id 〉
               ap (λ f → f [ a0 ]) (λ≃ (λ x → out-of-contractible (Trunc-rec (NTypes-level n) (λ x' → P x')) cA x [ a0 ])) ≃〈 Π≃β (λ x → out-of-contractible (Trunc-rec (NTypes-level n) (λ x' → P x')) cA x ([ a0 ])) {[ a0 ]} 〉
               (out-of-contractible (Trunc-rec (NTypes-level n) (λ x' → P x')) cA [ a0 ] [ a0 ]) ≃〈 out-of-contractible-id (Trunc-rec (NTypes-level n) (λ x' → P x')) cA [ a0 ] 〉
               id ∎ 
{-
  -- didn't end up needing these.  
  
   η : (n : TLevel) {A : Type} {a0 : A}
               -> (cA : Connected (S n) A)
               -> (P : A → NTypes n)
               -> (p0 : fst (P a0))
               -> (f : ((x : A) → fst (P x)))
               -> f a0 ≃ p0
               -> f ≃ everywhere n cA P p0
   η = ?

   ext : (n : TLevel) {A : Type} {a0 : A}
      -> (cA : Connected (S n) A)
      -> (P : A → NTypes n)
      -> (f g : ((x : A) → fst (P x)))
      -> f a0 ≃ g a0 
      -> f ≃ g
   ext n {a0 = a0} cA P f g on-a0 = ! (η n cA P (f a0) g (! on-a0)) ∘ η n cA P (f a0) f id

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

    abstract
      Extensions-level : ∀ {m n} {A : Type} (cA : Connected (S m) A)
                           (a0 : A) (C : A -> NTypes (plus2 n m)) (c0 : fst (C a0))
                       -> NType n (Extensions A a0 (fst o C) c0)
      Extensions-level {m}{ -2} cA a0 C c0 = 
       ntype ((ConnectedFib.everywhere m cA C c0 , ConnectedFib.β m cA C c0) ,
              (λ {(f , α) → pair≃ (λ≃ (ConnectedFib.everywhere m {_} {a0} cA 
                                       (λ a → Path (ConnectedFib.everywhere m cA C c0 a) (f a) , path-preserves-level (snd (C a)))
                                       (! α ∘ ConnectedFib.β m cA C c0)))
                            (transport (λ f' → f' a0 ≃ c0)
                               (λ≃
                                (ConnectedFib.everywhere m cA
                                 (λ a →
                                    Path (ConnectedFib.everywhere m cA C c0 a) (f a) ,
                                    path-preserves-level (snd (C a)))
                                 (! α ∘ ConnectedFib.β m cA C c0)))
                               (ConnectedFib.β m cA C c0) ≃〈 transport-Path-pre' (λ f' → f' a0) (λ≃ (ConnectedFib.everywhere m cA (λ a → Path (ConnectedFib.everywhere m cA C c0 a) (f a) , path-preserves-level (snd (C a))) (! α ∘ ConnectedFib.β m cA C c0))) (ConnectedFib.β m cA C c0) 〉
                             (ConnectedFib.β m cA C c0) ∘ 
                             ! (ap≃ (λ≃
                                (ConnectedFib.everywhere m cA
                                 (λ a →
                                    Path (ConnectedFib.everywhere m cA C c0 a) (f a) ,
                                    path-preserves-level (snd (C a)))
                                 (! α ∘ ConnectedFib.β m cA C c0))) {a0}) ≃〈 ap (λ x → ConnectedFib.β m cA C c0 ∘ ! x) (Π≃β (ConnectedFib.everywhere m cA (λ a → Path (ConnectedFib.everywhere m cA C c0 a) (f a) , path-preserves-level (snd (C a))) (! α ∘ ConnectedFib.β m cA C c0))) 〉 
                             (ConnectedFib.β m cA C c0) ∘ 
                             ! ((ConnectedFib.everywhere m cA
                                 (λ a →
                                    Path (ConnectedFib.everywhere m cA C c0 a) (f a) ,
                                    path-preserves-level (snd (C a)))
                                 (! α ∘ ConnectedFib.β m cA C c0)) a0) ≃〈 ap (λ x → ConnectedFib.β m cA C c0 ∘ ! x) (ConnectedFib.β m cA (λ a → Path (ConnectedFib.everywhere m cA C c0 a) (f a) , path-preserves-level (snd (C a))) (! α ∘ ConnectedFib.β m cA C c0)) 〉 
                             (ConnectedFib.β m cA C c0) ∘ 
                             ! (! α ∘ ConnectedFib.β m cA C c0) ≃〈 ap (_∘_ (ConnectedFib.β m cA C c0)) (!-∘ (! α) (ConnectedFib.β m cA C c0)) 〉 
                             (ConnectedFib.β m cA C c0) ∘ ! (ConnectedFib.β m cA C c0) ∘ ! (! α) ≃〈 !-inv-r-front (ConnectedFib.β m cA C c0) (! (! α)) 〉 
                             ! (! α) ≃〈 !-invol α 〉 
                             α ∎)}))
      Extensions-level {m}{S n} cA a0 C c0 =
        ntype (λ e1 e2 → transport (NType n) 
               (! (Extensions-Path (fst o C) c0 e1 e2))
               (Extensions-level {_} {n} cA a0 (\ a -> (Path (fst e1 a) (fst e2 a), use-level (snd (C a)) _ _)) 
                                               (! (snd e2) ∘ snd e1)))

    abstract
       wedge-elim' : ∀ {m n} {A B : Type} 
                      (cA : Connected (S m) A) 
                      (cB : Connected (S n) B)
                      (C : A → B → NTypes (plus2 m n)) 
                      {a0 : A} {b0 : B}
                   -> (fa0 : (b' : B) -> fst (C a0 b'))
                   -> (fb0 : (a' : A) -> fst (C a' b0))
                   -> fa0 b0 ≃ fb0 a0 
                   -> (a : A) -> Extensions B b0 (\ b -> fst (C a b)) (fb0 a)
       wedge-elim'{m}{n}{A}{B} cA cB C {a0}{b0} fa0 fb0 agree a = 
           (ConnectedFib.everywhere m {_} {a0} cA
            (λ a' → Extensions _ b0 (\ b -> fst (C a' b)) (fb0 a') , 
                    Extensions-level {n} {m} cB b0 (C a') (fb0 a')) 
            (fa0 , agree)
            a)

       wedge-elim : ∀ {m n p} {A B : Type} 
                      (cA : Connected (S m) A) 
                      (cB : Connected (S n) B)
                      (C : A → B → NTypes p) 
                      (app : p <=tl plus2 m n)
                      {a0 : A} {b0 : B}
                   -> (fa0 : (b : B) -> fst (C a0 b))
                   -> (fb0 : (a : A) -> fst (C a b0))
                   -> fa0 b0 ≃ fb0 a0 
                   -> (a : A) -> (b : B) -> fst (C a b)
       wedge-elim{m}{n}{p}{A}{B} cA cB C app fa0 fb0 agree a = 
         fst (wedge-elim' cA cB (λ a' b' → fst (C a' b') , raise-level app (snd (C a' b'))) fa0 fb0 agree a)

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
          fst≃
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
       wedge-elim-βb {m}{n}{p}{A}{B} cA cB C app{a0}{b0} fa0 fb0 agree =
        λ≃ (\ a -> snd (wedge-elim' cA cB (λ a b → fst (C a b) , raise-level app (snd (C a b))) fa0 fb0 agree a))

       wedge-elim-coh : ∀{m}{n}{p} {A B : Type}
                        (cA : Connected (S m) A) (cB : Connected (S n) B) (C : A → B → NTypes p) 
                        (app : p <=tl (plus2 m n)){a0 : A} {b0 : B}
                     -> (fa0 : (b : B) -> fst (C a0 b))
                     -> (fb0 : (a : A) -> fst (C a b0))
                     -> (agree : fa0 b0 ≃ fb0 a0)
                     ->   ap≃ (wedge-elim-βb cA cB C app fa0 fb0 agree) {a0}
                        ≃ agree ∘ ap≃ (wedge-elim-βa cA cB C app fa0 fb0 agree) {b0}
       wedge-elim-coh cA cB C app {a0}{b0} fa0 fb0 agree =
        let C' = (λ a b → fst (C a b) , raise-level app (snd (C a b))) 
        in 
         ap≃ (wedge-elim-βb cA cB C app fa0 fb0 agree) {a0} ≃〈 Π≃β (\ a -> snd (wedge-elim' cA cB (λ a b → fst (C a b) , raise-level app (snd (C a b))) fa0 fb0 agree a)) 〉
         snd (wedge-elim' cA cB (λ a b → fst (C a b) , raise-level app (snd (C a b))) fa0 fb0 agree a0) ≃〈 id 〉
         snd (ConnectedFib.everywhere _ {_} {a0} cA
               (λ a' → Extensions _ b0 (λ b → fst (C' a' b)) (fb0 a') ,
                       Extensions-level cB b0 (C' a') (fb0 a'))
               (fa0 , agree) a0) ≃〈 snd≃⁻
                                       (ConnectedFib.β _ cA
                                        (λ a' →
                                           Extensions _ _ (fst o C' a') (fb0 a') ,
                                           Extensions-level cB b0 (C' a') (fb0 a'))
                                        (fa0 , agree)) 〉 
         transport (λ f → f b0 ≃ fb0 a0)
           (! (wedge-elim-βa cA cB C app fa0 fb0 agree))
           agree ≃〈 transport-Path-pre' (λ f → f b0) (! (wedge-elim-βa cA cB C app fa0 fb0 agree)) agree 〉 
         agree ∘ ! (ap≃ (! (wedge-elim-βa cA cB C app fa0 fb0 agree)) {b0}) ≃〈 ap (_∘_ agree) (! (ap-! (λ f → f b0) (! (wedge-elim-βa cA cB C app fa0 fb0 agree)))) 〉 
         agree ∘ (ap≃ (! (! (wedge-elim-βa cA cB C app fa0 fb0 agree))) {b0}) ≃〈 ap (\ x -> agree ∘ ap≃ x {b0}) (!-invol (wedge-elim-βa cA cB C app fa0 fb0 agree)) 〉 
         (agree ∘ ap≃ (wedge-elim-βa cA cB C app fa0 fb0 agree) {b0} ∎)

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

       wedge-rec-coh : ∀{m}{n}{p} {A B C : Type}
                        (cA : Connected (S m) A) (cB : Connected (S n) B) (nC : NType p C) 
                        (app : p <=tl (plus2 m n)){a0 : A} {b0 : B}
                     -> (fa0 : B → C)
                     -> (fb0 : A → C)
                     -> (agree : fa0 b0 ≃ fb0 a0)
                     ->   ap≃ (wedge-rec-βb cA cB nC app fa0 fb0 agree) {a0}
                        ≃ agree ∘ ap≃ (wedge-rec-βa cA cB nC app fa0 fb0 agree) {b0}
       wedge-rec-coh cA cB nC = wedge-elim-coh cA cB (\ _ _ -> _ , nC)



