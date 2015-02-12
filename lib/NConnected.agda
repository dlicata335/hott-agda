
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
open import lib.HFiber
open import lib.cubical.PathOver
open import lib.cubical.Square
open Truncation

module lib.NConnected where

  Connected : TLevel -> Type -> Type
  Connected n A = NType -2 (Trunc n A)

  ConnectedMap : (n : TLevel) → ∀ {A B} → (f : A → B) → Type
  ConnectedMap n {A}{B} f = (y : B) → Connected n (HFiber f y)

  module Connected where 

   lower : ∀ {k1 k2} {A} → k1 <=tl k2 → Connected k2 A -> Connected k1 A
   lower {k1}{k2} lt = lower-Trunc-preserves-level k2 k1 { -2} lt

   Trunc-connected : ∀ n k A -> Connected n A -> Connected n (Trunc k A)
   Trunc-connected n k A cA = transport (NType -2) (! (FuseTrunc.path _ _ _)) (lower (mintl<=1 n k) cA)

   Path-connected : ∀ {k} {A} → Connected (S k) A → { x y : A} → Connected k (Path x y)
   Path-connected {k = k} cA = transport (NType -2) (! (TruncPath.path k)) (path-preserves-level cA)

   level : ∀ {k A} → HProp (Connected k A)
   level = NType-is-HProp _

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
     where lemma1 : Trunc-rec (NTypes-level n) (λ x' → P x') ≃ (\ _ -> P a0)
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

   contractible-implies-connected : ∀ {n} {A : Type} → Contractible A → Connected n A
   contractible-implies-connected cA = ntype ([ fst cA ] , (Trunc-elim _ (λ _ → path-preserves-level Trunc-level) (λ x → ap [_] (snd cA x))))

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

  module ConnectedMap where
    UMP : (n : TLevel) → ∀ {A B} → (f : A → B) → Type
    UMP n {A}{B} f =  (P : B → NTypes n)
                               -> (b : (x : A) → fst (P (f x)))
                               → Σ \(extend : ((y : B) → fst (P y))) -> 
                                    (x : A) → extend (f x) ≃ b x 

    extend : (n : TLevel) {A : Type} {B : Type} (f : A → B)
             -> ConnectedMap n f 
             -> (P : B → NTypes n)
             -> ((x : A) → fst (P (f x)))
             → ((y : B) → fst (P y))
    extend n f cf P forA y = Trunc-rec (snd (P y))
                                       (λ hfy → transport (fst o P) (snd hfy) (forA (fst hfy)))
                                       (fst (use-level (cf y)))

    extendβ : (n : TLevel) → ∀ {A B} (f : A → B) →
              (cf : ConnectedMap n f) →
              (P : B → NTypes n)
            -> (b : (x : A) → fst (P (f x)))
            →  (x : A) → extend n f cf P b (f x) ≃ b x 
    extendβ n f cF P b x = ap (Trunc-rec (snd (P _)) (λ hfy → transport (fst o P) (snd hfy) (b (fst hfy)))) (snd (use-level (cF (f x))) [ x , id ])

    has-UMP : (n : TLevel) {A B : Type} (f : A → B) →
               ConnectedMap n f → UMP n f 
    has-UMP n f cf P b = (extend n f cf P b , extendβ n f cf P b)

    from-UMP : (n : TLevel) {A B : Type} (f : A → B) →
                            UMP n f → ConnectedMap n f 
    from-UMP n f ext b = 
      let elm = (ext (λ b' → Trunc n (HFiber f b') , Trunc-level) (λ a → [ a , id ]))
       in ntype ((fst elm b) , 
                  Trunc-elim _ (λ _ → path-preserves-level Trunc-level) 
                               (fst (ext (λ b' → ((x : HFiber f b') → fst elm b' ≃ [ x ]) , Πlevel (λ _ → path-preserves-level Trunc-level)) 
                                         (λ a → (λ {(a' , p) → 
                                                ((ap [_] (ap≃ (transport-HFiber-arg f p)) 
                                                  ∘ transport-Trunc' (HFiber f) p [ a' , id ])
                                                  ∘ ap (transport (λ z → Trunc n (HFiber f z)) p) (snd elm a')
                                                  ∘ ! (apd (fst elm) p))})))
                                    b))

    trunc-equiv : (n : TLevel) → ∀ {A B} → (f : A → B) → ConnectedMap n f → Equiv (Trunc n A) (Trunc n B)
    trunc-equiv n f cf = 
      improve (hequiv (Trunc-func f) 
                      (Trunc-rec Trunc-level (λ y → Trunc-func fst (fst (use-level (cf y)))))
                      (Trunc-elim _ (λ _ → path-preserves-level Trunc-level)
                        (λ x → ap (Trunc-func fst) (snd (use-level (cf (f x))) [ x , id ])))
                      (Trunc-elim _ (λ _ → path-preserves-level Trunc-level)
                        (λ y → split-Trunc-dep1 n (λ tx → Trunc-func f tx ≃ [ y ]) (λ _ → path-preserves-level Trunc-level)
                                   (λ _ → λ p → ap [_] p)
                                   (fst (use-level (cf y)))))) where
           split-Trunc-dep1 : ∀ n {A} {B : A → Type} (P : Trunc n A → Type) (nP : (x : _) → NType n (P x))
                     → ((x : A) (y : B x) → P [ x ])
                     → (p : Trunc n (Σ B)) → P (Trunc-func fst p)
           split-Trunc-dep1 n P nP branch = Trunc-elim _ (λ _ → nP _) (λ {(a , b) → branch a b})


    fiberwise-to-total-connected : (n : TLevel) → ∀ {A} {B1 B2 : A → Type} → (f : (x : A) → B1 x → B2 x) → 
                                 ((x : A) → ConnectedMap n (f x)) → ConnectedMap n (fiberwise-to-total f)
    fiberwise-to-total-connected n {_}{B1} f c = from-UMP n (fiberwise-to-total f) 
                                                                         (λ P b → (λ y → fst
                                                                                           (has-UMP n (f (fst y)) (c (fst y))
                                                                                            (λ z → P (fst y , z)) (λ b1 → b (fst y , b1)))
                                                                                           (snd y)) , 
                                                                         (λ y → snd
                                                                                  (has-UMP n (f (fst y)) (c (fst y))
                                                                                   (λ z → P (fst y , z)) (λ b1 → b (fst y , b1)))
                                                                                  (snd y))) 

    level : ∀ {n A B} (f : A → B) → HProp (ConnectedMap n f)
    level f = Πlevel (\ _ -> Connected.level)

    -- FIXME: IsWeq to IsEquiv doesn't compute very well... 
    equiv-connected : ∀ {n} {A B : Type} (e : Equiv A B) → ConnectedMap n (fst e)
    equiv-connected e = λ b → Connected.contractible-implies-connected (coe (! (IsWeq≃IsEquiv (fst e))) (snd e) b)

    compose : ∀ {n} {A B C : Type} {g : B → C} {f : A → B} → ConnectedMap n g → ConnectedMap n f → ConnectedMap n (g o f)
    compose {g = g} {f} cg cf = λ c → ntype ((Trunc-rec Trunc-level 
                                        (λ hg → Trunc-rec Trunc-level (λ hf → [ fst hf , snd hg ∘ ap g (snd hf) ])
                                                 (fst (use-level (cf (fst hg)))))
                                        (fst (use-level (cg c)))) , 
                                      Trunc-elim _ (λ _ → path-preserves-level Trunc-level) 
                                        (λ hgf → ( ap (Trunc-rec Trunc-level (λ hf → [ fst hf , snd hgf ∘ ap g (snd hf) ])) (snd (use-level (cf (f (fst hgf)))) [ fst hgf , id ])) ∘
                                                   ap (Trunc-rec Trunc-level (λ hg → Trunc-rec Trunc-level (λ hf → [ fst hf , snd hg ∘ ap g (snd hf) ]) (fst (use-level (cf (fst hg))))))
                                                      (snd (use-level (cg c)) [ f (fst hgf) , snd hgf ])))

    -- need HFiber fst y == B(y)
    connected-fibers≃connected-first : ∀ {n A} {B : A → Type} → ((x : A) → Connected n (B x)) == ConnectedMap n (\ (p : Σ B) -> fst p)
    connected-fibers≃connected-first = ua (improve (hequiv 
                                             (λ cB → λ a → transport (λ X → NType -2 (Trunc _ X)) (hfiber-fst a) (cB a))
                                             (λ cB → λ a → transport (λ X → NType -2 (Trunc _ X)) (!  (hfiber-fst a)) (cB a))
                                             (λ _ → HProp-unique (Πlevel (λ _ → Connected.level)) _ _)
                                             (λ _ → HProp-unique (level _) _ _)))

    postcompose-equiv-connected : ∀ {n A B B'} {f : A → B} (e : Equiv B B') → ConnectedMap n f → ConnectedMap n (fst e o f)
    postcompose-equiv-connected e cf = compose (equiv-connected e) cf

    precompose-equiv-connected : ∀ {n A A' B} {f : A → B} (e : Equiv A' A) → ConnectedMap n f → ConnectedMap n (f o fst e)
    precompose-equiv-connected e cf = compose cf (equiv-connected e)

    -- FIXME might want a version that reduces
    connected-if-precompose-equiv-connected : ∀ {n A A' B} {f : A → B} (e : Equiv A' A) → ConnectedMap n (f o fst e) → ConnectedMap n f
    connected-if-precompose-equiv-connected {f = f} e ccomp = 
      transport (ConnectedMap _) (λ≃ (λ x → ap f (IsEquiv.β (snd e) x))) (precompose-equiv-connected (!equiv e) ccomp)

    -- connected-if-postcompose-equiv-connected : ∀ {n A B B'} (f : A → B) (e : Equiv B B') → ConnectedMap n (fst e o f) → ConnectedMap n f

    connected-type≃connected-map-to-point : ∀ {n A} → (Connected n A) == (ConnectedMap n (\ (_ : A) → <>))
    connected-type≃connected-map-to-point = ua (improve (hequiv (λ x y → transport (λ A → NType -2 (Trunc _ A)) (! (ua HFiber-of-map-to-point)) x)
                                             (λ x → transport (λ A → NType -2 (Trunc _ A)) (ua HFiber-of-map-to-point) (x <>))
                                             (λ _ → HProp-unique (Connected.level) _ _) (λ _ → HProp-unique (level _) _ _)))

    ConnectiveMap : ∀ {n A B} → -1 <=tl n → (A → B) → Type
    ConnectiveMap le f = ConnectedMap (fst (sub1 _ le)) f

    connected-type≃connected-map-from-point : ∀ {n A} (a : A) → Connected (S n) A == ConnectedMap n {Unit} (\ _ -> a)
    connected-type≃connected-map-from-point {n} a = ua (improve (hequiv (λ cA → from-UMP n (λ v → a) 
                                                                              (λ P b → Connected.everywhere n {a0 = a} cA P (b <>) , (λ _ → Connected.β n cA P (b <>))))
                                                                      (λ cf → ntype ([ a ] , Trunc-elim _ (λ _ → path-preserves-level Trunc-level) (λ x → fst
                                                                                                                                                            (use-level
                                                                                                                                                             (transport (NType -2) (TruncPath.path n)
                                                                                                                                                              (transport (λ X → NType -2 (Trunc n X))
                                                                                                                                                               (ua HFiber-of-map-from-point) (cf x))))))
                                                                      ) 
                                                                      (λ _ → HProp-unique Connected.level _ _)
                                                                      (λ _ → HProp-unique (level _) _ _)))

    fiber-top-equiv : ∀ {i A A' B} (f : A → A') (g : A → B) (h : A' → B)
                                 → ((x : A) → (h o f) x == g x)
                                 → ConnectedMap i f 
                                 → {b : B} → Equiv (Trunc i (HFiber g b)) (Trunc i (HFiber h b))  
    fiber-top-equiv {i} f g h tri cf {b} = 
      improve (hequiv map1 map2 comp1 comp2) where
       map1 : (Trunc i (HFiber g b)) → (Trunc i (HFiber h b))  
       map1 = (Trunc-rec Trunc-level (λ hg → [ f (fst hg) , snd hg ∘ tri _ ]))

       map2 : (Trunc i (HFiber h b)) → (Trunc i (HFiber g b)) 
       map2 = (Trunc-rec Trunc-level (λ hh → Trunc-rec Trunc-level (λ hf → [ fst hf , snd hh ∘ ap h (snd hf) ∘ ! (tri _) ]) (fst (use-level (cf (fst hh))))))
       abstract
          coh1 : {A : Type} {a a' : A} (α : a == a') → ((id ∘ α) ∘ id ∘ ! α) == id
          coh1 id = id

          coh2 : {A : Type} {a a' a'' : A} {α : a == a'} {β : a == a''} → (id ∘ β ∘ ! α) ∘ α == β
          coh2 {α = id} {β = id} = id

          lemma : ∀ {a' : _} → Path {Trunc _ (HFiber h (h a'))} (Trunc-rec Trunc-level (λ hf₁ → [ f (fst hf₁) , ap h (snd hf₁) ]) (fst (use-level (cf a')))) [ a' , id ]
          lemma {a'} = Trunc-elim
                             (λ Z₁ → Trunc-rec Trunc-level (λ hf₁ → [ f (fst hf₁) , ap h (snd hf₁) ]) Z₁ == [ a' , id ])
                             (λ _ → path-preserves-level Trunc-level)
                             (λ x → ap [_] (pair= (snd x) (PathOver=.in-PathOver-= (whisker-square id id (! (ap-constant _ (snd x))) id connection2))))
                             (fst (use-level (cf a')))

          comp1 : (x : _) → Path (map2 (map1 x)) x
          comp1 = (Trunc-elim _ (λ _ → path-preserves-level Trunc-level) 
                                    (λ hg → path-induction (λ b sndhg → Path (Trunc-rec Trunc-level (λ hf → [ fst hf , (sndhg ∘ tri _) ∘ ap h (snd hf) ∘ ! (tri _) ]) (fst (use-level (cf (f (fst hg)))))) [ fst hg , sndhg ]) 
                                              (ap (λ z → [ fst hg , z ]) (coh1 (tri _)) ∘
                                               ap (Trunc-rec Trunc-level (λ hf → [ fst hf , (id ∘ tri _) ∘ ap h (snd hf) ∘ ! (tri _) ])) (snd (use-level (cf (f (fst hg)))) [ fst hg , id ])) 
                                              (snd hg)))
          comp2 : (y : _) → Path (map1 (map2 y)) y
          comp2 =  -- weird that this side never uses snd (cf ...)
                   (Trunc-elim _ (λ _ → path-preserves-level Trunc-level) 
                                    (λ hf → path-induction
                                              (λ b sndhf → Path (Trunc-rec Trunc-level (λ hg → [ f (fst hg) , snd hg ∘ tri _ ]) (Trunc-rec Trunc-level (λ hf₁ → [ fst hf₁ , sndhf ∘ ap h (snd hf₁) ∘ ! (tri _) ]) (fst (use-level (cf (fst hf)))))) [ fst hf , sndhf ])
                                              ( lemma {a' = fst hf} ∘ ap (λ Z₁ → Trunc-rec Trunc-level Z₁ (fst (use-level (cf (fst hf))))) (λ≃ (λ x → ap (λ Z₁ → [ f (fst x) , Z₁ ]) (coh2 {α = tri _} {β = ap h (snd x)}))) ∘ Trunc-rec-cconv _ Trunc-level (λ hf₁ → [ fst hf₁ , id ∘ ap h (snd hf₁) ∘ ! (tri _) ]) (λ hg → [ f (fst hg) , snd hg ∘ tri _ ]) (fst (use-level (cf (fst hf)))))
                                              (snd hf)))

  {- -- should be a special case of the above if we ever want it.  ended up not using it.
    unfiberwise-to-total-connected : (n : TLevel) → ∀ {A} {B1 B2 : A → Type} → (f : (x : A) → B1 x → B2 x) → 
                                 ConnectedMap n (fiberwise-to-total f) → ((x : A) → ConnectedMap n (f x))
  -}

  module Extensions where

    Extensions : (A : Type) (a0 : A) (C : A -> Type) (c0 : C a0) -> Type
    Extensions A a0 C c0 = Σ (λ (f : (a : A) → (C a)) → f a0 ≃ c0)
    
    path : {A : Type} {a0 : A} (C : A -> Type) (c0 : C a0) 
                    (e1 e2 : Extensions A a0 C c0)
                    -> Path{(Extensions A a0 C c0)} e1 e2
                     ≃ Extensions A a0 (\ a -> Path{(C a)} (fst e1 a) (fst e2 a)) 
                                       (! (snd e2) ∘ snd e1)
    path {A}{a0}C c0 (f1 , α1) (f2 , α2) = 
      Path (f1 , α1) (f2 , α2)  ≃〈 ! ΣPath.path 〉 
      Σ (λ α → Path (transport (λ f → f a0 ≃ c0) α α1) α2) ≃〈 apΣ' (!equiv ΠPath.eqv) (λ _ → id) 〉 
      Σ (λ (h : (x : A) → Path (f1 x) (f2 x)) →
           Path (transport (λ f → f a0 ≃ c0) (λ≃ h) α1) α2) ≃〈 ap (λ B → Σ B) (λ≃ (λ h → ap (BackPath _) (ap (λ x → α1 ∘ ! x) (Π≃β h) ∘ transport-Path-pre' (λ f → f a0) (λ≃ h) α1))) 〉 
      Σ (λ (h : (x : A) → Path (f1 x) (f2 x)) →
           Path (α1 ∘ ! (h a0)) α2) ≃〈 ap (λ B → Σ B) (λ≃ (λ h → flip≃ ∘ flip-triangle≃ α1 α2 (h a0))) 〉 
      Σ (\ h -> h a0 ≃ ! α2 ∘ α1) ≃〈 id 〉 
      Extensions A a0 (λ a → Path (f1 a) (f2 a)) (! α2 ∘ α1) ∎

    abstract
      level : ∀ {m n} {A : Type} (cA : Connected (S m) A)
                           (a0 : A) (C : A -> NTypes (plus2 n m)) (c0 : fst (C a0))
                       -> NType n (Extensions A a0 (fst o C) c0)
      level {m}{ -2} cA a0 C c0 = 
       ntype ((Connected.everywhere m cA C c0 , Connected.β m cA C c0) ,
              (λ {(f , α) → pair≃ (λ≃ (Connected.everywhere m {_} {a0} cA 
                                       (λ a → Path (Connected.everywhere m cA C c0 a) (f a) , path-preserves-level (snd (C a)))
                                       (! α ∘ Connected.β m cA C c0)))
                            (transport (λ f' → f' a0 ≃ c0)
                               (λ≃
                                (Connected.everywhere m cA
                                 (λ a →
                                    Path (Connected.everywhere m cA C c0 a) (f a) ,
                                    path-preserves-level (snd (C a)))
                                 (! α ∘ Connected.β m cA C c0)))
                               (Connected.β m cA C c0) ≃〈 transport-Path-pre' (λ f' → f' a0) (λ≃ (Connected.everywhere m cA (λ a → Path (Connected.everywhere m cA C c0 a) (f a) , path-preserves-level (snd (C a))) (! α ∘ Connected.β m cA C c0))) (Connected.β m cA C c0) 〉
                             (Connected.β m cA C c0) ∘ 
                             ! (ap≃ (λ≃
                                (Connected.everywhere m cA
                                 (λ a →
                                    Path (Connected.everywhere m cA C c0 a) (f a) ,
                                    path-preserves-level (snd (C a)))
                                 (! α ∘ Connected.β m cA C c0))) {a0}) ≃〈 ap (λ x → Connected.β m cA C c0 ∘ ! x) (Π≃β (Connected.everywhere m cA (λ a → Path (Connected.everywhere m cA C c0 a) (f a) , path-preserves-level (snd (C a))) (! α ∘ Connected.β m cA C c0))) 〉 
                             (Connected.β m cA C c0) ∘ 
                             ! ((Connected.everywhere m cA
                                 (λ a →
                                    Path (Connected.everywhere m cA C c0 a) (f a) ,
                                    path-preserves-level (snd (C a)))
                                 (! α ∘ Connected.β m cA C c0)) a0) ≃〈 ap (λ x → Connected.β m cA C c0 ∘ ! x) (Connected.β m cA (λ a → Path (Connected.everywhere m cA C c0 a) (f a) , path-preserves-level (snd (C a))) (! α ∘ Connected.β m cA C c0)) 〉 
                             (Connected.β m cA C c0) ∘ 
                             ! (! α ∘ Connected.β m cA C c0) ≃〈 ap (_∘_ (Connected.β m cA C c0)) (!-∘ (! α) (Connected.β m cA C c0)) 〉 
                             (Connected.β m cA C c0) ∘ ! (Connected.β m cA C c0) ∘ ! (! α) ≃〈 !-inv-r-front (Connected.β m cA C c0) (! (! α)) 〉 
                             ! (! α) ≃〈 !-invol α 〉 
                             α ∎)}))
      level {m}{S n} cA a0 C c0 =
        ntype (λ e1 e2 → transport (NType n) 
               (! (path (fst o C) c0 e1 e2))
               (level {_} {n} cA a0 (\ a -> (Path (fst e1 a) (fst e2 a), use-level (snd (C a)) _ _)) 
                                               (! (snd e2) ∘ snd e1)))

    Extensions-ntype : ∀ {m n} {A : Type} (cA : Connected (S m) A)
                       (a0 : A) (C : A -> NTypes (plus2 n m)) (c0 : fst (C a0))
                     → NTypes n 
    Extensions-ntype {_}{_} {A} cA a0 C c0 = ((Extensions A a0 (fst o C) c0) , level cA a0 C c0)

  module ConnectedProduct where

    abstract
       wedge-elim' : ∀ {m n} {A B : Type} 
                      (cA : Connected (S m) A) 
                      (cB : Connected (S n) B)
                      (C : A → B → NTypes (plus2 m n)) 
                      {a0 : A} {b0 : B}
                   -> (fa0 : (b' : B) -> fst (C a0 b'))
                   -> (fb0 : (a' : A) -> fst (C a' b0))
                   -> fa0 b0 ≃ fb0 a0 
                   -> (a : A) -> Extensions.Extensions B b0 (\ b -> fst (C a b)) (fb0 a)
       wedge-elim'{m}{n}{A}{B} cA cB C {a0}{b0} fa0 fb0 agree a = 
           (Connected.everywhere m {_} {a0} cA
            (λ a' → Extensions.Extensions _ b0 (\ b -> fst (C a' b)) (fb0 a') , 
                    Extensions.level {n} {m} cB b0 (C a') (fb0 a')) 
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
          (Connected.β m cA
           (λ a' →
              Extensions.Extensions _ _ (fst o C a') (fb0 a') ,
              Extensions.level {n} {m} cB b0 (C a') (fb0 a'))
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
         snd (Connected.everywhere _ {_} {a0} cA
               (λ a' → Extensions.Extensions _ b0 (λ b → fst (C' a' b)) (fb0 a') ,
                       Extensions.level cB b0 (C' a') (fb0 a'))
               (fa0 , agree) a0) ≃〈 snd≃⁻
                                       (Connected.β _ cA
                                        (λ a' →
                                           Extensions.Extensions _ _ (fst o C' a') (fb0 a') ,
                                           Extensions.level cB b0 (C' a') (fb0 a'))
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

  module ConnectedSigma where

    abstract
       wedge-elim' : ∀ {m n} {A : Type} {B : A → Type}
                      (cA : Connected (S m) A) 
                      (cB : (a : A) → Connected (S n) (B a))
                      (C : (a : A) → (B a) → NTypes (plus2 m n)) 
                      {a0 : A} {b0 : (a : A) → B a}
                   -> (fa0 : (b' : B a0) -> fst (C a0 b'))
                   -> (fb0 : (a' : A) -> fst (C a' (b0 a')))
                   -> fa0 (b0 a0) ≃ fb0 a0 
                   -> (a : A) -> Extensions.Extensions (B a) (b0 a) (\ b -> fst (C a b)) (fb0 a)
       wedge-elim'{m}{n}{A}{B} cA cB C {a0}{b0} fa0 fb0 agree a = 
           (Connected.everywhere m {_} {a0} cA
            (λ a' → Extensions.Extensions _ (b0 a') (\ b -> fst (C a' b)) (fb0 a') , 
                    Extensions.level {n} {m} (cB a') (b0 a') (C a') (fb0 a')) 
            (fa0 , agree)
            a)

       wedge-elim : ∀ {m n p} {A : Type} {B : A → Type}
                      (cA : Connected (S m) A) 
                      (cB : (a : A) → Connected (S n) (B a))
                      (C : (a : A) → (B a) → NTypes p) 
                      (app : p <=tl plus2 m n)
                      {a0 : A} {b0 : (a : A) → B a}
                   -> (fa0 : (b' : B a0) -> fst (C a0 b'))
                   -> (fb0 : (a' : A) -> fst (C a' (b0 a')))
                   -> (agree : fa0 (b0 a0) ≃ fb0 a0)
                   -> (a : A) -> (b : (B a)) -> fst (C a b)
       wedge-elim{m}{n}{p}{A}{B} cA cB C app fa0 fb0 agree a = 
         fst (wedge-elim' cA cB (λ a' b' → fst (C a' b') , raise-level app (snd (C a' b'))) fa0 fb0 agree a)

       wedge-elim-βa : ∀ {m n p} {A : Type} {B : A → Type}
                      (cA : Connected (S m) A) 
                      (cB : (a : A) → Connected (S n) (B a))
                      (C : (a : A) → (B a) → NTypes p) 
                      (app : p <=tl plus2 m n)
                      {a0 : A} {b0 : (a : A) → B a}
                   -> (fa0 : (b' : B a0) -> fst (C a0 b'))
                   -> (fb0 : (a' : A) -> fst (C a' (b0 a')))
                   -> (agree : fa0 (b0 a0) ≃ fb0 a0)
                   -> (wedge-elim cA cB C app fa0 fb0 agree a0 ≃ fa0)
       wedge-elim-βa{m}{n}{p} cA cB C app{a0}{b0} fa0 fb0 agree = 
        let C = (λ a b → fst (C a b) , raise-level app (snd (C a b))) 
        in 
          fst≃
          (Connected.β m cA
           (λ a' →
              Extensions.Extensions _ _ (fst o C a') (fb0 a') ,
              Extensions.level {n} {m} (cB a') (b0 a') (C a') (fb0 a'))
           (fa0 , agree))

       wedge-elim-βb : ∀ {m n p} {A : Type} {B : A → Type}
                      (cA : Connected (S m) A) 
                      (cB : (a : A) → Connected (S n) (B a))
                      (C : (a : A) → (B a) → NTypes p) 
                      (app : p <=tl plus2 m n)
                      {a0 : A} {b0 : (a : A) → B a}
                   -> (fa0 : (b' : B a0) -> fst (C a0 b'))
                   -> (fb0 : (a' : A) -> fst (C a' (b0 a')))
                   -> (agree : fa0 (b0 a0) ≃ fb0 a0)
                   -> (\ a -> wedge-elim cA cB C app fa0 fb0 agree a (b0 a)) ≃ fb0
       wedge-elim-βb {m}{n}{p}{A}{B} cA cB C app{a0}{b0} fa0 fb0 agree =
        λ≃ (\ a -> snd (wedge-elim' cA cB (λ a b → fst (C a b) , raise-level app (snd (C a b))) fa0 fb0 agree a))

       wedge-elim-coh : ∀ {m n p} {A : Type} {B : A → Type}
                      (cA : Connected (S m) A) 
                      (cB : (a : A) → Connected (S n) (B a))
                      (C : (a : A) → (B a) → NTypes p) 
                      (app : p <=tl plus2 m n)
                      {a0 : A} {b0 : (a : A) → B a}
                   -> (fa0 : (b' : B a0) -> fst (C a0 b'))
                   -> (fb0 : (a' : A) -> fst (C a' (b0 a')))
                   -> (agree : fa0 (b0 a0) ≃ fb0 a0)
                   ->   ap≃ (wedge-elim-βb cA cB C app fa0 fb0 agree) {a0}
                        ≃ agree ∘ ap≃ (wedge-elim-βa cA cB C app fa0 fb0 agree) {b0 a0}
       wedge-elim-coh cA cB C app {a0}{b0} fa0 fb0 agree =
        let C' = (λ a b → fst (C a b) , raise-level app (snd (C a b))) 
        in 
         ap≃ (wedge-elim-βb cA cB C app fa0 fb0 agree) {a0} ≃〈 Π≃β (\ a -> snd (wedge-elim' cA cB (λ a b → fst (C a b) , raise-level app (snd (C a b))) fa0 fb0 agree a)) 〉
         snd (wedge-elim' cA cB (λ a b → fst (C a b) , raise-level app (snd (C a b))) fa0 fb0 agree a0) ≃〈 id 〉
         snd (Connected.everywhere _ {_} {a0} cA
               (λ a' → Extensions.Extensions _ (b0 a') (λ b → fst (C' a' b)) (fb0 a') ,
                       Extensions.level (cB a') (b0 a') (C' a') (fb0 a'))
               (fa0 , agree) a0) ≃〈 snd≃⁻
                                       (Connected.β _ cA
                                        (λ a' →
                                           Extensions.Extensions _ _ (fst o C' a') (fb0 a') ,
                                           Extensions.level (cB a') (b0 a') (C' a') (fb0 a'))
                                        (fa0 , agree)) 〉 
         transport (λ f → f (b0 a0) ≃ fb0 a0)
           (! (wedge-elim-βa cA cB C app fa0 fb0 agree))
           agree ≃〈 transport-Path-pre' (λ f → f (b0 a0)) (! (wedge-elim-βa cA cB C app fa0 fb0 agree)) agree 〉 
         agree ∘ ! (ap≃ (! (wedge-elim-βa cA cB C app fa0 fb0 agree)) {b0 a0}) ≃〈 ap (_∘_ agree) (! (ap-! (λ f → f (b0 a0)) (! (wedge-elim-βa cA cB C app fa0 fb0 agree)))) 〉 
         agree ∘ (ap≃ (! (! (wedge-elim-βa cA cB C app fa0 fb0 agree))) {b0 a0}) ≃〈 ap (\ x -> agree ∘ ap≃ x {b0 a0}) (!-invol (wedge-elim-βa cA cB C app fa0 fb0 agree)) 〉 
         (agree ∘ ap≃ (wedge-elim-βa cA cB C app fa0 fb0 agree) {b0 a0} ∎)

       wedge-rec : ∀ {m n p} {A : Type} {B : A → Type} {C}
                 -> Connected (S m) A 
                 -> (cB : (a : A) → Connected (S n) (B a))
                 -> NType p C 
                 -> (app : p <=tl (plus2 m n))
                 -> {a0 : A} (b0 : (a : A) → B a)
                 -> (fa0 : B a0 -> C)
                 -> (fb0 : A -> C)
                 -> fa0 (b0 a0) ≃ fb0 a0 
                 -> (a : A) -> B a -> C
       wedge-rec cA cB nC app b0 = wedge-elim cA cB (\ _ _ -> _ , nC) app {_}{b0}

       wedge-rec-βa : ∀ {m n p} {A : Type} {B : A → Type} {C}
                 -> (cA : Connected (S m) A)
                 -> (cB : (a : A) → Connected (S n) (B a))
                 -> (nC : NType p C)
                 -> (app : p <=tl (plus2 m n))
                 -> {a0 : A} (b0 : (a : A) → B a)
                 -> (fa0 : B a0 -> C)
                 -> (fb0 : A -> C)
                 -> (agree : fa0 (b0 a0) ≃ fb0 a0)
                 -> (wedge-rec cA cB nC app b0 fa0 fb0 agree a0 ≃ fa0)
       wedge-rec-βa cA cB nC app b0 = wedge-elim-βa cA cB (\ _ _ -> _ , nC) app {_}{b0}
      
       wedge-rec-βb : ∀ {m n p} {A : Type} {B : A → Type} {C}
                 -> (cA : Connected (S m) A)
                 -> (cB : (a : A) → Connected (S n) (B a))
                 -> (nC : NType p C)
                 -> (app : p <=tl (plus2 m n))
                 -> {a0 : A} (b0 : (a : A) → B a)
                 -> (fa0 : B a0 -> C)
                 -> (fb0 : A -> C)
                 -> (agree : fa0 (b0 a0) ≃ fb0 a0)
                 -> (\ a' -> wedge-rec cA cB nC app b0 fa0 fb0 agree a' (b0 a')) ≃ fb0
       wedge-rec-βb cA cB nC app b0 = wedge-elim-βb cA cB (\ _ _ -> _ , nC) app {_}{b0}

       wedge-rec-coh : ∀ {m n p} {A : Type} {B : A → Type} {C}
                 -> (cA : Connected (S m) A)
                 -> (cB : (a : A) → Connected (S n) (B a))
                 -> (nC : NType p C)
                 -> (app : p <=tl (plus2 m n))
                 -> {a0 : A} (b0 : (a : A) → B a)
                 -> (fa0 : B a0 -> C)
                 -> (fb0 : A -> C)
                 -> (agree : fa0 (b0 a0) ≃ fb0 a0)
                 ->   ap≃ (wedge-rec-βb cA cB nC app b0 fa0 fb0 agree) {a0}
                        ≃ agree ∘ ap≃ (wedge-rec-βa cA cB nC app b0 fa0 fb0 agree) {b0 a0}
       wedge-rec-coh cA cB nC app b0 = wedge-elim-coh cA cB (\ _ _ -> _ , nC) app {_}{b0}

