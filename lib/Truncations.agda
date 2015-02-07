
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Prods
open import lib.Sums
open import lib.Functions
open import lib.Nat
open import lib.NType
open import lib.Universe
open import lib.AdjointEquiv
open import lib.HFiber

module lib.Truncations where

  module Truncation where

   module T where
    private
      data Trunc' (n : TLevel) (A : Type) : Type where
        trunc' : A -> Trunc' n A

      data Trunc'' (n : TLevel) (A : Type) : Type where
        mkTrunc'' : Trunc' n A → (Unit -> Unit) → Trunc'' n A

    Trunc : (n : TLevel) (A : Type) → Type
    Trunc = Trunc'' 

    [_] : {n : TLevel} {A : Type} → A -> Trunc n A
    [ x ] = mkTrunc'' (trunc' x) _

    postulate {- HoTT Axiom -}
      Trunc-level : {n : TLevel} {A : Type} → NType n (Trunc n A)

    Trunc-rec : {A C : Type} {n : TLevel} (tC : NType n C)
          -> (A → C)
          → (Trunc n A) → C
    Trunc-rec _ f (mkTrunc'' (trunc' x) _) = f x

    Trunc-elim : {A : Type} {n : TLevel} (C : Trunc n A → Type)
                (tC : (x : Trunc n A) → NType n (C x))
          -> ((x : A) → C [ x ])
          → (x : (Trunc n A)) → C x
    Trunc-elim _ _ f (mkTrunc'' (trunc' x) _) = f x
   open T public

   τ₋₁ = Trunc -1
   τ₀ = Trunc (tl 0)
   τ₁ = Trunc (tl 1)
   τ₂ = Trunc (tl 2)

   Trunc-simple-η : ∀ {n A} {y : Trunc n A} 
                  → Trunc-rec{A}{Trunc n A}{n} (Trunc-level{n}{A}) [_] y ≃ y
   Trunc-simple-η {n}{A}{y} = Trunc-elim (λ z → Path (Trunc-rec (Trunc-level{n}{A}) [_] z) z) 
                                         (λ x → path-preserves-level (Trunc-level {n} {A}) )
                                         (λ _ → id)
                                         y
                                      
   transport-Trunc : {n : TLevel} {Γ : Type} (A : Γ → Type) {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
                   →  transport (\ x -> Trunc n (A x)) δ 
                    ≃ Trunc-rec (Trunc-level {n} {A θ2}) (λ x → [ transport A δ x ])
   transport-Trunc A id = λ≃ (\ y -> ! (Trunc-simple-η {_} {_} {y}))

   transport-Trunc-tlevel : {n k : TLevel} (A : Type) (a : A) (δ : n ≃ k)
                   →  transport (\ x -> Trunc x A) δ [ a ] ≃ [ a ]
   transport-Trunc-tlevel A a id = id

   coe-Trunc-tlevel : {n k : TLevel} (A : Type) (a : A) (δ : n ≃ k)
                   →  coe (ap (\ x -> Trunc x A) δ) [ a ] ≃ [ a ]
   coe-Trunc-tlevel A a id = id

   -- avoid the λ≃ because it's annoying to unpack later
   transport-Trunc' : {n : TLevel} {Γ : Type} (A : Γ → Type) {θ1 θ2 : Γ} (δ : θ1 ≃ θ2) (y : Trunc n (A θ1))
                     →  transport (\ x -> Trunc n (A x)) δ y
                    ≃ Trunc-rec (Trunc-level {n} {A θ2}) (λ x → [ transport A δ x ]) y
   transport-Trunc' A id y = ! (Trunc-simple-η {_} {_} {y})

   Trunc-func : {n : TLevel} {A B : Type} -> (A -> B) -> (Trunc n A -> Trunc n B)
   Trunc-func f = Trunc-rec Trunc-level ([_] o f)

   -- one of the monad laws
   Trunc-rec-cconv : (n : TLevel) {A B C : Type} (nC : NType n C)
                     (f : A → Trunc n B) (g : B → C)
                     (x : Trunc n A) → Trunc-rec nC g (Trunc-rec Trunc-level f x) ==  Trunc-rec nC (Trunc-rec nC g o f) x
   Trunc-rec-cconv n nC f g = Trunc-elim _ (λ _ → path-preserves-level nC) (λ _ → id)
                    
   Trunc-reflective : ∀ k {A} -> NType k A → Trunc k A ≃ A
   Trunc-reflective k tA = ua (improve (hequiv (Trunc-rec tA (λ x → x)) [_] (Trunc-elim _ (λ _ → path-preserves-level Trunc-level) (λ _ → id)) (λ _ → id)))

   -- version that computes
   apTrunc' : {n : TLevel} {A B : Type} → Equiv A B → Equiv (Trunc n A) (Trunc n B)
   apTrunc' e = improve (hequiv (Trunc-func (fst e)) (Trunc-func (IsEquiv.g (snd e)))
                                (Trunc-elim _ (λ _ → path-preserves-level Trunc-level) (λ x → ap [_] (IsEquiv.α (snd e) x)))
                                (Trunc-elim _ (λ _ → path-preserves-level Trunc-level) (λ x → ap [_] (IsEquiv.β (snd e) x))))

   module TruncPath (n : _) {A : _} {x : A} where

     decode' : {y : _} → (Trunc n (Path x y)) → Path {(Trunc (S n) A)} [ x ] [ y ]
     decode' {y} = Trunc-rec (use-level (Trunc-level {S n} {A}) [ x ] [ y ]) (ap [_]) 

     Codes : Trunc (S n) A → NTypes n
     Codes = Trunc-rec (NTypes-level n) 
                       (λ y → Trunc n (Path x y) , Trunc-level) 
     
     encode : {y : Trunc (S n) A}
           → Path {(Trunc (S n) A)} [ x ] y
           → fst (Codes y)
     encode α = transport (fst o Codes) α [ id ]

     encode' : {y : A}
           → Path {(Trunc (S n) A)} [ x ] [ y ]
           → (Trunc n (Path x y))
     encode'{y} = encode {[ y ]}

     encode-decode' : {y : A} (c : fst (Codes [ y ]))
                    → encode'{y} (decode'{y} c) ≃ c
     encode-decode' = Trunc-elim _ (λ x' → path-preserves-level Trunc-level) 
       (λ α → transport (λ x' → fst (Trunc-rec (NTypes-level n) (λ y → Trunc n (Id x y) , Trunc-level) x')) (ap [_] α) [ id ] ≃〈 ! (ap≃ (transport-ap-assoc' (λ x' → fst (Trunc-rec (NTypes-level n) (λ y → Trunc n (Id x y) , Trunc-level) x')) [_] α)) 〉 
              transport (λ y → Trunc n (Id x y)) α [ id ] ≃〈 ap≃ (transport-Trunc (λ y → Id x y) α) 〉
              [ transport (\ y -> (Id x y)) α id ] ≃〈 ap [_] (transport-Path-right α id) 〉
              [ α ] ∎)

     decode : {y : Trunc (S n) A}
           → fst (Codes y)
           → Path {(Trunc (S n) A)} [ x ] y
     decode {y} = Trunc-elim (\ y -> fst (Codes y) → Path {(Trunc (S n) A)} [ x ] y)
                             (λ x' → Πlevel (λ x'' → path-preserves-level Trunc-level))
                             (λ y' → decode' {y'})
                             y
 
     decode-encode : {y : _} (p : Path [ x ] y) → decode{y} (encode{y} p) ≃ p
     decode-encode id = id

     eqv : {y : A} -> Equiv (Trunc n (Path x y)) (Path {(Trunc (S n) A)} [ x ] [ y ])
     eqv {y} = improve (hequiv decode encode encode-decode' decode-encode)

     path : {y : A} -> (Trunc n (Path x y)) ≃ (Path {(Trunc (S n) A)} [ x ] [ y ])
     path {y} = ua eqv

   abstract
     decrement-Trunc-preserves-level : ∀ {n} {k} {A} 
                                     -> NType k (Trunc (S n) A) → NType k (Trunc n A)
     decrement-Trunc-preserves-level {n} { -2} nTA = ntype (lemma (use-level nTA)) where
         lower-path : ∀ {n} {A} {x y} → Path {Trunc (S n) A} [ x ] [ y ] → Path {Trunc n A} [ x ] [ y ]
         lower-path = ap (Trunc-rec (increment-level Trunc-level) (λ x → [ x ]))
   
         lemma : ∀ {n A} → Contractible (Trunc (S n) A) → Contractible (Trunc n A)
         lemma {n}{A} c = Trunc-elim (λ x → ((y : _) → Path x y) → Contractible (Trunc n A))
                            (λ _ → Πlevel (λ _ → raise-HProp (Contractible-is-HProp _)))
                            (λ x f → [ x ] , 
                                     (Trunc-elim (λ y → Path [ x ] y) 
                                                 (λ _ → path-preserves-level Trunc-level)
                                                 (λ y → lower-path (f [ y ]))))
                            (fst c) (snd c)
     decrement-Trunc-preserves-level { -2 } {k} nTA = raise-level (-2<= _) Trunc-level
     decrement-Trunc-preserves-level {S n} {(S k)} nTA = 
       ntype (Trunc-elim (\ x -> ( y : _) -> NType k (Path x y))
                         (λ _ → Πlevel (λ _ → raise-HProp (NType-is-HProp _)))
                         (λ x → Trunc-elim (λ y → NType k (Path [ x ] y)) 
                                (λ _ → raise-HProp (NType-is-HProp _))
                                (λ y →  transport (NType k) (TruncPath.path _)
                                          (decrement-Trunc-preserves-level
                                           (transport (NType k) (! (TruncPath.path _))
                                            (use-level nTA [ x ] [ y ]))))))
    
     lower-Trunc-preserves-level : ∀ n1 n2 {k} {A} → n2 <=tl n1 
                                  -> NType k (Trunc n1 A) → NType k (Trunc n2 A)
     lower-Trunc-preserves-level .(S n2) n2 (Inl ltS) nTA = decrement-Trunc-preserves-level nTA
     lower-Trunc-preserves-level (S m) n2 (Inl (ltSR lt)) nTA = lower-Trunc-preserves-level _ _ (Inl lt) (decrement-Trunc-preserves-level nTA)
     lower-Trunc-preserves-level n1 .n1 (Inr id) nTA = nTA

     Trunc-preserves-contractibility : ∀ {n}{A} -> Contractible A -> Contractible (Trunc n A)
     Trunc-preserves-contractibility (center , eq) = 
       [ center ] , Trunc-elim _ (λ _ → path-preserves-level Trunc-level) (λ x → ap [_] (eq x))
  
     Trunc-level-better : ∀ {n} {k} {A} -> NType n A -> NType (mintl k n) (Trunc k A)
     Trunc-level-better {n} { -2} nA = Trunc-level
     Trunc-level-better { -2 } {S k} nA = ntype (Trunc-preserves-contractibility (use-level nA))
     Trunc-level-better { S n } {S k} nA = 
       ntype (Trunc-elim _ (λ _ → Πlevel (λ _ → raise-HProp (NType-is-HProp _)))
                           (\ x -> Trunc-elim (λ y → NType (mintl k n) (Path [ x ] y)) 
                                              (λ _ → raise-HProp (NType-is-HProp _))
                                              (λ y → transport (NType (mintl k n)) (TruncPath.path _)
                                                       (Trunc-level-better (use-level nA _ _)))))

   module FuseTrunc (n k : TLevel) (A : Type) where 
 
     left : (Trunc n (Trunc k A)) → (Trunc (mintl n k) A)
     left = (Trunc-rec (raise-level (mintl<=1 n k) Trunc-level) 
                                      (Trunc-rec (raise-level (mintl<=2 n k) Trunc-level) 
                                                 [_]))

     right : (Trunc (mintl n k) A) → (Trunc n (Trunc k A))
     right = (Trunc-rec (Trunc-level-better Trunc-level) (λ x → [ [ x ] ]))

     eqv : Equiv (Trunc n (Trunc k A)) (Trunc (mintl n k) A)
     eqv = improve (hequiv left
                           right
                           (Trunc-elim _ (λ _ → path-preserves-level Trunc-level)
                              (Trunc-elim _ 
                                (λ _ → path-preserves-level (raise-level (mintl<=2 n k) (Trunc-level-better Trunc-level)))
                                (λ _ → id)))
                           (Trunc-elim _ (λ _ → path-preserves-level Trunc-level) (λ _ → id)))

     path : Trunc n (Trunc k A) ≃ Trunc (mintl n k) A
     path = ua eqv

   module SwapTrunc (n k : TLevel) (A : Type) where 
     path : Trunc n (Trunc k A) ≃ Trunc k (Trunc n A)
     path = ! (FuseTrunc.path k n A) ∘ ap (λ x → Trunc x A) (mintl-comm n k) ∘ FuseTrunc.path n k A

   module UnTrunc (n : TLevel) (A : Type) (nA : NType n A) where

    eqv : Equiv (Trunc n A) A
    eqv = improve (hequiv (Trunc-rec nA (λ x → x)) [_] (Trunc-elim _ (λ _ → path-preserves-level Trunc-level) (λ _ → id)) (λ _ → id))
    
    path : Trunc n A ≃ A
    path = ua eqv

   truncated-HFiber-equiv : {i : TLevel} {A B C : Type} 
     (f : A → C) (g : B → C) 
     (l' : (a : A) → Trunc i (HFiber g (f a)))
     (r' : (b : B) → Trunc i (HFiber f (g b)))
     (rl' : (a : A) → Path{Trunc i (HFiber f (f a))}
               (Trunc-rec Trunc-level (λ p → Trunc-func (λ p' → fst p' , snd p ∘ snd p') (r' (fst p))) (l' a) )
               [ a , id ])
     (lr' : (b : B) → Path{Trunc i (HFiber g (g b))}
               (Trunc-rec Trunc-level (λ p → Trunc-func (λ p' → fst p' , snd p ∘ snd p') (l' (fst p))) (r' b) )
               [ b , id ])
    → {c : C} → Equiv (Trunc i (HFiber f c)) (Trunc i (HFiber g c))
   truncated-HFiber-equiv {i} {A}{B}{C} f g l' r' rl' lr' {c} = 
     improve (hequiv (Trunc-rec Trunc-level l) 
                     (Trunc-rec Trunc-level r) 
                     (Trunc-elim _ (λ _ → path-preserves-level Trunc-level) rl)
                     (Trunc-elim _ (λ _ → path-preserves-level Trunc-level) lr)) where
     -- FIXME abstrct duplication

     l : {c : C} → HFiber f c → Trunc i (HFiber g c)
     l (a , q) = Trunc-func (λ p → fst p , q ∘ snd p) (l' a) -- write out the transport by hand so it reduces

     r : {c : C} → HFiber g c → Trunc i (HFiber f c)
     r (b , q) = Trunc-func (λ p → fst p , q ∘ snd p) (r' b)

     rl : {c : C} → (hf : HFiber f c) → (Trunc-rec Trunc-level r (l hf)) == [ hf ]
     rl (a , id) = Trunc-rec Trunc-level r (l (a , id)) ≃〈 id 〉 
                   Trunc-rec Trunc-level r (Trunc-func (λ p → fst p , id ∘ snd p) (l' a)) ≃〈 ap (λ X → Trunc-rec Trunc-level r (Trunc-func X (l' a))) (λ≃ (λ p → ap (λ Z₁ → fst p , Z₁) (∘-unit-l (snd p)))) 〉 
                   Trunc-rec Trunc-level r (Trunc-func (λ p → fst p , snd p) (l' a)) ≃〈 id 〉 
                   Trunc-rec Trunc-level r (Trunc-rec Trunc-level (λ p → [ fst p , snd p ]) (l' a)) ≃〈 Trunc-rec-cconv i Trunc-level (λ p → [ fst p , snd p ]) r  (l' a) 〉 
                   Trunc-rec Trunc-level (\ p → r (fst p , snd p)) (l' a) ≃〈 rl' a 〉 
                   _ ∎

     lr : {c : C} → (hf : HFiber g c) → (Trunc-rec Trunc-level l (r hf)) == [ hf ]
     lr (b , id) = Trunc-rec Trunc-level l (r (b , id)) ≃〈 id 〉 
                   Trunc-rec Trunc-level l (Trunc-func (λ p → fst p , id ∘ snd p) (r' b)) ≃〈 ap (λ X → Trunc-rec Trunc-level l (Trunc-func X (r' b))) (λ≃ (λ p → ap (λ Z₁ → fst p , Z₁) (∘-unit-l (snd p)))) 〉 
                   Trunc-rec Trunc-level l (Trunc-func (λ p → fst p , snd p) (r' b)) ≃〈 id 〉 
                   Trunc-rec Trunc-level l (Trunc-rec Trunc-level (λ p → [ fst p , snd p ]) (r' b)) ≃〈 Trunc-rec-cconv i Trunc-level (λ p → [ fst p , snd p ]) l  (r' b) 〉 
                   Trunc-rec Trunc-level (\ p → l (fst p , snd p)) (r' b) ≃〈 lr' b 〉 
                   _ ∎

   
