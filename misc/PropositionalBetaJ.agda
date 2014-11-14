
module misc.PropositionalBetaJ where

  record Σe (A : Set) (B : A -> Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B fst
  open Σe public

  Σ : {A : Set} -> (B : A -> Set) -> Set
  Σ {A} B = Σe A B

  infixr 0 _,_

  postulate
    Id : {A : Set} → A → A → Set
    refl : {A : Set} {a : A} → Id a a 
    transport :  {B : Set} (E : B → Set) 
              {b1 b2 : B} → Id b1 b2 → (E b1 → E b2)
    transport-refl : {B : Set} (E : B → Set) 
                     {b1 : B} (e1 : E b1) → Id (transport E refl e1) e1
  
  Contractible : Set -> Set
  Contractible A = Σ \(c : A) → (y : A) → Id c y

  postulate 
    scontr : {A : Set} {a b : A} (p : Id a b) → Id { Σ \ y → Id a y} (a , refl) (b , p)

  path-induction : {A : Set} {M : A}
                  (C : (x : A) → Id M x → Set)
               → (C M refl)
               → {N : A} → (P : Id M N)
               → C N P
  path-induction {A}{a} C b P = transport (\ (q : Σ \ y → Id a y) → C (fst q) (snd q)) (scontr P) b

  scontr' : {A : Set} {a : A} → Contractible (Σ \ y → Id a y)
  scontr' {A}{a} = ((a , refl) , (λ y → scontr (snd y)))
  
  apd  :  {B : Set} {E : B → Set} {b₁ b₂ : B} 
            (f : (x : B) → E x) (β : Id b₁ b₂) 
         → Id(transport E β (f b₁)) (f b₂) 
  apd {B}{E}{b₁}{b₂} f β = 
    path-induction (λ b₃ β₁ → Id (transport E β₁ (f b₁)) (f b₃)) (transport-refl E (f b₁)) β

  transport-β-right : {A : Set} {a b : A} {p : Id a b} 
                      → Id (transport (\ x -> Id a x) p refl) p
  transport-β-right {A}{a}{b}{p} = 
    path-induction (\ b p → Id (transport (\ x -> Id a x) p refl) p)
                   (transport-refl (λ x → Id _ x) refl) p

  _∘_  : {A : Set} {M N P : A} 
      → Id N P → Id M N → Id M P
  _∘_ P Q = transport (\ x -> Id _ x) P Q

  !  : {A : Set} {M N : A} → Id M N → Id N M
  ! P = transport (λ x → Id x _) P refl

  transport-same : {A : Set} {a b : A} {p : Id b b } {q : Id a b}
                  → Id (transport (\ x -> Id a x) p q) q
                  → Id p refl
  transport-same {A}{a}{b}{p}{q} = path-induction
                                     (λ b' q' →
                                        (p₁ : Id b' b') →
                                        Id (transport (λ x → Id a x) p₁ q') q' → Id p₁ refl)
                                     (λ p₁ → λ r → r ∘ ! (transport-β-right {p = p₁})) q p

  contr-loop-hprop : {A : Set} → Contractible A → 
                    (x : A) (p : Id x x) → Id p refl
  contr-loop-hprop cA x p = transport-same (apd (snd cA) p)

  contr-paths-hprop : {A : Set} → Contractible A → 
                    (x y : A) (p q : Id x y) → Id p q
  contr-paths-hprop cA x y p q = 
    path-induction (λ y₁ q₁ → ∀ p₁ → Id p₁ q₁) (λ q₁ → contr-loop-hprop cA _ q₁) q p

  thm : {A : Set} {a : A} → Id{Id{Σ \ y → Id a y} (a , refl) (a , refl)} (scontr {A}{a} refl) refl
  thm = contr-paths-hprop scontr' _ _ _ _
