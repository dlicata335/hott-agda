{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module misc.Reflective where

  module Reflective (P : Type → NTypes -1) 
                    (<_> : Type → Type)
                    (isP : (A : Type) → fst (P < A >))
                    (<<_>> : {A : Type} → A → < A >)
                    (eqv : ∀ {A B} → fst (P B) → IsEquiv {< A > → B} {A → B}  (\ g → g o <<_>>)) where

   <>rec : ∀ {A B} → fst (P B) → (A → B) → (< A > → B)
   <>rec p = IsEquiv.g (eqv p)

   β : ∀ {A C} (p : fst (P C)) {f : A → C} → {x : A} → <>rec p f << x >> == f x
   β p {f} =  ap≃ (IsEquiv.β (eqv p) f)

   η : ∀ {A B} (p : fst (P B)) → (f : < A > → B) (g : A → B) → ((x : A) → f << x >> == g x) → ((y : < A >) → f y == <>rec p g y)
   η p f g h = (λ x → ap (λ h₁ → <>rec p h₁ x) (λ≃ h) ∘ ! (ap≃ (IsEquiv.α (eqv p) f)))

   ext : ∀ {A B} (p : fst (P B)) → (f g : < A > → B) → ((x : A) → f << x >> == g << x >>) → ((y : < A >) → f y == g y)
   ext p f g h y = ! (η p g (g o <<_>>) (λ _ → id) y) ∘ η p f (g o <<_>>) h y
             
   fromequiv : ∀ {A} → Equiv A (< A >) → fst (P A)
   fromequiv e = transport (fst o P) (! (ua e)) (isP _)

   toequiv : ∀ {A} → fst (P A) → Equiv A (< A >) 
   toequiv p = improve (hequiv <<_>> (<>rec p (λ x → x)) 
                       (λ x → β p) 
                       (λ y → ! (η (isP _) (λ y₁ → y₁) <<_>> (λ _ → id) y) ∘ η (isP _) (λ y₁ → << <>rec p (λ x → x) y₁ >>) <<_>> (λ x → ap <<_>> (β p)) y))

   P-retraction : ∀ {A B} → fst (P A) → (s : B → A) (r : A → B) → ((x : B) → r (s x) == x) → fst (P B)
   P-retraction p s r rs = fromequiv (improve (hequiv <<_>> (r o <>rec p s) 
                                   (λ x → rs _ ∘ ap r (β p)) 
                                   (λ y → ext (isP _) (λ y₁ → << r (<>rec p s y₁) >>) (λ x → x) (λ x → ap <<_>> (rs _ ∘ ap r (β p))) y)))

   -- P A if <<_>> admits a retraction
   <<>>admits : ∀ {A} → (un<<>> : < A > → A) → ((x : A) → un<<>> << x >> == x) → fst (P A)
   <<>>admits r h = P-retraction (isP _) <<_>> r h

   -- therefore negatives are automatically in P

   ⊤P : fst (P Unit)
   ⊤P = <<>>admits (λ _ → <>) (λ _ → id)

   ×P : ∀ {A B} → fst (P A) → fst (P B) → fst (P (A × B))
   ×P pA pB = <<>>admits (λ x → <>rec pA fst x , <>rec pB snd x) (λ x → ap2 _,_ (β pA) (β pB))

   ΠP : ∀ {A} {B : A → Type} → ((x : A) → fst (P (B x))) → fst (P ((x : A) → B x))
   ΠP pB = <<>>admits (λ <f> → λ x → <>rec (pB _) (λ f → f x) <f>) 
                      (λ f → λ≃ (λ x → β _))

   -- TODO P of Id, encode decode

   -- doesn't seem to hold in general
   -- P⊥ : fst (P Void)
   -- P⊥ = <<>>admits {!!} {!!}
   
   -- gets stuck because not right invertible
   -- PEither : ∀ {A B} → fst (P A) → fst (P B) → fst (P (Either A B))
   -- PEither pA pB = <<>>admits {!!} {!!} 

   -- can do this just by writing the maps and checking them
   commute<>× : ∀ {A B} → Equiv (< A > × < B >) (< A × B >)
   commute<>× = improve (hequiv (λ ab → <>rec (isP _) (λ a → <>rec (isP _) (λ b → << a , b >>) (snd ab)) (fst ab))
                                (<>rec (×P (isP _) (isP _)) (λ ab → << fst ab >> , << snd ab >>)) 
                                (λ p → ext (×P (isP _) (isP _))
                                         (λ a → <>rec (×P (isP _) (isP _)) (λ ab → << fst ab >> , << snd ab >>) (<>rec (isP _) (λ a₁ → <>rec (isP _) (λ b → << a₁ , b >>) (snd p)) a))
                                         (λ a → a , snd p) 
                                         (λ a → ext (×P (isP _) (isP _)) (λ b → <>rec (×P _ _) (λ ab → << fst ab >> , << snd ab >>) (<>rec (isP _) (λ a₁ → <>rec (isP _) (λ b₁ → << a₁ , b₁ >>) b) << a >>))
                                                    (λ b → << a >> , b)
                                                    (λ b → β _ ∘ ap (<>rec _ _) (β _ ∘ β _)) (snd p)) (fst p))
                                (ext (isP _) _ _ (λ p → (β _) ∘
                                                          ap2 (λ h1 h2 → <>rec (isP _) h1 h2 )
                                                              (λ≃ (λ a → β _ ∘ ap (λ h → <>rec (isP _) (λ b → << a , b >>) h) (ap snd (β _))))
                                                              (ap fst (β _)))))

   -- also can do it using a lemma like what's in the book, but 
   -- *** need to show M is in P ! ***
   suffices-to-show-universal-property : ∀ {M A} → 
           (p : fst (P M))
           (<<_>>' : A → M) 
           (eqv : ∀ {B} → fst (P B) → IsEquiv {M → B} {A → B}  (\ g → g o <<_>>'))
           → Equiv M (< A >) 
   suffices-to-show-universal-property{M}{A} p <<_>>' eqv' = improve (hequiv (IsEquiv.g (eqv' (isP _)) <<_>>) 
                                                    (<>rec p <<_>>') 
                                                    (ext' p _ _ (λ x → β _ ∘ ap (<>rec p <<_>>') (ap≃ (IsEquiv.β (eqv' _) <<_>>))))
                                                    (ext (isP _) _ _ (λ x → ap≃ (IsEquiv.β (eqv' (isP _)) <<_>>) ∘ ap (IsEquiv.g (eqv' (isP _)) <<_>>) (β _)))) where
      -- FIXME abstract the copy and paste with above
      <>rec' : ∀ {B} → fst (P B) → (A → B) → (M → B)
      <>rec' p = IsEquiv.g (eqv' p)
   
      η' : ∀ {B} (p : fst (P B)) → (f : M → B) (g : A → B) → ((x : A) → f << x >>' == g x) → ((y : M) → f y == <>rec' p g y)
      η' p f g h = (λ x → ap (λ h₁ → <>rec' p h₁ x) (λ≃ h) ∘ ! (ap≃ (IsEquiv.α (eqv' p) f)))

      ext' : ∀ {B} (p : fst (P B)) → (f g : M → B) → ((x : A) → f << x >>' == g << x >>') → ((y : M) → f y == g y)
      ext' p f g h y = ! (η' p g (g o <<_>>') (λ _ → id) y) ∘ η' p f (g o <<_>>') h y

   commute<>×-book : ∀ {A B} → Equiv (< A > × < B >) (< A × B >)
   commute<>×-book {A} {B} = suffices-to-show-universal-property (×P (isP _) (isP _))
                                              (λ p → << fst p >> , << snd p >>) 
                                              (λ {C} pC → snd (the-eqv pC)) where
      the-eqv : ∀ {C} (pC : fst (P C)) → Equiv (< A > × < B > → C) (A × B → C)
      the-eqv {C} pC = !equiv (uncurry-eqv A (λ _ → B) (λ _ → C)) ∘equiv ((_ , eqv (ΠP (λ x → pC))) ∘equiv ap→-range-eqv {< A >}{< B > → C}{ B → C} (_ , eqv pC)) ∘equiv uncurry-eqv < A > (λ _ → < B >) (λ _ → C)


   -- not true in general?
   -- commuteP→ : ∀ {A B} → < (A → B) > == (A → < B >)
   -- commuteP→ = {!!}

   -- if we drop the condition that M is known to be in P, then the same proof works for coproducts
   module Bad (suffices-to-show? : ∀ {M A} → 
                                     (<<_>>' : A → M) 
                                     (eqv : ∀ {B} → fst (P B) → IsEquiv {M → B} {A → B}  (\ g → g o <<_>>'))
                                   → Equiv M (< A >)) 
          where

     coprod : ∀ {A B} → Equiv (Either < A > < B >) (< Either A B >)
     coprod {A} {B} = suffices-to-show? (Sums.case _ (Inl o <<_>>) (Inr o <<_>>)) 
                                      -- ENH: case analysis is doing f(case) = case with f in branches 
                                      (λ pC → transport IsEquiv (λ≃ (λ f → λ≃ (λ { (Inl x) → id ; (Inr y) → id }))) (snd (the-eqv pC))) where
       the-eqv : ∀ {C} (pC : fst (P C)) → Equiv (Either < A > < B > → C) (Either A B → C)
       the-eqv pC = Sums.Either-UMP ∘equiv ap×-eqv (_ , eqv pC) (_ , eqv pC) ∘equiv !equiv Sums.Either-UMP


  module DN where
    ¬ : Type → Type
    ¬ A = A → Void

    dni : ∀ {A} → A → ¬ (¬ A)
    dni a k = k a

    tne : ∀ {A} → ¬ (¬ (¬ A)) → ¬ A
    tne f a = f (dni a)

    tn-eqv : ∀ {A} → Equiv (¬ A) (¬ (¬ (¬ A))) 
    tn-eqv = improve (hequiv dni tne (λ _ → id) (λ k → λ≃ (λ x → Sums.abort (k x))))

    -- instance of a general construction: start with <_> and <<_>>, predicate is A equiv ◯ A

    ¬¬Stable : Type → NTypes -1
    ¬¬Stable = (\ A → (IsEquiv {A} {(¬ (¬ A))} dni , IsEquiv-HProp _))

    <_> : Type → Type
    < A > =  ¬ (¬ A)

    <<_>> : ∀ {A} → A → < A >
    << a >> = dni a

    <>func : ∀ {A B} → (A → B) → < A > → < B >
    <>func f kk k = kk (k o f)

    open Reflective ¬¬Stable <_> (λ A → snd tn-eqv) <<_>> 
                    -- (essentially) ¬¬A → ¬¬B is same as A → ¬¬B
                    (λ a → snd (improve (hequiv _ (λ f → IsEquiv.g a o <>func f) 
                                                  (λ x → λ≃ (λ kk → IsEquiv.α a (x kk) ∘ ap (IsEquiv.g a) (λ≃ (λ x₁ → Sums.abort (x₁ (x kk))))))
                                                  (λ f → λ≃ (λ y → move-path-along-equiv/general-conclusion (!equiv (_ , a)) (IsEquiv.β a (dni (f y))))))))

    ⊥P : fst (¬¬Stable Void)
    ⊥P = snd (improve (hequiv _ (λ k → k (λ x → x)) (λ x → Sums.abort x) (λ y → Sums.abort (y (λ x → x)))))

    -- probably not?
    -- ΣP : ∀ {A} {B : A → Type} → fst (¬¬Stable A) → ((x : A) → fst (¬¬Stable (B x))) → fst (¬¬Stable (Σ B))
    -- ΣP pA pB = <<>>admits (λ ab → (<>rec pA fst ab) , (<>rec (pB _) (λ ab₁ → {!!}) ab)) {!!}
