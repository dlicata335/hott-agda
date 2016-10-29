
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 

module misc.Monad where

  flip : ∀ {A B C} → (A → B → C) → (B → A → C)
  flip f b a = f a b


  module Old where

    record Monad (T : Type → Type) : Type where
      field
        return : ∀ {A} → A → T A
        _>>=_  : ∀ {A B} → T A → (A → T B) → T B
        lunit  : ∀ {A B} {a : A} {f : A → T B} → (return a >>= f) == f a
        runit  : ∀ {A} {c : T A} → (c >>= return) == c
        assoc  : ∀ {A B C} {c : T A} {f : A → T B} {g : B → T C} 
               → ((c >>= f) >>= g) == c >>= (λ x → f x >>= g) 


  module New where

    record Applicative (T : Type → Type) : Type where
      constructor applicative
      field
        pure       : ∀ {A} → A → T A
        _<*>_      : ∀ {A B} → T (A → B) → T A → T B
        pure-id    : ∀ {A} {c : T A} → pure (\ x → x) <*> c == c
        pure-comp  : ∀ {A B C} {f : T (A → B)} {g : T (B → C)} {c : T A} 
                   → ((pure _o_ <*> g) <*> f) <*> c == g <*> (f <*> c)
        apply-pure : ∀ {A B} {f : A → B} {a : A} 
                   → pure f <*> pure a == pure (f a)
        apply-to-pure : ∀ {A B} {f : T (A → B)} {a : A} 
                      → f <*> (pure a) == pure (λ f₁ → f₁ a) <*> f

      fmap    : ∀ {A B} → (A → B) → T A → T B
      fmap f a = pure f <*> a

    applicative-hset= : ∀ {T : Type → Type} (sT : (A : Type) → HSet (T A))
                     → {t1 t2 : Applicative T}
                     → (\ {A : Type} → Applicative.pure t1 {A}) == Applicative.pure t2
                     → (\ {A} {B} → Applicative._<*>_ t1 {A}{B}) == Applicative._<*>_ t2
                     → t1 == t2
    applicative-hset= {T} sT {applicative pure _<*>_ pure-id pure-comp apply-pure apply-to-pure} {applicative .pure ._<*>_ pure-id₁ pure-comp₁ apply-pure₁ apply-to-pure₁} id id = 
      ( ap (λ (h : ∀ {A B} {f : T (A → B)} {a : A} → f <*> (pure a) == pure (λ f₁ → f₁ a) <*> f) → applicative pure _<*>_ _ _ _ h) (λ≃i (λ _ → λ≃i (λ _ → λ≃i (λ _ → λ≃i (λ _ → HSet-UIP (sT _) _ _ _ _))))) ∘
        ap (λ (h : ∀ {A B} {f : A → B} {a : A} → pure f <*> pure a == pure (f a)) → applicative pure _<*>_ _ _ h _) (λ≃i (λ _ → λ≃i (λ _ → λ≃i (λ _ → λ≃i (λ _ → HSet-UIP (sT _) _ _ _ _))))) ∘
        ap (λ (h : ∀ {A B C} {f : T (A → B)} {g : T (B → C)} {c : T A} → ((pure _o_ <*> g) <*> f) <*> c == g <*> (f <*> c)) → applicative pure _<*>_ _ h _ _) (λ≃i (λ _ → λ≃i (λ _ → λ≃i (λ _ → λ≃i (λ _ → λ≃i (λ _ → λ≃i (λ _ → HSet-UIP (sT _) _ _ _ _)))))))) ∘
        ap (λ (h : ∀ {A} {c : T A} → pure (λ x → x) <*> c == c) → applicative pure _<*>_ h _ _ _) (λ≃i (λ _ → λ≃i (λ _ → HSet-UIP (sT _) _ _ _ _)))
      
    record App⇒Monad (T : Type → Type) : Type where
      constructor monad
      field
        AT : Applicative T
      open Applicative AT
      field
        return : ∀ {A} → A → T A
        _>>=_  : ∀ {A B} → T A → (A → T B) → T B
        lunit  : ∀ {A B} {a : A} {f : A → T B} → (return a >>= f) == f a
        runit  : ∀ {A} {c : T A} → (c >>= return) == c
        assoc  : ∀ {A B C} {c : T A} {f : A → T B} {g : B → T C} 
               → ((c >>= f) >>= g) == c >>= (λ x → f x >>= g) 
        return-pure : ∀ {A} {a : A} → pure a == return a
        <*>-ap      : ∀ {A B} {f : T (A → B)} {a : T A}
                    → f <*> a == ( f >>= λ f' → 
                                   a >>= λ a' → 
                                   return (f' a'))

    monad-hset= : ∀ {T : Type → Type} (sT : (A : Type) → HSet (T A))
                     → {m1 m2 : App⇒Monad T}
                     → (\ {A : Type} → App⇒Monad.return m1 {A}) == App⇒Monad.return m2
                     → (\ {A} {B} → App⇒Monad._>>=_ m1 {A}{B}) == App⇒Monad._>>=_ m2
                     → m1 == m2
    monad-hset= sT {monad AT return _>>=_ lunit runit assoc return-pure <*>-ap} {monad AT₁ .return ._>>=_ lunit₁ runit₁ assoc₁ return-pure₁ <*>-ap₁} id id with applicative-hset= sT {AT} {AT₁} (λ≃i (λ _ → λ≃ (λ x → ! return-pure₁ ∘ return-pure))) (λ≃i (λ _ → λ≃i (λ _ → λ≃ (λ _ → λ≃ (λ _ → ! <*>-ap₁ ∘ <*>-ap)))))
    monad-hset= {T} sT {monad AT return _>>=_ lunit runit assoc return-pure <*>-ap} {monad .AT .return ._>>=_ lunit₁ runit₁ assoc₁ return-pure₁ <*>-ap₁} id id | id = 
      ap (\ (h : ∀ {A B} {a : A} {f : A → T B} → (return a >>= f) == f a) → monad AT return _>>=_ h _ _ _ _) (λ≃i (λ _ → λ≃i (λ _ → λ≃i (λ _ → λ≃i (λ _ → HSet-UIP (sT _) _ _ _ _))))) ∘ 
      ap (\ (h : ∀ {A} {c : T A} → (c >>= return) == c) → monad AT return _>>=_ _ h _ _ _) (λ≃i (λ _ → λ≃i (λ _ → HSet-UIP (sT _) _ _ _ _))) ∘ 
      ap (\ (h : ∀ {A B C} {c : T A} {f : A → T B} {g : B → T C} → ((c >>= f) >>= g) == c >>= (λ x → f x >>= g) ) → monad AT return _>>=_ _ _ h _ _) (λ≃i (λ _ → λ≃i (λ _ → λ≃i (λ _ → λ≃i (λ _ → λ≃i (λ _ → λ≃i (λ _ → HSet-UIP (sT _) _ _ _ _))))))) ∘ 
      ap (\ (h : ∀ {A} {a : A} → Applicative.pure AT a == return a) → monad AT return _>>=_ _ _ _ h _) (λ≃i (λ _ → λ≃i (λ _ → HSet-UIP (sT _) _ _ _ _))) ∘
      ap (\ (h : ∀ {A B} {f : T (A → B)} {a : T A} → Applicative._<*>_ AT f a == ( f >>= λ f' → a >>= λ a' → return (f' a'))) → monad AT return _>>=_ _ _ _ _ h) (λ≃i (λ _ → λ≃i (λ _ → λ≃i (λ _ → λ≃i (λ _ → HSet-UIP (sT _) _ _ _ _)))))

  module OldToNew {T : Type → Type} (MT : Old.Monad T) where
  
    open Old.Monad MT

    default-applicative : New.Applicative T
    default-applicative = record
                            { pure = return
                            ; _<*>_ = λ f a → _>>=_ f (λ f' → _>>=_ a (λ a' → return (f' a')))
                            ; pure-id = runit ∘ lunit
                            ; pure-comp = (ap (_>>=_ _) (λ≃ (λ _ → ! assoc ∘ ap (_>>=_ _) (λ≃ (λ _ → (! assoc ∘ ap (_>>=_ _) (λ≃ (λ x → ! lunit))) ∘ lunit)) ∘ assoc)) ∘ assoc) ∘ ap (flip _>>=_ _) (((ap (_>>=_ _) (λ≃ (λ x → lunit)) ∘ assoc) ∘ lunit) ∘ assoc)
                            ; apply-pure = lunit ∘ lunit
                            ; apply-to-pure = ! lunit ∘ ap (_>>=_ _) (λ≃ (λ f' → lunit))
                            }

    new-monad : New.App⇒Monad T
    new-monad = record
                  { AT = default-applicative
                  ; return = return
                  ; _>>=_ = _>>=_
                  ; lunit = lunit
                  ; runit = runit
                  ; assoc = assoc
                  ; return-pure = id
                  ; <*>-ap = id
                  }
    
  module NewToOld {T : Type → Type} (MT : New.App⇒Monad T) where
    
    open New.App⇒Monad MT

    old-monad : Old.Monad T
    old-monad = record { return = return ; _>>=_ = _>>=_ ; lunit = lunit ; runit = runit ; assoc = assoc }


  oldnewold : {T : Type → Type} (MT : Old.Monad T) → NewToOld.old-monad (OldToNew.new-monad MT) == MT
  oldnewold MT = id

  newoldnew : {T : Type → Type} (sT : (A : Type) → HSet (T A)) (MT : New.App⇒Monad T) → OldToNew.new-monad (NewToOld.old-monad MT) == MT
  newoldnew sT MT = New.monad-hset= sT id id


  eqv : {T : Type → Type} (sT : (A : Type) → HSet (T A))
        → Equiv (Old.Monad T) (New.App⇒Monad T)
  eqv sT = improve (hequiv OldToNew.new-monad NewToOld.old-monad oldnewold (newoldnew sT))

  
