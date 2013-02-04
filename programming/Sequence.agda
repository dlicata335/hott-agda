
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module programming.Sequence where

  listreduce : ∀ {A} -> Monoid A -> List A -> A
  listreduce M = ListM.fold `1 _⊙_ 
    where open Monoid M

  record Collection (Col : Type -> Type) : Type where
    field
      length   : ∀ {A} -> Col A -> Nat
      nth      : ∀ {A} -> Col A -> Nat -> Maybe A
      tabulate : ∀ {A} -> (Nat -> A) -> Nat -> Col A
      reduce   : ∀ {A} -> Monoid A -> Col A -> A
      map      : ∀ {A B} -> (A -> B) -> Col A -> Col B

  listOps : Collection List
  listOps = record { length = ListM.length; nth = ListM.nth; tabulate = ListM.tabulate; reduce = listreduce; map = ListM.map }

  module PSeq where
    postulate 
      Seq : Type -> Type
      ops : Collection Seq

      model  : Id {Σ Collection} (Seq , ops) (List , listOps)

    open Collection ops public
  
  -- abstraction isomorphism
  abs : PSeq.Seq ≃ List
  abs = fst≃ PSeq.model

  l2s : ∀ {A} -> List A -> PSeq.Seq A
  l2s{A} = transport (\ C -> C A) (! abs)

  s2l : ∀ {A} -> PSeq.Seq A -> List A
  s2l{A} = transport (\ C -> C A) abs

  transport-Collection : ∀ {C1 C2} (α : C1 ≃ C2) ->
                     transport Collection α
                   ≃ (λ c → record { length = transport (\ Col -> ∀ {A} -> Col A -> Nat) α (Collection.length c);
                                     nth = transport (λ Col → {A : _} → Col A → Nat → Maybe A) α (Collection.nth c); 
                                     tabulate = transport (λ Col → {A : _} → (Nat → A) → Nat → Col A) α (Collection.tabulate c); 
                                     reduce = transport (λ Col → {A : _} → Monoid A → Col A → A) α (Collection.reduce c); 
                                     map = transport (λ Col → {A B : _} → (A → B) → Col A → Col B) α (Collection.map c) })
  transport-Collection id = id

  -- using snd≃– might save the ap-! ? not sure what happened
  map≃ : ∀ {A B} -> 
                PSeq.map{A}{B}
              ≃ transport (\ C -> (A -> B) -> C A -> C B) (! abs) (ListM.map{A}{B})
  map≃{A}{B} = 
          (ap (λ x → transport (λ γ → (A → B) → γ A → γ B) x ListM.map) (ap-! fst PSeq.model) ∘
             ap≃i
             (transport-Π2i Set (λ Col B' → (A → B') → Col A → Col B')
              (ap fst (! PSeq.model)) (λ {B'} → ListM.map {A} {B'}))
             {B}) 
         ∘ ap≃i (ap≃i (transport-Π2i Set (\ Col A -> {B : Set} → (A → B) → Col A → Col B) (ap fst (! PSeq.model)) (\ {A}{B} -> ListM.map{A}{B})))  
         ∘ ap≃i
           (ap≃i
            (ap Collection.map
             (ap≃ (transport-Collection (ap fst (! PSeq.model))))
             ∘ ! (ap Collection.map (snd≃ (! PSeq.model)))))

  map≃' : ∀{A B} -> 
                PSeq.map{A}{B}
              ≃ (λ f → l2s o ListM.map f o s2l)
  map≃'{A}{B} = PSeq.map ≃〈 map≃ 〉
                transport (λ C → (A → B) → C A → C B) (! abs) ListM.map ≃〈 transport-Π2 (A → B) (λ C _ → C A → C B) (! abs) ListM.map 〉
                (λ f → transport (λ C → C A → C B) (! abs) (ListM.map f)) ≃〈 λ≃ (\ f -> transport-→ (\ C -> C A) (\ C -> C B) (! abs) (ListM.map f)) 〉
                (λ f ->   l2s
                        o (ListM.map f) 
                        o (transport (\ C -> C A) (! (! abs)))) ≃〈 ap (λ x → λ f → l2s o ListM.map f o transport (λ C → C A) x) (!-invol abs) 〉 
                (λ f ->   l2s
                        o (ListM.map f) 
                        o s2l) ∎

  s2l-l2s-inv : ∀ {A} -> (s2l o l2s) ≃ (\ (x : List A) -> x)
  s2l-l2s-inv{A} = s2l o l2s                        ≃〈 ! (transport-∘ (λ C → C A) abs (! abs)) 〉
                   transport (λ C → C A) (abs ∘ ! abs)  ≃〈 ap (λ x → transport (λ C → C A) x) (!-inv-r abs) 〉
                   (\ x -> x) ∎

  map-o : ∀ {A B C} {f : A -> B} {g : B -> C}
        -> PSeq.map (g o f) ≃ PSeq.map g o PSeq.map f
  map-o {A}{B}{C}{f = f}{g = g} = 
    PSeq.map (g o f)                 ≃〈 ap≃ map≃' 〉 

    l2s o ListM.map (g o f) o s2l   ≃〈 ap (λ x → l2s o x o s2l) (! (λ≃ ListM.fuse-map)) 〉 

    l2s o (ListM.map g o ListM.map f) o s2l ≃〈 id 〉 

      (l2s o ListM.map g)
    o (\ x -> x)
    o (ListM.map f o s2l)           ≃〈 ap (λ x → (l2s o ListM.map g) o x o ListM.map f o s2l) (! s2l-l2s-inv) 〉 

      (l2s o ListM.map g)
    o (s2l o l2s)
    o (ListM.map f o s2l)           ≃〈 id 〉 

      (l2s o ListM.map g o s2l)
    o (l2s o ListM.map f o s2l)     ≃〈 ! (ap2 (λ x y → x o y) (ap≃ map≃') (ap≃ map≃')) 〉 

    PSeq.map g o PSeq.map f 
    ∎