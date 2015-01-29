-- Prove pi1(S1) by showing that loop^ is 0-connected;
-- should be the same template as Blakers-Massey

{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.cubical.Cubical
open ConnectedMap
open Int
open Truncation

module homotopy.blakersmassey.Pi1S1Connected where

  open S¹ using (S¹-elimo; S¹; S¹-rec)

  apΣo : {A A' : Type} {B : A → Type} {B' : A' → Type}
        (a : A ≃ A')
        (b : PathOver (\ (X : Type) → (x : X) → Type) a B B')
      → Σ B ≃ Σ B'
  apΣo .id id = id

  coe-apΣo : {A A' : Type} {B : A → Type} {B' : A' → Type}
           (a : A == A')
           (b : PathOver (\ (X : Type) → (x : X) → Type) a B B')
           (p : Σ B)
           → (coe (apΣo a b) p) == (coe a (fst p) , coe (coe PathOverΠ-NDrange b _ _ (PathOver-transport-right (λ X → X) a)) (snd p))
  coe-apΣo .id id p = ap (λ x → fst p , x) {!!}

  ap-uncurryd-NDrange : {A : Type} {B : A → Type} {C : Type}
                (f : (x : A) → B x → C) {a0 a1 : A} {b0 : B a0} {b1 : B a1} (α : a0 == a1) (β : PathOver B α b0 b1)
                → ap (uncurryd f) (pair= α β) == coe PathOverΠ-NDrange (apdo f α) _ _ β 
  ap-uncurryd-NDrange _ .id id = {!!}

  loop^ : Int → Path S¹.base S¹.base
  loop^ Zero        = id
  loop^ (Pos One)   = S¹.loop
  loop^ (Pos (S n)) = S¹.loop ∘ loop^ (Pos n)
  loop^ (Neg One)   = ! S¹.loop
  loop^ (Neg (S n)) = ! S¹.loop ∘ loop^ (Neg n)

  succ-is-∘ : (n : _) → loop^ (succ n) == S¹.loop ∘ loop^ n
  succ-is-∘ (Pos n) = id
  succ-is-∘ (Zero) = id
  succ-is-∘ (Neg One) = ! (!-inv-r S¹.loop)
  succ-is-∘ (Neg (S n)) = ! (!-inv-r-front S¹.loop (loop^ (Neg n)))

  pred-is-∘ : (n : _) → loop^ (pred n) == (! S¹.loop) ∘ loop^ n
  pred-is-∘ (Pos One) = ! (!-inv-l S¹.loop)
  pred-is-∘ (Pos (S n)) = ! (!-inv-l-front S¹.loop (loop^ (Pos n)))
  pred-is-∘ (Zero) = id
  pred-is-∘ (Neg n) = id
  -- alternate definition:
  -- ! (!-inv-l-front S¹.loop (loop^ (pred n))) · ap (λ x → ! S¹.loop ∘ x) (! (succ-is-∘ (pred n))) · ap (λ x → ! S¹.loop ∘ loop^ x) (IsEquiv.β (snd succEquiv) n)

  Codes-eqv-2-lr : {p q : S¹.base == S¹.base} (s : PathOver (\ x -> S¹.base == x) S¹.loop p q) 
                {x y : Int} (e : PathOver (\ X → X) (ua succEquiv) x y) 
                → (Path (loop^ x) p) → (Path (loop^ y) q)
  Codes-eqv-2-lr {q = q} s {x} {y} e id = ((over-to-hom/left s ∘ ! (over-to-hom/left {A = Path S¹.base} {δ = S¹.loop} (PathOverPathFrom.in-PathOver-= ∘-square))) ∘ succ-is-∘ x) ∘ ! (ap loop^ (over-to-hom/left e ∘ ap≃ (! (type≃β succEquiv))))

  Codes-eqv-2' : {p q : S¹.base == S¹.base} (s : PathOver (\ x -> S¹.base == x) S¹.loop p q) 
                {x y : Int} (e : PathOver (\ X → X) (ua succEquiv) x y) 
                → Equiv (Path (loop^ x) p) (Path (loop^ y) q)
  Codes-eqv-2' s e = (improve (hequiv (Codes-eqv-2-lr s e) {!!} {!!} {!!}))

  Codes-eqv-2 : {p q : S¹.base == S¹.base} (s : PathOver (\ x -> S¹.base == x) S¹.loop p q) 
                {x y : Int} (e : PathOver (\ X → X) (ua succEquiv) x y) 
                → (Path (loop^ x) p) == (Path (loop^ y) q)
  Codes-eqv-2 s e = ua (Codes-eqv-2' s e)

  Codes-eqv : (p q : S¹.base == S¹.base) (s : PathOver (\ x -> S¹.base == x) S¹.loop p q) 
            → (HFiber loop^ p) == (HFiber loop^ q)
  Codes-eqv p q s = apΣo (ua succEquiv) (coe (! PathOverΠ-NDrange) (λ x y e → Codes-eqv-2 s e))

  CodesFor : (x : S¹) → S¹.base == x → Type
  CodesFor = S¹-elimo _ (λ p → Trunc (tl 0) (HFiber loop^ p))
                        (coe (! PathOverΠ-NDrange) (λ p q s → ap (Trunc (tl 0)) (Codes-eqv p q s)))

  CodesFor' : (Σ \ x → S¹.base == x) → Type
  CodesFor' (x , y) = CodesFor x y

  lemma : ∀ {p q : Path S¹.base S¹.base} (r : (PathOver (\ y → S¹.base == y) S¹.loop p q))
        → ap CodesFor' (pair= S¹.loop r) == ap (Trunc (tl 0)) (Codes-eqv _ _ r)
  lemma r = ap CodesFor' (pair= S¹.loop r) ≃〈 ap-uncurryd-NDrange CodesFor S¹.loop r 〉 
            coe PathOverΠ-NDrange (apdo CodesFor S¹.loop) _ _ r ≃〈 ap (λ z → coe PathOverΠ-NDrange z _ _ r) (S¹.βloop/elimo _ _ _) 〉
            coe PathOverΠ-NDrange (coe (! PathOverΠ-NDrange) (λ p q s → ap (Trunc (tl 0)) (Codes-eqv p q s))) _ _ r ≃〈 ap (λ z → z _ _ r) (IsEquiv.β (snd (coe-equiv PathOverΠ-NDrange)) _) 〉
            ap (Trunc (tl 0)) (Codes-eqv  _ _ r) ∎

  transport-CodesFor'-loop : ∀ {n} → coe (ap CodesFor' (pair= S¹.loop (PathOverPathFrom.in-PathOver-= ∘-square))) [ n , id ] == [ succ n , succ-is-∘ n ]
  transport-CodesFor'-loop {n} = coe (ap CodesFor' (pair= S¹.loop (PathOverPathFrom.in-PathOver-= ∘-square))) [ n , id ] ≃〈 ap (λ z → coe z [ n , id ]) (lemma (PathOverPathFrom.in-PathOver-= ∘-square)) 〉
                                 coe (ap (Trunc (tl 0)) (Codes-eqv  _ _ (PathOverPathFrom.in-PathOver-= ∘-square))) [ n , id ] ≃〈 {!!} 〉
                                 [ coe (Codes-eqv  _ _ (PathOverPathFrom.in-PathOver-= ∘-square)) (n , id) ] ≃〈 ap [_] (coe-apΣo (ua succEquiv) (coe (! PathOverΠ-NDrange) (λ x y e → Codes-eqv-2 (PathOverPathFrom.in-PathOver-= ∘-square) e)) (n , id)) 〉
                                 [ coe (ua succEquiv) n , coe (coe PathOverΠ-NDrange (coe (! PathOverΠ-NDrange) (λ x y e → Codes-eqv-2 {(loop^ n)} {(S¹.loop ∘ loop^ n)} (PathOverPathFrom.in-PathOver-= ∘-square) {x} {y} e)) n (transport (λ X → X) (ua succEquiv) n) (PathOver-transport-right (λ X → X) (ua succEquiv))) id ] ≃〈 {!!} 〉
                                 [ coe (ua succEquiv) n , coe (Codes-eqv-2  (PathOverPathFrom.in-PathOver-= ∘-square) (PathOver-transport-right (λ X → X) (ua succEquiv))) id ] ≃〈 ap [_] (pair= (ap≃ (type≃β succEquiv)) (PathOver=.in-PathOver-= s)) 〉
                                 [ succ n , succ-is-∘ n ] ∎ where
    reduce : Codes-eqv-2-lr (PathOverPathFrom.in-PathOver-= ∘-square) (PathOver-transport-right (λ X → X) (ua succEquiv)) id == 
             succ-is-∘ n ∘ ! (ap loop^ (ap≃ (! (type≃β succEquiv))))
    reduce = {!!} -- (! (((over-to-hom/left (PathOverPathFrom.in-PathOver-= ∘-square) ∘ ! (transport-Path-right S¹.loop _)) ∘ succ-is-∘ n)
               --             ∘ ! (ap loop^ (over-to-hom/left (PathOver-transport-right (λ X → X) (ua succEquiv)) ∘ ap≃ (! (type≃β succEquiv))))
               --             ≃〈 {!!} 〉 
               --           ((over-to-hom/left (PathOverPathFrom.in-PathOver-= ∘-square) ∘ ! (transport-Path-right S¹.loop _)) ∘ succ-is-∘ n)
               --             ∘ ! (ap loop^ (ap≃ (! (type≃β succEquiv)))) ≃〈 {!!} 〉 
               --           (succ-is-∘ n ∘ ! (ap loop^ (ap≃ (! (type≃β succEquiv)))) ∎)))
  
    s : Square
      (coe (Codes-eqv-2 (PathOverPathFrom.in-PathOver-= ∘-square) (PathOver-transport-right (λ X → X) (ua succEquiv))) id)
      (ap (λ z → loop^ z) (ap≃ (type≃β succEquiv)))
      (ap (λ _ → S¹.loop ∘ loop^ n) (ap≃ (type≃β succEquiv)))
      (succ-is-∘ n)
    s = whisker-square (! (ap≃ (type≃β (Codes-eqv-2' (PathOverPathFrom.in-PathOver-= ∘-square) (PathOver-transport-right (λ X → X) (ua succEquiv)))))) id (! (ap-constant _ (ap≃ (type≃β succEquiv)))) id 
        (whisker-square (! reduce) id id id (disc-to-square {!!})) 
  

  transport-CodesFor'-!loop : ∀ {n} → coe (ap CodesFor' (pair= (! S¹.loop) (PathOverPathFrom.in-PathOver-= ∘-square))) [ n , id ] == [ pred n , pred-is-∘ n ]
  transport-CodesFor'-!loop = {!!}

                {-
                encode S¹.base S¹.loop ≃〈 {!!} 〉 
                transport CodesFor' (pair= S¹.loop (PathOverPathFrom.in-PathOver-= connection)) [ Zero , id ] ≃〈 {!!} 〉 
                coe (ap CodesFor' (pair= S¹.loop (PathOverPathFrom.in-PathOver-= connection))) [ Zero , id ] ≃〈 {!!} 〉 
                coe
                    (coe PathOverΠ-NDrange (apdo CodesFor S¹.loop) _ _ (PathOverPathFrom.in-PathOver-= connection))
                  [ Zero , id ] ≃〈 {!!} 〉 
                coe (ap (Trunc (tl 0)) (Codes-eqv _ _ (PathOverPathFrom.in-PathOver-= connection)))
                  [ Zero , id ] ≃〈 {!!} 〉 
                [ coe (Codes-eqv _ _ (PathOverPathFrom.in-PathOver-= connection)) (Zero , id) ] ≃〈 {!!} 〉 
                [ (coe (ua succEquiv) Zero) , coe {!!} id ] ≃〈 {!!} 〉 
                [ Pos One , id ] ∎
                -}

  encode : (x : S¹) (p : S¹.base == x) → (CodesFor x p)
  encode x p = 
    coe (ap CodesFor' (pair= p (PathOverPathFrom.in-PathOver-= connection)))
        [ Zero , id ]

  -- FIXME generalize
  encode-∘ : {x y : S¹} (q : x == y) (p : S¹.base == x) → 
    encode _ (q ∘ p) == coe (ap CodesFor' (pair= q (PathOverPathFrom.in-PathOver-= ∘-square))) (encode _ p)
  encode-∘ id id = id

  encode-loop : encode S¹.base S¹.loop == [ Pos One , id ]
  encode-loop = transport-CodesFor'-loop {n = Zero}

  encode-loop^ : (k : Int) → Path {Trunc (tl 0) (HFiber loop^ (loop^ k))} 
                                  (encode S¹.base (loop^ k))
                                  [ k , id ]
  encode-loop^ (Pos One) = encode-loop
  encode-loop^ (Pos (S n)) = encode-∘ S¹.loop (loop^ (Pos n)) · 
                             ap (coe (ap CodesFor' (pair= S¹.loop (PathOverPathFrom.in-PathOver-= ∘-square)))) (encode-loop^ (Pos n)) ·
                             transport-CodesFor'-loop {n = Pos n}
  encode-loop^ Zero = id
  encode-loop^ (Neg One) = transport-CodesFor'-!loop {Zero}
  encode-loop^ (Neg (S n)) = encode-∘ (! S¹.loop) (loop^ (Neg n)) ·
                             ap (coe (ap CodesFor' (pair= (! S¹.loop) (PathOverPathFrom.in-PathOver-= ∘-square)))) (encode-loop^ (Neg n)) · 
                             transport-CodesFor'-!loop {Neg n}

  -- path induction on the proof that fst f decodes to p
  encode-decode-base : (p : S¹.base == S¹.base) (f : HFiber loop^ p) → Path (encode S¹.base p) [ f ]  
  encode-decode-base ._ (k , id) = encode-loop^ k

  -- induction on x, then the code
  encode-decode : (x : S¹) (p : S¹.base == x) (y : CodesFor x p) → Path (encode x p) y
  encode-decode = S¹-elimo _ (\ p → (Trunc-elim _ (λ _ → path-preserves-level Trunc-level) (encode-decode-base p)))
                             (in-PathOverΠ (λ p q α → in-PathOverΠ (λ x y β → hom-to-over/left _ (HSet-UIP Trunc-level _ _ _ _)))) 

  Codes-contr : (x : S¹) (p : S¹.base == x) → Contractible (CodesFor x p)
  Codes-contr x p = encode x p , encode-decode x p

  thm' : (α : S¹.base == S¹.base) → Contractible (Trunc (tl 0) (HFiber loop^ α))
  thm' α = Codes-contr _ α

  thm : ConnectedMap (tl 0) loop^
  thm α = ntype (thm' α)

{-
  module ImproveC {n}{A}{B} (f : A → B) where

    l' : (b : B) → Contractible (HFiber (Trunc-func {n} f) [ b ]) → (Trunc n (HFiber f b)) 
    l' b ((a , pa) , eqt) = {!snd ct!} -- would need Path{Trunc n} (Trunc-func f a) [ b ] → Trunc n (Path (f a) b) but that decrements the level

    l : (b : B) → Contractible (HFiber (Trunc-func {n} f) [ b ]) → Contractible (Trunc n (HFiber f b)) 
    l b = {!!}

  improvec : ∀ {n A B} (f : A → B) → (IsWEq {Trunc n A} {Trunc n B} (Trunc-func f)) → ConnectedMap n f
  improvec f ef y = ntype (ImproveC.l f y (ef [ y ]))
-}
