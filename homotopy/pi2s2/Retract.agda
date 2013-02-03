{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open import homotopy.Hopf
open Paths

module homotopy.Pi2S2.Retract where

  private 
    module S² = S²1
  open S² using (S² ; S²-rec ; S²-elim; S²-fibration/βloop)
  open S¹ using (S¹ ; S¹-rec ; S¹-elim)

  encode : {x : S²} -> Path{S²} S².base x -> H x
  encode {x} α = transport H α S¹.base

  encode' : Path{S²} S².base S².base -> S¹
  encode' = encode{S².base}
  
  private
   -- for some reason, making this abstract gives lots of unsolved metas
   transport-H-loop2' : (ap encode' S².loop) ≃ S¹.loop
   transport-H-loop2' = 
     (ap encode' S².loop)                  ≃〈 ap-by-equals (λ α → ap≃ (transport-ap-assoc H α) {S¹.base}) S².loop 〉
     id ∘ (ap (coe-base o ap H) S².loop)   ≃〈 ∘-unit-l _ 〉
     (ap (coe-base o ap H) S².loop)        ≃〈 ap-o coe-base (ap H) S².loop 〉
     (ap coe-base (ap (ap H) S².loop))     ≃〈 ap (λ y → ap coe-base y) (S²-fibration/βloop S¹-loops) 〉
     (ap coe-base
         (loop-family->id-loop S¹-loops)) ≃〈 id 〉
     (ap coe-base
       ((type≃η id)
        ∘ ap ua (loop-family->id-equiv-loop S¹-loops)
        ∘ ! (type≃η id)))                         ≃〈 ap-∘3 coe-base (type≃η id) (ap ua (loop-family->id-equiv-loop S¹-loops)) (! (type≃η id)) 〉
     (ap coe-base (type≃η id) ∘
      ap coe-base (ap ua (loop-family->id-equiv-loop S¹-loops)) ∘ 
      ap coe-base (! (type≃η id)))                ≃〈 ap (λ x → ap coe-base (type≃η id) ∘ x ∘ ap coe-base (! (type≃η id))) (! (ap-o coe-base ua (loop-family->id-equiv-loop S¹-loops))) 〉
     (ap coe-base (type≃η id) ∘
      ap (coe-base o ua) (loop-family->id-equiv-loop S¹-loops) ∘
      ap coe-base (! (type≃η id)))                ≃〈 ap (λ x → ap coe-base (type≃η id) ∘ x ∘ ap coe-base (! (type≃η id))) (ap-by-equals (λ e → ap≃ (type≃β e) {S¹.base}) (loop-family->id-equiv-loop S¹-loops)) 〉
     (ap coe-base (type≃η id) ∘
      (! (ap≃ (type≃β id-equiv)) ∘ 
       ap (\ (e : Equiv S¹ S¹) -> (fst e) S¹.base) (loop-family->id-equiv-loop S¹-loops) ∘
       ap≃ (type≃β id-equiv)) ∘ 
      ap coe-base (! (type≃η id)))                ≃〈 rassoc-1-3-1 (ap coe-base (type≃η id))  (! (ap≃ (type≃β id-equiv))) (ap (\ (e : Equiv S¹ S¹) -> (fst e) S¹.base) (loop-family->id-equiv-loop S¹-loops)) (ap≃ (type≃β id-equiv)) (ap coe-base (! (type≃η id))) 〉 
     (ap coe-base (type≃η id) ∘
      ! (ap≃ (type≃β id-equiv)) ∘ 
      ap (\ (e : Equiv S¹ S¹) -> (fst e) S¹.base) (loop-family->id-equiv-loop S¹-loops) ∘
      ap≃ (type≃β id-equiv) ∘ 
      ap coe-base (! (type≃η id)))                 ≃〈 ap (λ z → ap coe-base (type≃η id) ∘ ! (ap≃ (type≃β id-equiv)) ∘ z ∘ ap≃ (type≃β id-equiv) ∘ ap coe-base (! (type≃η id))) sts 〉
     (ap coe-base (type≃η id) ∘
      ! (ap≃ (type≃β id-equiv)) ∘ 
      S¹.loop ∘
      ap≃ (type≃β id-equiv) ∘ 
      ap coe-base (! (type≃η id)))                 ≃〈 ap (λ x → x ∘ ! (ap≃ (type≃β id-equiv)) ∘ S¹.loop ∘ ap≃ (type≃β id-equiv) ∘ ap coe-base (! (type≃η id))) rewrite-β 〉
     ((ap≃ (type≃β id-equiv)) ∘
      ! (ap≃ (type≃β id-equiv)) ∘ 
      S¹.loop ∘
      ap≃ (type≃β id-equiv) ∘ 
      ap coe-base (! (type≃η id)))                 ≃〈 !-inv-r-front _ _ 〉
     (S¹.loop ∘
      ap≃ (type≃β id-equiv) ∘ 
      ap coe-base (! (type≃η id)))                 ≃〈 ap (λ x → S¹.loop ∘ ap≃ (type≃β id-equiv) ∘ x) (ap-! coe-base (type≃η id)) 〉
     (S¹.loop ∘
      ap≃ (type≃β id-equiv) ∘ 
      ! (ap coe-base (type≃η id)))                 ≃〈 ap (λ x → S¹.loop ∘ ap≃ (type≃β id-equiv) ∘ ! x) rewrite-β 〉
     (S¹.loop ∘
      ap≃ (type≃β id-equiv) ∘ 
      ! (ap≃ (type≃β id-equiv)))       ≃〈 !-inv-r-back S¹.loop (ap≃ (type≃β id-equiv)) 〉
     S¹.loop ∎ 
    where coe-base = (λ α → transport (\ x -> x) α S¹.base)
     
          sts : ap (\ (e : Equiv S¹ S¹) -> (fst e) S¹.base) (loop-family->id-equiv-loop S¹-loops) 
              ≃ S¹.loop
          sts = ap (λ (e : Equiv S¹ S¹) → fst e S¹.base) (loop-family->id-equiv-loop S¹-loops) ≃〈 id 〉 
                ap ((λ f → f S¹.base) o fst) (loop-family->id-equiv-loop S¹-loops) ≃〈 ap-o (λ f → f S¹.base) fst (loop-family->id-equiv-loop S¹-loops) 〉 
                ap (λ f → f S¹.base) (ap fst (loop-family->id-equiv-loop S¹-loops)) ≃〈 ap (λ z → ap (λ f → f S¹.base) z) (Σ≃β1 (λ≃ S¹-loops) _) 〉 
                ap (λ f → f S¹.base) (λ≃ S¹-loops) ≃〈 Π≃β S¹-loops 〉 
                S¹.loop ∎
  
          rewrite-β : (ap (λ α → transport (\ x -> x) α S¹.base) (type≃η id)) ≃ ap≃ (type≃β id-equiv)
          rewrite-β = ap (λ α → transport (λ x → x) α S¹.base) (type≃η id) ≃〈 id 〉
           ap ((\ f → f S¹.base) o (\ α → transport (λ x → x) α)) (type≃η id) ≃〈 ap-o (λ f → f S¹.base) (λ α → transport (λ x → x) α) (type≃η id) 〉
           ap (\ f → f S¹.base) (ap (transport (λ x → x)) (type≃η id)) ≃〈 ap (λ x → ap≃ x) (type≃-coh id) 〉
           ap (\ f -> f S¹.base) (type≃β id-equiv) ≃〈 id 〉 
           ap≃ (type≃β id-equiv) ∎

  abstract
   transport-H-loop2 : (ap encode' S².loop) ≃ S¹.loop
   transport-H-loop2 = transport-H-loop2'

   transport-H-!loop2 : (ap encode' (! S².loop)) ≃ ! S¹.loop
   transport-H-!loop2 = ap ! transport-H-loop2 ∘ ap-! encode' S².loop

  decode' : S¹ → Path S².base S².base
  decode' = S¹-rec id S².loop

  encode-decode' : (x : S¹) -> encode (decode' x) ≃ x
  encode-decode' = S¹-elim (\ x -> encode (decode' x) ≃ x) 
                           id 
                           respects-loop
                           where
   abstract
    respects-loop : transport (λ x → encode (decode' x) ≃ x) S¹.loop id ≃ id
    respects-loop = (transport (λ x → encode (decode' x) ≃ x) S¹.loop id           ≃〈 transport-Path (encode o decode') (λ x → x) S¹.loop id 〉 
                     ap (\ x -> x) S¹.loop ∘ id ∘ ! (ap (encode o decode') S¹.loop) ≃〈 ap (λ y → y ∘ id ∘ ! (ap (encode o decode') S¹.loop)) (ap-id S¹.loop) 〉 
                     S¹.loop ∘ id ∘ ! (ap (encode o decode') S¹.loop)               ≃〈 ap (λ y → S¹.loop ∘ y) (∘-unit-l (! (ap (encode o decode') S¹.loop))) 〉 
                     S¹.loop ∘ ! (ap (encode o decode') S¹.loop)                    ≃〈 ap (λ y → S¹.loop ∘ ! y) STS 〉 
                     S¹.loop ∘ ! S¹.loop                                            ≃〈 !-inv-r S¹.loop 〉 
                     id ∎) where
      STS : (ap (encode o decode') S¹.loop) ≃ S¹.loop
      STS = (ap (encode o decode') S¹.loop)  ≃〈 ap-o encode decode' S¹.loop 〉 
            (ap encode (ap decode' S¹.loop)) ≃〈 ap (λ y → ap encode y) (S¹.βloop/rec id S².loop) 〉 
            (ap encode (S².loop))            ≃〈 transport-H-loop2 〉 
            S¹.loop ∎

  {-
  module NeedTruncation where

    -- FIXME: special case of ap-λ and ap-app ?
    ap-of-o : {A B C D : _} (f : A → B → C) (g : A → D → B) {M N : A} (α : M ≃ N)
            → ap (\ x -> f x o g x) α ≃ λ≃ (λ x → ap2 (λ f' x' → f' x') (ap f α) (ap (λ y → g y x) α))
    ap-of-o f g id = Π≃η id

    ap≃₁→ : {A B : Type} {f g : A → B} {x y : A} → f ≃ g → x ≃ y → f x ≃ g y
    ap≃₁→ α β = ap2 (\ f x -> f x) α β

    ap≃₁→-β1 : {A B : Type} {f g : A → B} {x y : A} → (α : (x : _) → f x ≃ g x) (β : x ≃ y) 
               → ap≃₁→ (λ≃ α) β ≃ ap g β ∘ (α x) 
    ap≃₁→-β1 α id = {!!}

    decode : {x : S²} -> H x → Path{S²} S².base x
    decode{x} = S²-elim (λ x' → H x' → Path {S²} S².base x')
                        decode'
                        (transport (λ y → Path (transport (λ x' → H x' → Path S².base x') y decode') decode') S².loop id ≃〈 transport-Path (λ y → transport (λ x' → H x' → Path S².base x') y decode') (λ y → decode') S².loop id 〉 
                         (ap (\ _ -> decode') S².loop)
                         ∘ id
                         ∘ ! (ap (\ y -> (transport (λ x' → H x' → Path S².base x') y decode')) S².loop) ≃〈 ap (λ x' → ap (λ _ → decode') S².loop ∘ x') (∘-unit-l (! (ap (λ y → transport (λ x' → H x' → Path S².base x') y decode') S².loop))) 〉 
                         (ap (\ _ -> decode') S².loop)
                         ∘ ! (ap (\ y -> (transport (λ x' → H x' → Path S².base x') y decode')) S².loop) ≃〈 ap (λ x' → x' ∘ ! (ap (λ y → transport (λ x0 → H x0 → Path S².base x0) y decode') S².loop)) (ap-constant decode' S².loop) 〉 
                         id
                         ∘ ! (ap (\ y -> (transport (λ x' → H x' → Path S².base x') y decode')) S².loop) ≃〈 ∘-unit-l (! (ap (λ y → transport (λ x' → H x' → Path S².base x') y decode') S².loop)) 〉 
                         ! (ap (\ y -> (transport (λ x' → H x' → Path S².base x') y decode')) S².loop) ≃〈 ap ! STS 〉 
                         id ∎)
                        x where

              STS : (ap (\ y -> (transport (λ x' → H x' → Path S².base x') y decode')) S².loop) ≃ id {_} {decode'}
              STS = ap (λ y → transport (λ x' → H x' → Path S².base x') y decode') S².loop ≃〈 ap-by-equals (λ α → transport-→ H (Path S².base) α decode') S².loop 〉 
                    id ∘ ap (λ α → transport (Path S².base) α o decode' o transport H (! α)) S².loop ≃〈 ∘-unit-l (ap (λ α → transport (Path S².base) α o decode' o transport H (! α)) S².loop) 〉 
                    ap (λ α → transport (Path S².base) α o decode' o transport H (! α)) S².loop ≃〈 ap-of-o (λ α → transport (Path S².base) α o decode') (λ α → transport H (! α)) S².loop 〉 
                    λ≃ (\ (x : S¹) → ap2 (\ f x -> f x) (ap (\ α' -> transport (Path S².base) α' o decode') S².loop)
                                                        (ap (\ β -> transport H (! β) x) S².loop)) ≃〈 ap λ≃ (λ≃ STS2) 〉 
                    λ≃ (\ x -> id) ≃〈 ! (Π≃η id) 〉 
                    id ∎ 
               where
                STS2 : (x : S¹) → ap2 (\ f x -> f x) (ap (\ α' -> transport (Path S².base) α' o decode') S².loop)
                                                         (ap (\ β -> transport H (! β) x) S².loop)
                                 ≃ id
                STS2 = S¹-elim (\ x -> ap2 (\ f x -> f x) (ap (\ α' -> transport (Path S².base) α' o decode') S².loop)
                                                          (ap (\ β -> transport H (! β) x) S².loop) ≃ id) 
                               (ap2 (λ f x' → f x')
                                  (ap (λ α' → transport (Path S².base) α' o decode') S².loop)
                                  (ap (λ β → transport H (! β) S¹.base) S².loop) ≃〈 {!STS3!} 〉 
                               (ap2 (λ f x' → f x')
                                    (ap (λ α' → transport (Path S².base) α' o decode') S².loop)
                                    (! S¹.loop)) ≃〈 {!STS4!} 〉 
                               (ap2 (λ f x' → f x')
                                    (λ≃ (λ y → ap (λ α' → transport (Path S².base) α' (decode' y)) S².loop))
                                    (! S¹.loop)) ≃〈 {! naturality!} 〉
                               (ap decode' (! S¹.loop)
                                ∘ ap (λ α' → transport (Path S².base) α' (decode' S¹.base)) S².loop) ≃〈 {!!} 〉 
                               (! (ap decode' S¹.loop)
                                ∘ ap (λ α' → transport (Path S².base) α' (decode' S¹.base)) S².loop) ≃〈 {!!} 〉 
                               (! S².loop
                                ∘ ap (λ α' → transport (Path S².base) α' (decode' S¹.base)) S².loop) ≃〈 {!!} 〉 
                               (! S².loop
                                ∘ ap (λ α' → transport (Path S².base) α' id) S².loop) ≃〈 {!!} 〉 
                               (! S².loop
                                ∘ ap (λ α' → α' ∘ id) S².loop) ≃〈 {!!} 〉 
                               (! S².loop
                                ∘ S².loop) ≃〈 {!!} 〉 
                               (! S².loop
                                ∘ ap (λ α' → α') S².loop) ≃〈 {!!} 〉 
                               id ∎)
                               {!!}  -- ?1 is a Path{Path {Path {Path {S²} base base} (id {_} {base}) (id {_} {base})} something somethingelse} tra lala
                                     -- is that trivial in the truncation?
                 where 
                  STS3 : (ap (λ β → transport H (! β) S¹.base) S².loop) ≃ ! S¹.loop
                  STS3 = {!!} -- by analogy with above; can we derive it from that?

                  STS4 :   (ap (λ α' → transport (Path S².base) α' o decode') S².loop)
                         ≃ λ≃ (λ y → ap (λ α' → transport (Path S².base) α' (decode' y)) S².loop)
                  STS4 = (ap (λ α' → transport (Path S².base) α' o decode') S².loop) ≃〈 {!!} 〉
                         (ap (λ α' → (\ (y : S¹) → transport (Path S².base) α' (decode' y))) S².loop) ≃〈 {!!} 〉
                         (λ≃ (\ y -> (ap (\α' → transport (Path S².base) α' (decode' y))) S².loop)) ≃〈 {!!} 〉
                         (λ≃ (\ y -> (ap≃ (ap (\α' → transport (Path S².base) α') S².loop)
                                          {(decode' y)}))) ≃〈 {!!} 〉
                         (λ≃ (\ y -> (ap≃ (λ≃ (\β → ap (\ α' → transport (Path S².base) α' β) S².loop))
                                          {(decode' y)}))) ≃〈 {!!} 〉
                         (λ≃ (\ y -> (ap (\ α' → transport (Path S².base) α' (decode' y)) S².loop))) ∎


    decode-encode : {x : S²} (α : _) → decode{x} (encode{x} α) ≃ α
    decode-encode id = id
  
    impossible : HEquiv (Path{S²} S².base S².base) S¹
    impossible = hequiv encode decode decode-encode encode-decode'
  -}