{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open import homotopy.Hopf
open Paths

module homotopy.Pi2S2 where

  private 
    module S² = S²1
  open S² using (S² ; S²-rec ; S²-elim)
  open S¹ using (S¹ ; S¹-rec ; S¹-elim)

  encode : {x : S²} -> Path{S²} S².base x -> H x
  encode {x} α = transport H α S¹.base

  encode' = encode{S².base}

  transport-H-loop2 : (ap encode' S².loop) ≃ S¹.loop
  transport-H-loop2 = 
    (ap encode' S².loop)                  ≃〈 ap-by-equals (λ α → ap≃ (transport-ap-assoc H α) {S¹.base}) S².loop 〉
    id ∘ (ap (coe-base o ap H) S².loop)   ≃〈 ∘-unit-l _ 〉
    (ap (coe-base o ap H) S².loop)        ≃〈 ap-o coe-base (ap H) S².loop 〉
    (ap coe-base (ap (ap H) S².loop))     ≃〈 ap (λ y → ap coe-base y) (S²-fibration/βloop S¹-loops) 〉
    (ap coe-base
        (loop-family->id-loop S¹-loops)) ≃〈 id 〉
    (ap coe-base
      (id-ua
       ∘ ap ua (loop-family->id-equiv-loop S¹-loops)
       ∘ ! id-ua))                         ≃〈 ap-∘3 coe-base id-ua (ap ua (loop-family->id-equiv-loop S¹-loops)) (! id-ua) 〉
    (ap coe-base id-ua ∘
     ap coe-base (ap ua (loop-family->id-equiv-loop S¹-loops)) ∘ 
     ap coe-base (! id-ua))                ≃〈 ap (λ x → ap coe-base id-ua ∘ x ∘ ap coe-base (! id-ua)) (! (ap-o coe-base ua (loop-family->id-equiv-loop S¹-loops))) 〉
    (ap coe-base id-ua ∘
     ap (coe-base o ua) (loop-family->id-equiv-loop S¹-loops) ∘
     ap coe-base (! id-ua))                ≃〈 ap (λ x → ap coe-base id-ua ∘ x ∘ ap coe-base (! id-ua)) (ap-by-equals (λ e → ap≃ (transport-ua e) {S¹.base}) (loop-family->id-equiv-loop S¹-loops)) 〉
    (ap coe-base id-ua ∘
     (! (ap≃ (transport-ua id-equiv)) ∘ 
      ap (\ (e : Equiv S¹ S¹) -> (fst e) S¹.base) (loop-family->id-equiv-loop S¹-loops) ∘
      ap≃ (transport-ua id-equiv)) ∘ 
     ap coe-base (! id-ua))                ≃〈 rassoc-1-3-1 (ap coe-base id-ua)  (! (ap≃ (transport-ua id-equiv))) (ap (\ (e : Equiv S¹ S¹) -> (fst e) S¹.base) (loop-family->id-equiv-loop S¹-loops)) (ap≃ (transport-ua id-equiv)) (ap coe-base (! id-ua)) 〉 
    (ap coe-base id-ua ∘
     ! (ap≃ (transport-ua id-equiv)) ∘ 
     ap (\ (e : Equiv S¹ S¹) -> (fst e) S¹.base) (loop-family->id-equiv-loop S¹-loops) ∘
     ap≃ (transport-ua id-equiv) ∘ 
     ap coe-base (! id-ua))                 ≃〈 ap (λ z → ap coe-base id-ua ∘ ! (ap≃ (transport-ua id-equiv)) ∘ z ∘ ap≃ (transport-ua id-equiv) ∘ ap coe-base (! id-ua)) sts 〉
    (ap coe-base id-ua ∘
     ! (ap≃ (transport-ua id-equiv)) ∘ 
     S¹.loop ∘
     ap≃ (transport-ua id-equiv) ∘ 
     ap coe-base (! id-ua))                 ≃〈 ap (λ x → x ∘ ! (ap≃ (transport-ua id-equiv)) ∘ S¹.loop ∘ ap≃ (transport-ua id-equiv) ∘ ap coe-base (! id-ua)) rewrite-β 〉
    ((ap≃ (transport-ua id-equiv)) ∘
     ! (ap≃ (transport-ua id-equiv)) ∘ 
     S¹.loop ∘
     ap≃ (transport-ua id-equiv) ∘ 
     ap coe-base (! id-ua))                 ≃〈 !-inv-r-front _ _ 〉
    (S¹.loop ∘
     ap≃ (transport-ua id-equiv) ∘ 
     ap coe-base (! id-ua))                 ≃〈 ap (λ x → S¹.loop ∘ ap≃ (transport-ua id-equiv) ∘ x) (ap-! coe-base id-ua) 〉
    (S¹.loop ∘
     ap≃ (transport-ua id-equiv) ∘ 
     ! (ap coe-base id-ua))                 ≃〈 ap (λ x → S¹.loop ∘ ap≃ (transport-ua id-equiv) ∘ ! x) rewrite-β 〉
    (S¹.loop ∘
     ap≃ (transport-ua id-equiv) ∘ 
     ! (ap≃ (transport-ua id-equiv)))       ≃〈 !-inv-r-back S¹.loop (ap≃ (transport-ua id-equiv)) 〉
    S¹.loop ∎ 
   where coe-base = (λ α → transport (\ x -> x) α S¹.base)
    
         sts : ap (\ (e : Equiv S¹ S¹) -> (fst e) S¹.base) (loop-family->id-equiv-loop S¹-loops) 
             ≃ S¹.loop
         sts = ap (λ (e : Equiv S¹ S¹) → fst e S¹.base) (loop-family->id-equiv-loop S¹-loops) ≃〈 id 〉 
               ap ((λ f → f S¹.base) o fst) (loop-family->id-equiv-loop S¹-loops) ≃〈 ap-o (λ f → f S¹.base) fst (loop-family->id-equiv-loop S¹-loops) 〉 
               ap (λ f → f S¹.base) (ap fst (loop-family->id-equiv-loop S¹-loops)) ≃〈 ap (λ z → ap (λ f → f S¹.base) z) (Σ≃β1 (λ≃ S¹-loops) _) 〉 
               ap (λ f → f S¹.base) (λ≃ S¹-loops) ≃〈 Π≃β S¹-loops 〉 
               S¹.loop ∎

         rewrite-β : (ap (λ α → transport (\ x -> x) α S¹.base) id-ua) ≃ ap≃ (transport-ua id-equiv)
         rewrite-β = ap (λ α → transport (λ x → x) α S¹.base) id-ua ≃〈 id 〉
          ap ((\ f → f S¹.base) o (\ α → transport (λ x → x) α)) id-ua ≃〈 ap-o (λ f → f S¹.base) (λ α → transport (λ x → x) α) id-ua 〉
          ap (\ f → f S¹.base) (ap (transport (λ x → x)) id-ua) ≃〈 ap (λ x → ap≃ x) id-ua-transport-ua 〉
          ap (\ f -> f S¹.base) (transport-ua id-equiv) ≃〈 id 〉 
          ap≃ (transport-ua id-equiv) ∎

  decode' : S¹ → Path S².base S².base
  decode' = S¹-rec id S².loop

  encode-decode' : (x : S¹) -> encode (decode' x) ≃ x
  encode-decode' = S¹-elim (\ x -> encode (decode' x) ≃ x) 
                           id 
                           (transport (λ x → encode (decode' x) ≃ x) S¹.loop id           ≃〈 transport-Path (encode o decode') (λ x → x) S¹.loop id 〉 
                            ap (\ x -> x) S¹.loop ∘ id ∘ ! (ap (encode o decode') S¹.loop) ≃〈 ap (λ y → y ∘ id ∘ ! (ap (encode o decode') S¹.loop)) (ap-id S¹.loop) 〉 
                            S¹.loop ∘ id ∘ ! (ap (encode o decode') S¹.loop)               ≃〈 ap (λ y → S¹.loop ∘ y) (∘-unit-l (! (ap (encode o decode') S¹.loop))) 〉 
                            S¹.loop ∘ ! (ap (encode o decode') S¹.loop)                    ≃〈 ap (λ y → S¹.loop ∘ ! y) sts 〉 
                            S¹.loop ∘ ! S¹.loop                                            ≃〈 !-inv-r S¹.loop 〉 
                            id ∎) where
                 sts : (ap (encode o decode') S¹.loop) ≃ S¹.loop
                 sts = (ap (encode o decode') S¹.loop)  ≃〈 ap-o encode decode' S¹.loop 〉 
                       (ap encode (ap decode' S¹.loop)) ≃〈 ap (λ y → ap encode y) (S¹.βloop/rec id S².loop) 〉 
                       (ap encode (S².loop))            ≃〈 transport-H-loop2 〉 
                       S¹.loop ∎

  decode : {x : S²} -> H x → Path{S²} S².base x
  decode{x} = S²-elim (λ x' → H x' → Path {S²} S².base x')
                      decode'
                      {!!} 
                      x

  decode-encode : {x : S²} (α : _) → decode{x} (encode{x} α) ≃ α
  decode-encode id = id

  impossible : HEquiv (Path{S²} S².base S².base) S¹
  impossible = hequiv encode decode decode-encode encode-decode'
  