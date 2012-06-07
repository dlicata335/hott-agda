{-# OPTIONS --type-in-type --without-K #-}
open import lib.Prelude
open Paths
open S¹

module applications.Pi1S1-2 where
  
  succA : AEq Int Int
  succA = isoToAdj (succ , isiso pred succ-pred pred-succ)

  predA : AEq Int Int
  predA = isoToAdj (pred , isiso succ pred-succ succ-pred)

  succ≃ : Int ≃ Int
  succ≃ = ua succA

  pred≃ : Int ≃ Int
  pred≃ = ua predA

  succ≃-! : (! succ≃) ≃ pred≃
  succ≃-! = !-adj succ (snd succA) (snd predA)

  C : S¹ -> Set
  C = S¹-rec Int succ≃

  subst-C-loop : subst C loop ≃ succ
  subst-C-loop = 
    subst C loop                  ≃〈 subst-resp C loop 〉 
    subst (λ x → x) (resp C loop) ≃〈 resp (subst (λ x → x)) (βloop/rec Int succ≃) 〉 
    subst (λ x → x) succ≃         ≃〈 subst-univ _ 〉 
    succ ∎

  subst-C-!loop : subst C (! loop) ≃ pred
  subst-C-!loop = 
    subst C (! loop)                  ≃〈 subst-resp C (! loop) 〉 
    subst (λ x → x) (resp C (! loop)) ≃〈 resp (subst (λ x → x)) (resp-! C loop) 〉 
    subst (λ x → x) (! (resp C loop)) ≃〈 resp (λ y → subst (λ x → x) (! y)) (βloop/rec Int succ≃) 〉 
    subst (λ x → x) (! succ≃)         ≃〈 resp (subst (λ x → x)) succ≃-! 〉 
    subst (λ x → x) pred≃             ≃〈 subst-univ _ 〉 
    pred ∎

  loop^ : Int -> base ≃ base
  loop^ Zero = Refl
  loop^ (Neg Z) = ! loop
  loop^ (Neg (S n)) = ! loop ∘ loop^ (Neg n)
  loop^ (Pos Z) = loop
  loop^ (Pos (S n)) = loop ∘ loop^ (Pos n)

  encode : {a : S¹} -> base ≃ a -> C a
  encode p = subst C p Zero

  encode' : base ≃ base -> Int
  encode' = encode {base}

  encode-loop^ : (n : Int) -> encode (loop^ n) ≃ n
  encode-loop^ Zero = Refl
  encode-loop^ (Pos Z) = app≃ subst-C-loop
  encode-loop^ (Pos (S y)) = 
    subst C (loop ∘ loop^ (Pos y)) Zero         ≃〈 app≃ (subst-∘ C (loop^ (Pos y)) loop) 〉 
    subst C loop (subst C (loop^ (Pos y)) Zero) ≃〈 app≃ subst-C-loop 〉 
    succ (subst C (loop^ (Pos y)) Zero)         ≃〈 resp succ (encode-loop^ (Pos y)) 〉 
    succ (Pos y) ∎
  encode-loop^ (Neg Z) = app≃ subst-C-!loop
  encode-loop^ (Neg (S y)) = 
    subst C (! loop ∘ loop^ (Neg y)) Zero ≃〈 app≃ (subst-∘ C (loop^ (Neg y)) (! loop)) 〉 
    subst C (! loop) (subst C (loop^ (Neg y)) Zero) ≃〈 app≃ subst-C-!loop 〉 
    pred (subst C (loop^ (Neg y)) Zero) ≃〈 resp pred (encode-loop^ (Neg y)) 〉 
    pred (Neg y) ∎

  shift : (n : Int) -> (loop ∘ (loop^ (pred n))) ≃ loop^ n
  shift (Pos Z) = Refl
  shift (Pos (S y)) = Refl
  shift Zero = !-inv-r loop
  shift (Neg Z) = 
    ∘-unit-l _ ∘ 
    resp (λ x → x ∘ ! loop) (!-inv-r loop) ∘ 
    ∘-assoc loop (! loop) (! loop)
  shift (Neg (S y)) = 
    loop ∘ ! loop ∘ ! loop ∘ loop^ (Neg y)   ≃〈 ∘-assoc loop (! loop) (! loop ∘ loop^ (Neg y)) 〉 
    (loop ∘ ! loop) ∘ ! loop ∘ loop^ (Neg y) ≃〈 resp (λ x → x ∘ ! loop ∘ loop^ (Neg y)) (!-inv-r loop) 〉 
    Refl ∘ ! loop ∘ loop^ (Neg y)            ≃〈 ∘-unit-l _ 〉 
    ! loop ∘ loop^ (Neg y) ∎

  decode : {a : S¹} -> C a -> base ≃ a
  decode {a} = 
    S¹-elim {λ x → C x → base ≃ x} 
      loop^ 
      (subst (λ x' → C x' → base ≃ x') loop loop^                ≃〈 subst-→ C (Id base) loop loop^ 〉 
       (λ y → subst (Id base) loop (loop^ (subst C (! loop) y))) ≃〈 λ≃ (λ y → subst-Id-post loop (loop^ (subst C (! loop) y))) 〉 
       (λ y → loop ∘ loop^ (subst C (! loop) y))                 ≃〈 λ≃ (λ y → resp (λ x' → loop ∘ loop^ x') (app≃ subst-C-!loop)) 〉 
       (λ y → loop ∘ loop^ (pred y))                             ≃〈 λ≃ shift 〉 
       (λ y → loop^ y)
       ∎) 
      a

  decode-encode : ∀ {a} -> (p : base ≃ a) -> decode (encode p) ≃ p
  decode-encode {a} p = 
    jay1 (λ a' (p' : base ≃ a') → decode (encode p') ≃ p') p Refl


  theorem : Id base base ≃ Int
  theorem = ua (isoToAdj (encode , isiso decode encode-loop^ decode-encode))