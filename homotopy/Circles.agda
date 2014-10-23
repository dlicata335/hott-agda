
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.cubical.Cubical

module homotopy.Circles where

  module Circle = S¹
  module Circle2 = S¹2

  one2two : Circle.S¹ -> Circle2.S¹
  one2two = Circle.S¹-rec Circle2.w ((! Circle2.s) ∘ Circle2.n)

  two2one : Circle2.S¹ → Circle.S¹
  two2one = Circle2.S¹-rec Circle.base Circle.base Circle.loop id

  comp1 : (x : Circle.S¹) → two2one (one2two x) == x
  comp1 = Circle.S¹-elimo _ id 
          (PathOver=.in-PathOver-= (vertical-degen-square 
            (ap (λ z → two2one (one2two z)) Circle.loop     ≃〈 ap-o two2one one2two Circle.loop 〉
             ap two2one (ap one2two Circle.loop)             ≃〈 ap (ap two2one) (Circle.βloop/rec _ _) 〉
             ap two2one ((! Circle2.s) ∘ Circle2.n)          ≃〈 ap-∘ two2one (! Circle2.s) (Circle2.n) 〉
             ap two2one (! Circle2.s) ∘ ap two2one Circle2.n ≃〈 ap (λ h → h ∘ ap two2one Circle2.n) (ap-! two2one Circle2.s) 〉
             ! (ap two2one Circle2.s) ∘ ap two2one Circle2.n ≃〈 ap (λ h → ! (ap two2one Circle2.s) ∘ h) (Circle2.βn/rec Circle.base Circle.base Circle.loop id) 〉
             ! (ap two2one Circle2.s) ∘ Circle.loop          ≃〈 ap (λ h → ! h ∘ Circle.loop) (Circle2.βs/rec Circle.base Circle.base Circle.loop id) 〉
             ! id ∘ Circle.loop                              ≃〈 ∘-unit-l Circle.loop 〉
             Circle.loop                                     ≃〈 ! (ap-id Circle.loop) 〉
             ap (λ z → z) Circle.loop ∎)))

  comp2 : (x : Circle2.S¹) → one2two (two2one x) == x
  comp2 = Circle2.S¹-elim _
           id
           Circle2.s
           (PathOver=.in-PathOver-= (disc-to-square (! 
             (Circle2.s ∘ ap (λ z → one2two (two2one z)) Circle2.n  ≃〈 ap (λ x → Circle2.s ∘ x) (ap-o one2two two2one Circle2.n) 〉
              Circle2.s ∘ ap one2two (ap two2one Circle2.n)         ≃〈 ap (λ x → Circle2.s ∘ ap one2two x) (Circle2.βn/rec Circle.base Circle.base Circle.loop id) 〉
              Circle2.s ∘ ap one2two (Circle.loop)                  ≃〈 ap (λ h → Circle2.s ∘ h) (Circle.βloop/rec _ _) 〉
              Circle2.s ∘ (! Circle2.s ∘ Circle2.n)                 ≃〈 ∘-assoc Circle2.s (! Circle2.s) Circle2.n 〉
              (Circle2.s ∘ ! Circle2.s) ∘ Circle2.n                 ≃〈 ap (λ h → h ∘ Circle2.n) (!-inv-r Circle2.s) 〉
              (id) ∘ Circle2.n                                      ≃〈 ∘-unit-l Circle2.n 〉
              Circle2.n                                             ≃〈 ! (ap-id Circle2.n) 〉 
              ap (λ z → z) Circle2.n ∎))))
           (PathOver=.in-PathOver-= (disc-to-square (! 
             (Circle2.s ∘ ap (λ z → one2two (two2one z)) Circle2.s  ≃〈 ap (λ x → Circle2.s ∘ x) (ap-o one2two two2one Circle2.s) 〉
              Circle2.s ∘ ap one2two (ap two2one Circle2.s)         ≃〈 ap (λ x → Circle2.s ∘ ap one2two x) (Circle2.βs/rec Circle.base Circle.base Circle.loop id) 〉
              Circle2.s                                             ≃〈 ! (ap-id Circle2.s) 〉 
              ap (λ z → z) Circle2.s ∎))))


