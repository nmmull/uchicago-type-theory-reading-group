{-# OPTIONS --without-K #-}
open import Agda.Primitive using (Level; _⊔_; lsuc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _+_; suc)

-- Section 1.11: Propositions as types

example-1 :
    ∀ {l m}
    {A : Set l}
    {B : Set m} →
    ---
    ¬ A × ¬ B → ¬ (A ⊎ B)
example-1 (x , y) (inj₁ a) = x a
example-1 (x , y) (inj₂ b) = y b
--example-1 (x , y) (inj₁ a) = x a
--example-1 (x , y) (inj₂ b) = y b

example-2 :
    ∀ {l m}
    {A : Set l}
    {B : Set m} →
    ---
    ¬ (A ⊎ B) → ¬ A × ¬ B
example-2 {l} {m} {A} {B} p = (p1 , p2) where
    p1 : ¬ A
    p1 a = p (inj₁ a)
    p2 : ¬ B
    p2 b = p (inj₂ b)

example-3 :
    ∀ {l1 l2 l3}
    {A : Set l1}
    {P : A → Set l2}
    {Q : A → Set l3} →
    ---
    (∀ x → (P x) × (Q x)) → (∀ x → P x) × (∀ x → Q x)
example-3 p = ((λ { x → proj₁ (p x) }) , λ { x → proj₂ (p x) })

exercise-1-11 :
    ∀ {l}
    {A : Set l} →
    ---
    ¬ ¬ ¬ A → ¬ A
exercise-1-11 {l} {A} p a = p double-neg where
    double-neg : ¬ ¬ A
    double-neg neg = neg a

exercise-1-12-i :
    ∀ {l m}
    {A : Set l}
    {B : Set m} →
    ---
    A → (B → A)
exercise-1-12-i a b = a

exercise-1-12-ii :
    ∀ {l}
    {A : Set l} →
    ---
    A → ¬ ¬ A
exercise-1-12-ii a n = n a

exercise-1-12-iii :
    ∀ {l m}
    {A : Set l}
    {B : Set m} →
    ---
    ¬ A ⊎ ¬ B → ¬ (A × B)
exercise-1-12-iii (inj₁ na) (a , _) = na a
exercise-1-12-iii (inj₂ nb) (_ , b) = nb b

exercise-1-13 :
    ∀ {l}
    {P : Set l} →
    ---
    ¬ ¬ (P ⊎ ¬ P)
exercise-1-13 {l} {P} p = p (inj₂ neg-P-prf) where
    neg-P-prf : ¬ P
    neg-P-prf p-prf = p (inj₁ p-prf)

-- Section 1.12: Identity types

indiscern-of-id :
    ∀ {l m}
    {A : Set l}
    {C : A → Set m} →
    ---
    ∀ x y → x ≡ y → C x → C y
indiscern-of-id x y refl cx = cx

path-induction :
    ∀ {l m}
    {A : Set l}
    (C : (x y : A) → x ≡ y → Set m)
    (c : (x : A) → C x x refl) →
    ---
    ∀ x y (p : x ≡ y) → C x y p
path-induction C c x y refl = c x

based-path-induction :
    ∀ {l m}
    {A : Set l}
    (a : A)
    (C : (x : A) → a ≡ x → Set m)
    (c : C a refl) → 
    ---
    ∀ x (p : a ≡ x) → C x p
based-path-induction a C c x refl = c

path-ind-from-based-path-ind :
    ∀ {l m} →
    {A : Set l} →
    (C : (x y : A) → x ≡ y → Set m) →
    (c : (x : A) → C x x refl) →
    ---
    ∀ x y (p : x ≡ y) → C x y p
path-ind-from-based-path-ind {A} C c x = based-path-induction x (C x) (c x)

based-path-ind-from-path-ind :
    ∀ {l m}
    {A : Set l}
    (a : A)
    (C : (x : A) → a ≡ x → Set m)
    (c : C a refl) →
    ---
    ∀ x (p : a ≡ x) → C x p
based-path-ind-from-path-ind {l} {m} {A} a C c x p = f a x p C c where
    D : (x y : A) → x ≡ y → Set (l ⊔ (lsuc m))
    D x y p = (C : (z : A) → x ≡ z → Set m) → C x refl → C y p
    d : (x : A) → D x x refl
    d x C c = c
    f : (x y : A) → (p : x ≡ y) → D x y p
    f = path-induction D d

-- -- only works if K axiom is allowed
-- exercise-1-14 :
--     {A : Set} →
--     (x : A) →
--     (eq : x ≡ x) →
--     eq ≡ refl
-- exercise-1-14 x refl = refl

exercise-1-15 :
    ∀ {l m}
    {A : Set l}
    (C : A → Set m) →
    ---
    ∀ x y (p : x ≡ y) → C x → C y
-- exercise-1-15 C x y p c = based-path-ind-from-path-ind x (λ { a _ → C a }) c y p
exercise-1-15 {l} {m} {A} C x y p c = f x y p C c where
    D : (x y : A) → (p : x ≡ y) → Set (l ⊔ lsuc m)
    D x y p = (C : A → Set m) → C x → C y
    d : (x : A) → D x x refl
    d a C p = p
    f : (x y : A) → (p : x ≡ y) → (C : A → Set m) → C x → C y
    f = path-induction D d

exercise-1-16 :
    ∀ (n m : ℕ) →
    ---
    n + m ≡ m + n
exercise-1-16 0 0 = refl
exercise-1-16 (suc j) 0 = cong suc (exercise-1-16 j 0)
exercise-1-16 n (suc k) = trans (lemma n k) (cong suc (exercise-1-16 n k)) where
    lemma :
        ∀ (i j : ℕ) →
        ---
        i + (suc j) ≡ (suc i) + j
    lemma 0 j = refl
    lemma (suc k) j = cong suc (lemma k j)