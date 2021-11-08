{-# OPTIONS --without-K #-}
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Function.Base using (_∘_; id)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; trans)
open Eq.≡-Reasoning
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

-- Lemma 2.1.1
inv :
    ∀ {l}
    {A : Set l}
    {a b : A} →
    ---
    a ≡ b → b ≡ a
inv refl = refl

-- Lemma 2.1.2
infixl 30 _■_
_■_ :
    ∀ {l}
    {A : Set l}
    {a b c : A} →
    ---
    a ≡ b → b ≡ c → a ≡ c
refl ■ refl = refl

-- Lemma 2.1.3 ?

-- Lemma 2.1.4(i)
id-right :
    ∀ {l}
    {A : Set l}
    {x y : A}
    {p : x ≡ y} →
    ---
    p ≡ p ■ refl
id-right {p = refl} = refl

id-left :
    ∀ {l}
    {A : Set l}
    {x y : A}
    {p : x ≡ y} → 
    ---
    p ≡ refl ■ p
id-left {p = refl} = refl

-- Lemma 2.1.4(ii)
inv-left :
    ∀ {l}
    {A : Set l}
    {x y : A}
    {p : x ≡ y} →
    ---
    (inv p) ■ p ≡ refl
inv-left {p = refl} = refl

inv-right :
    ∀ {l}
    {A : Set l}
    {x y : A}
    {p : x ≡ y} →
    ---
    p ■ (inv p) ≡ refl
inv-right {p = refl} = refl

-- Lemma 2.1.4(iii)
double-inv :
    ∀ {l}
    {A : Set l}
    {x y : A}
    {p : x ≡ y} →
    ---
    inv (inv p) ≡ p
double-inv {p = refl} = refl

-- Lemma 2.1.4(iv)
assoc :
    ∀ {l}
    {A : Set l}
    {x y z w : A} →
    ---
    ∀ (p : x ≡ y)
    (q : y ≡ z)
    (r : z ≡ w) →
    p ■ (q ■ r) ≡ (p ■ q) ■ r
assoc refl refl refl = refl

loop-space :
    ∀ {l}
    (A : Set l)
    (a : A) →
    Set l
loop-space A a = a ≡ a

2D-loop-space :
    ∀ {l}
    (A : Set l)
    (a : A) →
    Set l
2D-loop-space {l} A a = refl {l} {A} {a} ≡ refl {l} {A} {a}

whisker-right :
    ∀ {l}
    {A : Set l}
    {a b c : A}
    {p q : a ≡ b}
    (α : p ≡ q)
    (r : b ≡ c) → 
    ---
    p ■ r ≡ q ■ r
whisker-right α refl = inv id-right ■ α ■ id-right

whisker-right' :
    ∀ {l}
    {A : Set l}
    {a b c : A}
    {p q : a ≡ b}
    (α : p ≡ q)
    (r : b ≡ c) → 
    ---
    p ■ r ≡ q ■ r
whisker-right' refl refl = refl

whisker-eq :
    ∀ {l}
    {A : Set l}
    {a b c : A}
    {p q : a ≡ b}
    (α : p ≡ q)
    (r : b ≡ c) →
    ---
    whisker-right α r ≡ whisker-right' α r
whisker-eq refl refl = begin
        inv id-right ■ refl ■ id-right
    ≡⟨ cong (λ { x → x ■ id-right}) (inv id-right) ⟩
        inv id-right ■ id-right
    ≡⟨ inv-left ⟩
        refl
    ∎

whisker-left :
    ∀ {l}
    {A : Set l}
    {a b c : A}
    {p q : b ≡ c}
    (l : a ≡ b)
    (α : p ≡ q) → 
    ---
    l ■ p ≡ l ■ q
whisker-left refl α = inv id-left ■ α ■ id-left

h-comp :
    ∀ {l}
    {A : Set l}
    {a b c : A}
    {p : a ≡ b}
    (q : a ≡ b)
    (α : p ≡ q)
    (r : b ≡ c)
    {s : b ≡ c}
    (β : r ≡ s) →
    ---
    p ■ r ≡ q ■ s
h-comp q α r β = (whisker-right α r) ■ (whisker-left q β)

infixl 30 _⋆_
_⋆_ :
    ∀ {l}
    {A : Set l}
    {a : A} →
    ---
    2D-loop-space A a → 2D-loop-space A a → 2D-loop-space A a
α ⋆ β = h-comp refl α refl β

refl-both-sides :
    ∀ {l}
    {A : Set l}
    {a b : A}
    {p : a ≡ b} →
    ---
    refl ■ p ■ refl ≡ p
refl-both-sides {p = p} =
    begin
        refl ■ p ■ refl
    ≡⟨ cong (λ { x → x ■ refl}) (inv id-left) ⟩
        p ■ refl
    ≡⟨ inv id-right ⟩
        p
    ∎

h-comp-to-concat :
    ∀ {l}
    {A : Set l}
    {a : A}
    (α β : 2D-loop-space A a) →
    ---
    α ⋆ β ≡ α ■ β
h-comp-to-concat α β = 
    begin
        α ⋆ β
    ≡⟨⟩
        (inv id-right ■ α ■ id-right) ■ (inv id-left ■ β ■ id-left)
    ≡⟨⟩
        (refl ■ α ■ refl) ■ (refl ■ β ■ refl)
    ≡⟨ cong₂ (λ { x y → x ■ y }) refl-both-sides refl-both-sides ⟩
        α ■ β
    ∎

h-comp' :
    ∀ {l}
    {A : Set l}
    {a b c : A}
    (p : a ≡ b)
    {q : a ≡ b}
    (α : p ≡ q)
    {r : b ≡ c}
    (s : b ≡ c)
    (β : r ≡ s) →
    ---
    p ■ r ≡ q ■ s
h-comp' p α s β = (whisker-left p β) ■ (whisker-right α s)

infixl 30 _⋆'_
_⋆'_ :
    ∀ {l}
    {A : Set l}
    {a : A} →
    ---
    2D-loop-space A a → 2D-loop-space A a → 2D-loop-space A a
α ⋆' β = h-comp' refl α refl β

h-comp'-to-concat :
    ∀ {l}
    {A : Set l}
    {a : A}
    (α β : 2D-loop-space A a) →
    ---
    α ⋆' β ≡ β ■ α
h-comp'-to-concat α β = 
    begin
        α ⋆' β
    ≡⟨⟩
        (refl ■ β ■ refl) ■ (refl ■ α ■ refl)
    ≡⟨ cong₂ (λ { x y → x ■ y }) refl-both-sides refl-both-sides ⟩
        β ■ α
    ∎

h-comp-eq :
    ∀ {l}
    {A : Set l}
    {a : A}
    (α β : 2D-loop-space A a) →
    α ⋆ β ≡ α ⋆' β
h-comp-eq α β = lemma refl refl α refl refl β where
    lemma :
        ∀ {l}
        {A : Set l}
        {a b c : A}
        (p : a ≡ b)
        (q : a ≡ b)
        (α : p ≡ q)
        (r : b ≡ c)
        (s : b ≡ c)
        (β : r ≡ s) →
        ---
        h-comp q α r β ≡ h-comp' p α s β
    lemma refl refl refl refl refl refl = refl

-- Theorem 2.1.6
eckmann-hilton :
    ∀ {l}
    {A : Set l}
    {a : A} →
    ---
    ∀ (α β : 2D-loop-space A a) → α ■ β ≡ β ■ α
-- eckmann-hilton refl refl = refl
eckmann-hilton α β =
    begin
        α ■ β
    ≡⟨ inv (h-comp-to-concat α β) ⟩
        α ⋆ β
    ≡⟨ h-comp-eq α β ⟩
        α ⋆' β
    ≡⟨ h-comp'-to-concat α β ⟩
        β ■ α
    ∎

-- Lemma 2.2.1
ap :
    ∀ {l m}
    {A : Set l}
    {B : Set m}
    {x y : A}
    (f : A → B) →
    ---
    x ≡ y → f x ≡ f y
ap f refl = refl

-- Lemma 2.2.2(i)
ap-commutes-with-concat :
    ∀ {l m}
    {A : Set l}
    {B : Set m}
    {x y z : A}
    (f : A → B)
    (p : x ≡ y)
    (q : y ≡ z) →
    ---
    ap f (p ■ q) ≡ ap f p ■ ap f q
ap-commutes-with-concat f refl refl = refl

-- Lemma 2.2.2(ii)
ap-commutes-with-inverse :
    ∀ {l m}
    {A : Set l}
    {B : Set m}
    {x y : A}
    (f : A → B)
    (p : x ≡ y) →
    ---
    ap f (inv p) ≡ inv (ap f p)
ap-commutes-with-inverse f refl = refl

-- Lemma 2.2.2(iii)
ap-composes :
    ∀ {l m n}
    {A : Set l}
    {B : Set m}
    {C : Set n}
    {x y : A}
    (f : A → B)
    (g : B → C)
    (p : x ≡ y) →
    ---
    ap g (ap f p) ≡ ap (g ∘ f) p
ap-composes f g refl = refl

ap-id :
    ∀ {l}
    {A : Set l}
    {x y : A}
    (p : x ≡ y) →
    ---
    ap id p ≡ p
ap-id refl = refl

    








 