{-# OPTIONS --without-K #-}
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Function.Base using (_∘_; id)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; trans)
open Eq.≡-Reasoning

-- 2.1 Types are higher groupoids

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

-- alternative definition of whiskering that does not work for the proof below
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

-- proof that both definitions of whiskering are equal at the "next level"
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
-- this works if K-axioms is enabled
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