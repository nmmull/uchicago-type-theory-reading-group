{-# OPTIONS --without-K #-}
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Data.Product
open import Function.Base using (_∘_; id)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; trans; erefl)
open Eq.≡-Reasoning
open import 11-05-meeting
open import 11-12-meeting
open import Function.Base using (_∘_; id)
open import Data.Unit

-- 2.6 Cartesian product types

-- 2.6.1

proj-eq :
    ∀ {l m}
    {A : Set l}
    {B : Set m}
    {x y : A × B} →
    ---
    x ≡ y → (proj₁ x ≡ proj₁ y) × (proj₂ x ≡ proj₂ y)
proj-eq p = (ap proj₁ p , ap proj₂ p)

-- 2.6.3

pair⁼ :
    ∀ {l m}
    {A : Set l}
    {B : Set m}
    {x y : A × B} →
    ---
    (proj₁ x ≡ proj₁ y) × (proj₂ x ≡ proj₂ y) → x ≡ y
pair⁼ (refl , refl) = refl

-- Theorem 2.6.2

proj-eq-qinv :
    ∀ {l m}
    {A : Set l}
    {B : Set m}
    {x y : A × B} →
    ---
    qinv (proj-eq {l} {m} {A} {B} {x} {y})
proj-eq-qinv {l} {m} {A} {B} {x} {y} =
    (pair⁼ {l} {m} {A} {B} {x} {y} ,
        (λ { (refl , refl) → refl }) ,
        (λ { refl → refl}))

-- Propositional computation rules

beta-pair-1 :
    ∀ {l m}
    {A : Set l}
    {B : Set m}
    {x y : A × B}
    (p : proj₁ x ≡ proj₁ y)
    (q : proj₂ x ≡ proj₂ y) →
    ---
    ap proj₁ (pair⁼ (p , q)) ≡ p
beta-pair-1 refl refl = refl 

beta-pair-2 :
    ∀ {l m}
    {A : Set l}
    {B : Set m}
    {x y : A × B}
    (p : proj₁ x ≡ proj₁ y)
    (q : proj₂ x ≡ proj₂ y) →
    ---
    ap proj₂ (pair⁼ (p , q)) ≡ q
beta-pair-2 refl refl = refl

-- Propositional uniqueness principle

eta-pair :
    ∀ {l m}
    {A : Set l}
    {B : Set m}
    {x y : A × B}
    (r : x ≡ y) →
    ---
    r ≡ pair⁼ (ap proj₁ r , ap proj₂ r)
eta-pair refl = refl

-- Reflexivity characterization

refl-pair :
    ∀ {l m}
    {A : Set l}
    {B : Set m}
    {z : A × B} →
    ---
    erefl z ≡ pair⁼ (erefl (proj₁ z) , erefl (proj₂ z) )
refl-pair = refl

-- inverse characterization

inv-pair :
    ∀ {l m}
    {A : Set l}
    {B : Set m}
    {x y : A × B}
    (p : x ≡ y) →
    ---
    inv p ≡ pair⁼ (ap proj₁ (inv p) , ap proj₂ (inv p))
inv-pair refl = refl

-- concatentation characterization

■-pair :
    ∀ {l m}
    {A : Set l}
    {B : Set m}
    {x y z : A × B}
    (p : x ≡ y)
    (q : y ≡ z) →
    ---
    p ■ q ≡ pair⁼ (ap proj₁ p ■ ap proj₁ q , ap proj₂ p ■ ap proj₂ q)
■-pair refl refl = refl

-- Theorem 2.6.4

transport-pair :
    ∀ {l m n}
    {Z : Set l}
    {A : Z → Set m}
    {B : Z → Set n}
    {z w : Z}
    {x : (A z) × (B z)}
    (p : z ≡ w) →
    ---
    transport (λ { y → (A y) × (B y)}) p x ≡ (transport A p (proj₁ x) , transport B p (proj₂ x))
transport-pair refl = refl

-- Theorem 2.6.5

pair-func :
    ∀ {l m n o}
    {A : Set l}
    {B : Set m}
    {A' : Set n}
    {B' : Set o}
    (g : A → A')
    (h : B → B') →
    ---
    A × B → A' × B'
pair-func g h (a , a') = (g a , h a')

ap-pair :
    ∀ {l m n o}
    {A : Set l}
    {B : Set m}
    {A' : Set n}
    {B' : Set o}
    {g : A → A'}
    {h : B → B'}
    {x y : A × B}
    (p : proj₁ x ≡ proj₁ y)
    (q : proj₂ x ≡ proj₂ y) →
    ---
    ap (pair-func g h) (pair⁼ (p , q)) ≡ pair⁼ (ap g p , ap h q)
ap-pair refl refl = refl

-- 2.7 Σ-Types

-- Theorem 2.7.2

Σ-proj-eq :
    ∀ {l m}
    {A : Set l}
    {P : A → Set m}
    {w w' : Σ[ x ∈ A ] (P x)} →
    ---
    w ≡ w' → Σ[ p ∈ (proj₁ w ≡ proj₁ w') ] (transport P p (proj₂ w) ≡ proj₂ w')
Σ-proj-eq refl = (refl , refl)

Σ-pair⁼ :
    ∀ {l m}
    {A : Set l}
    {P : A → Set m}
    {w w' : Σ[ x ∈ A ] (P x)} →
    ---
    Σ[ p ∈ (proj₁ w ≡ proj₁ w') ] (transport P p (proj₂ w) ≡ proj₂ w') → w ≡ w'
Σ-pair⁼ {w = (w1 , w2)} {w' = (w1' , w2')} (refl , refl) = refl

Σ-proj-eq-qinv :
    ∀ {l m}
    {A : Set l}
    {P : A → Set m}
    {w w' : Σ[ x ∈ A ] (P x)} →
    ---
    qinv (Σ-proj-eq {l} {m} {A} {P} {w} {w'})
Σ-proj-eq-qinv {l} {m} {A} {P} {w} {w'} =
    (Σ-pair⁼ {l} {m} {A} {P} {w} {w'} ,
        (λ { (refl , refl) → refl}) ,
        (λ { refl → refl}))

-- Propositional uniqueness principle

eta-Σ :
    ∀ {l m}
    {A : Set l}
    {P : A → Set m}
    {z : Σ[ x ∈ A ] (P x)} →
    ---
    z ≡ (proj₁ z , proj₂ z)
eta-Σ = refl

-- Theorem 2.7.4

transport-Σ :
    ∀ {l m n}
    {A : Set l}
    {P : A → Set m}
    {Q : Σ[ x ∈ A ] (P x) → Set n}
    {x y : A}
    (p : x ≡ y)
    (uz : Σ[ u ∈ (P x) ] (Q (x , u))) →
    ---
    transport (λ { z → Σ[ u ∈ P z ] Q (z , u) }) p uz ≡
        (transport P p (proj₁ uz), transport Q (Σ-pair⁼ (p , refl)) (proj₂ uz))
transport-Σ refl prf = refl

-- 2.8 The unit type

-- Theorem 2.8.1

eq-⊤ :
    ∀ {x y : ⊤} →
    ---
    (x ≡ y) ≃ ⊤
eq-⊤ {x} {y} = (f , qinv-to-isequiv f ((g , (λ { tt → refl }) , λ { refl → refl } ))) where
    f : (x ≡ y) → ⊤
    f _ = tt
    g : ⊤ → (x ≡ y)
    g _ = refl


    



 