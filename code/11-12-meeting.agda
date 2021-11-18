{-# OPTIONS --without-K #-}
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Data.Product
open import Function.Base using (_∘_; id)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; trans)
open Eq.≡-Reasoning
open import 11-05-meeting
open import Function.Base using (_∘_; id)

-- Lemma 2.3.1

transport :
    ∀ {l m}
    {A : Set l}
    {x y : A}
    (P : A → Set m) →
    ---
    (p : x ≡ y) → P x → P y
transport P refl prf = prf

-- Lemma 2.3.2

lift :
    ∀ {l m}
    {A : Set l}
    {P : A → Set m}
    {x y : A}
    (u : P x)
    (p : x ≡ y) → 
    ---
    (x , u) ≡ (y , transport P p u)
lift u refl = refl

-- Lemma 2.3.4

apd :
    ∀ {l m}
    {A : Set l}
    {P : A → Set m}
    {x y : A}
    (f : (z : A) → P z)
    (p : x ≡ y) →
    ---
    transport P p (f x) ≡ f y
apd f refl = refl

-- Lemma 2.3.5

transportconst :
    ∀ {l m}
    {A : Set l}
    {x y : A}
    (B : Set m)
    (p : x ≡ y)
    (b : B) →
    ---
    transport (λ { _ → B}) p b ≡ b
transportconst B refl b = refl

-- Lemma 2.3.8

apd-eq-transportconst-ap :
    ∀ {l m}
    {A : Set l}
    {B : Set m}
    {x y : A}
    (f : A → B)
    (p : x ≡ y) →
    ---
    apd f p ≡ transportconst B p (f x) ■ (ap f p)
apd-eq-transportconst-ap f refl = refl

-- Lemma 2.3.9

transport-compose :
    ∀ {l m}
    {A : Set l}
    {x y z : A}
    (P : A → Set m)
    (p : x ≡ y)
    (q : y ≡ z)
    (u : P x) →
    ---
    transport P q (transport P p u) ≡ transport P (p ■ q) u
transport-compose P refl refl u = refl

-- Lemma 2.3.10

transport-ap-commute :
    ∀ {l m n}
    {A : Set l}
    {B : Set m}
    {x y : A}
    (f : A → B)
    (P : B → Set n)
    (p : x ≡ y)
    (u : P (f x)) →
    ---
    transport (P ∘ f) p u ≡ transport P (ap f p) u
transport-ap-commute f P refl u = refl

-- Lemma 2.3.11

transport-dep-imp-commute :
    ∀ {l m n}
    {A : Set l}
    {x y : A}
    (P : A → Set m)
    (Q : A → Set n)
    (f : ∀ (z : A) → P z → Q z)
    (p : x ≡ y)
    (u : P x) →
    ---
    transport Q p (f x u) ≡ f y (transport P p u)
transport-dep-imp-commute P Q f refl u = refl

homotopy :
    ∀ {l m}
    {A : Set l}
    {P : A → Set m} →
    ---
    (f g : ∀ (x : A) → P x) →  Set (l ⊔ m)
homotopy {A = A} f g = ∀ (x : A) → f x ≡ g x

infixl 30 _∼_
_∼_ :
    ∀ {l m}
    {A : Set l}
    {P : A → Set m} →
    ---
    (f g : ∀ (x : A) → P x) →  Set (l ⊔ m)
f ∼ g = homotopy f g

-- Lemma 2.4.2(i)

homotopy-refl :
    ∀ {l m}
    {A : Set l}
    {P : A → Set m}
    (f : ∀ (x : A) → P x) →
    ---
    f ∼ f
homotopy-refl _ _ = refl

-- Lemma 2.4.2(ii)

homotopy-symm :
    ∀ {l m}
    {A : Set l}
    {P : A → Set m}
    (f g : ∀ (x : A) → P x) →
    ---
    f ∼ g → g ∼ f
homotopy-symm f g H x = inv (H x)

-- Lemma 2.4.2(iii)

homotopy-trans : 
    ∀ {l m}
    {A : Set l}
    {P : A → Set m}
    (f g h : ∀ (x : A) → P x) →
    ---
    f ∼ g → g ∼ h → f ∼ h
homotopy-trans f g h H1 H2 x = (H1 x) ■ (H2 x)

-- Lemma 2.4.3

homotopy-nat-trans :
    ∀ {l m}
    {A : Set l}
    {B : Set m}
    {x y : A}
    (f g : A → B)
    (H : f ∼ g)
    (p : x ≡ y) → 
    ---
    H x ■ ap g p ≡ ap f p ■ H y
homotopy-nat-trans f g H refl = inv id-right ■ id-left

-- Corollary 2.4.4

homotopy-id :
    ∀ {l}
    {A : Set l}
    (f : A → A)
    (H : f ∼ id)
    (x : A) →
    ---
    H (f x) ≡ ap f (H x)
homotopy-id f H x = begin
        H (f x)
    ≡⟨ id-right ⟩
        H (f x) ■ refl
    ≡⟨ cong (λ { y → H (f x) ■ y }) (inv inv-right) ⟩
        H (f x) ■ (H x ■ inv (H x))
    ≡⟨ assoc (H (f x)) (H x) (inv (H x)) ⟩
        (H (f x) ■ H x) ■ inv (H x)
    ≡⟨ cong (λ { y → (H (f x) ■ y) ■ inv (H x) }) (inv (ap-id (H x))) ⟩
        (H (f x) ■ ap id (H x)) ■ inv (H x)
    ≡⟨ cong (λ { y → y ■ inv (H x) })  (homotopy-nat-trans f id H (H x)) ⟩
        (ap f (H x) ■ H x) ■ inv (H x)
    ≡⟨ inv (assoc (ap f (H x)) (H x) (inv (H x))) ⟩
        ap f (H x) ■ (H x ■ inv (H x))
    ≡⟨ cong (λ { y → ap f (H x) ■ y }) inv-right ⟩
        ap f (H x) ■ refl
    ≡⟨ inv id-right ⟩
        ap f (H x)
    ∎

-- Definition 2.4.6

qinv :
    ∀ {l m}
    {A : Set l}
    {B : Set m} →
    ---
    (f : A → B) → Set (l ⊔ m)
qinv {A = A} {B = B} f = Σ[ g ∈ (B → A) ] ((f ∘ g) ∼ id) × ((g ∘ f) ∼ id)

-- Example 2.4.7

qinv-id :
    ∀ {l}
    {A : Set l} →
    ---
    qinv {A = A} id
qinv-id = (id , (λ { x → refl }) , λ { x → refl })

-- Example 2.4.8

qinv-concat-left :
    ∀ {l}
    {A : Set l}
    {x y z : A}
    (p : x ≡ y) → 
    ---
    qinv {A = y ≡ z} (λ { q → p ■ q })
qinv-concat-left p = ((λ {q → (inv p) ■ q }) , prf1 , prf2) where
    prf1 : ∀ q → p ■ ((inv p) ■ q) ≡ q
    prf1 q =
        begin
            p ■ (inv p ■ q)
        ≡⟨ assoc p (inv p) q ⟩
            p ■ inv p ■ q
        ≡⟨ cong (λ { r → r ■ q }) inv-right ⟩
            refl ■ q
        ≡⟨ inv id-left ⟩
            q
        ∎
    prf2 : ∀ q → inv p ■ (p ■ q) ≡ q
    prf2 q =
        begin
            inv p ■ (p ■ q)
        ≡⟨ assoc (inv p) p q ⟩
            (inv p ■ p) ■ q
        ≡⟨ cong (λ { r → r ■ q }) inv-left ⟩
            refl ■ q
        ≡⟨ inv id-left ⟩
            q
        ∎

qinv-concat-right :
    ∀ {l}
    {A : Set l}
    {x y z : A}
    (p : y ≡ z) → 
    ---
    qinv {A = x ≡ y} (λ { q → q ■ p })
qinv-concat-right p = ((λ {q → q ■ (inv p) }) , prf1 , prf2) where
    prf1 : ∀ q → q ■ inv p ■ p ≡ q
    prf1 q =
        begin
            q ■ inv p ■ p
        ≡⟨ inv (assoc q (inv p) p) ⟩
            q ■ (inv p ■ p)
        ≡⟨ cong (λ { r → q ■ r }) inv-left ⟩
            q ■ refl
        ≡⟨ inv id-right ⟩
            q
        ∎
    prf2 : ∀ q → q ■ p ■ inv p ≡ q
    prf2 q =
        begin
            (q ■ p) ■ inv p
        ≡⟨ inv (assoc q p (inv p)) ⟩
            q ■ (p ■ inv p)
        ≡⟨ cong (λ { r → q ■ r }) inv-right ⟩
            q ■ refl
        ≡⟨ inv id-right ⟩
            q
        ∎

-- Example 2.4.9

qinv-transport :
    ∀ {l m}
    {A : Set l}
    {x y : A}
    (p : x ≡ y)
    (P : A → Set m) →
    ---
    qinv (transport P p)
qinv-transport p P = (transport P (inv p) , prf1 , prf2) where
    prf1 : ∀ q → transport P p (transport P (inv p) q) ≡ q
    prf1 q =
        begin
            transport P p (transport P (inv p) q)
        ≡⟨ transport-compose P (inv p) p q ⟩
            transport P (inv p ■ p) q
        ≡⟨ cong (λ { r → transport P r q }) inv-left ⟩
            q 
        ∎
    prf2 : ∀ q → transport P (inv p) (transport P p q) ≡ q
    prf2 q =
        begin
            transport P (inv p) (transport P p q)
        ≡⟨ transport-compose P p (inv p) q ⟩
            transport P (p ■ inv p) q
        ≡⟨ cong (λ { r → transport P r q }) inv-right ⟩
            q
        ∎

-- 2.4.10

isequiv :
    ∀ {l m}
    {A : Set l}
    {B : Set m}
    ---
    (f : A → B) → Set (l ⊔ m)
isequiv {A = A} {B = B} f = (Σ[ g ∈ (B → A) ] ((f ∘ g) ∼ id)) × (Σ[ h ∈ (B → A) ] ((h ∘ f) ∼ id))

-- quasi-inverse implies equivalence

qinv-to-isequiv :
    ∀ {l m}
    {A : Set l}
    {B : Set m}
    (f : A → B) →
    ---
    qinv f → isequiv f
qinv-to-isequiv f (g , α , β) = ((g , α) , (g , β))

-- equivalence implies quasi-inverse

isequiv-to-qinv :
    ∀ {l m}
    {A : Set l}
    {B : Set m}
    (f : A → B) →
    isequiv f → qinv f
isequiv-to-qinv f ((g , α) , (h , β))= (g , α , β') where
    β' : (g ∘ f) ∼ id
    β' x = inv (β (g (f x))) ■ ap h (α (f x)) ■ β x

-- 2.4.11

infix 30 _≃_
_≃_ :
    ∀ {l m} →
    ---
    Set l → Set m → Set (l ⊔ m)
A ≃ B = Σ[ f ∈ (A → B) ] (isequiv f)

-- Lemma 2.4.12(i)

type-equiv-refl :
    ∀ {l}
    {A : Set l} →
    ---
    A ≃ A
type-equiv-refl = ( id , ((( id , λ { x → refl } )) , (id , λ { x → refl } )))

-- Lemma 2.4.12(ii)

type-equiv-symm :
    ∀ {l m}
    {A : Set l}
    {B : Set m} →
    ---
    A ≃ B → B ≃ A
type-equiv-symm (f , (g , H1) , (h , H2)) =
    (g ,
    (f , λ { x → (inv (H2 (g (f x)))) ■ ((cong h (H1 (f x))) ■ H2 x) }) ,
    (f , H1))

-- Lemma 2.4.12(iii)

type-equiv-tran :
    ∀ {l m n}
    {A : Set l}
    {B : Set m}
    {C : Set n} →
    ---
    A ≃ B → B ≃ C → A ≃ C
type-equiv-tran
    (f  , (g  , H1 ) , (h  , H2 ))
    (f' , (g' , H1') , (h' , H2')) =
        (f' ∘ f ,
        (g ∘ g' , λ { x → (cong f' (H1 (g' x))) ■ (H1' x) }) ,
        (h ∘ h' , λ { x → (cong h (H2' (f x))) ■ (H2 x) } ))