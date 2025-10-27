
----
---- Práctica 5: Programas correctos por construcción
----

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≟_; s≤s⁻¹)
open import Data.Nat.Properties using (≤-step; ≤-refl; ≤-trans; +-monoʳ-≤)
open import Relation.Nullary using (Dec; yes; no; ¬_)

-- Recordemos la definición de algunas funciones básicas sobre listas:

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : {A : Set} → List A → ℕ
length []       = zero
length (_ ∷ xs) = suc (length xs)

reverse : {A : Set} → List A → List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

---- Parte A ----

-- A.1) Demostrar que dada una lista xs y un entero k ≤ length xs,
-- es posible partir la lista xs en un prefijo ys de longitud k
-- seguido de un sufijo zs.

split : {A : Set} (xs : List A) (k : ℕ)
      → k ≤ length xs
      → Σ[ ys ∈ List A ] Σ[ zs ∈ List A ] ((xs ≡ ys ++ zs) × k ≡ length ys)
split []       zero    0≤#xs   = [] , [] , refl , refl
split (x ∷ xs) zero    0≤#xs   = [] , x ∷ xs , refl , refl
split (x ∷ xs) (suc m) k≤#x∷xs = 
  let (ys' , zs' , xs≡ys'++zs' , m≤#xs) = split xs m (s≤s⁻¹ k≤#x∷xs) in
  x ∷ ys' , zs' , cong (x ∷_) xs≡ys'++zs' , cong suc m≤#xs

-- Definimos un predicado "x ∈ ys" que es verdadero si x aparece en ys:

data _∈_ : ℕ → List ℕ → Set where
  zero : {x : ℕ} {xs : List ℕ} → x ∈ (x ∷ xs)
  suc  : {x y : ℕ} {xs : List ℕ} → x ∈ xs → x ∈ (y ∷ xs)

-- A.2) Demostrar que es posible decidir si un número natural aparece en una lista.
-- (Usar _≟_ para decidir la igualdad de números naturales).

lema1 : {x y : ℕ} {ys : List ℕ} → x ≡ y → x ∈ (y ∷ ys)
lema1 {x} {y} {ys} refl = zero 

∈-decidible : {x : ℕ} {ys : List ℕ} → Dec (x ∈ ys)
∈-decidible {x} {[]} = no (λ ())
∈-decidible {x} {y ∷ ys} 
  with ∈-decidible {x} {ys}
... | yes x∈ys = yes (suc x∈ys)
... | no  x∉ys 
    with x ≟ y 
...   | yes x=y = yes (lema1 x=y)
...   | no  x≠y = no λ{ (suc x∈ys) → x∉ys x∈ys; zero → x≠y refl } 

-- A.3) Demostrar que la igualdad de listas es decidible
-- asumiendo que es decidible la igualdad de sus elementos.

∷-inv₁ : {A : Set} {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
∷-inv₁ refl = refl

∷-inv₂ : {A : Set} {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷-inv₂ refl = refl

lema4 : {A : Set} {x y : A} {xs ys : List A} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
lema4 refl refl = refl


List-igualdad-decidible : {A : Set}
                        → ((x y : A) → Dec (x ≡ y))
                        → ((xs ys : List A) → Dec (xs ≡ ys))
List-igualdad-decidible eq []       []       = yes refl
List-igualdad-decidible eq []       (y ∷ ys) = no λ ()
List-igualdad-decidible eq (x ∷ xs) []       = no λ ()
List-igualdad-decidible eq (x ∷ xs) (y ∷ ys) 
  with eq x y
... | no ¬x≡y = no λ x∷xs≡y∷ys → ¬x≡y (∷-inv₁ x∷xs≡y∷ys)  
... | yes x≡y 
    with List-igualdad-decidible eq xs ys
...   | yes xs≡ys = yes (lema4 x≡y xs≡ys)
...   | no ¬xs≡ys = no λ x∷xs≡y∷ys → ¬xs≡ys (∷-inv₂ x∷xs≡y∷ys)

---- Parte B ----

infix  3 _~_
infix  3 _<<_
infixr 3 _~⟨_⟩_
infix  4 _~∎

-- Considerar el siguiente tipo de las permutaciones:

data _~_ : List ℕ → List ℕ → Set where
  ~-empty : [] ~ []
  ~-cons  : {x : ℕ} {xs ys : List ℕ}
          → xs ~ ys
          → x ∷ xs ~ x ∷ ys
  ~-swap  : {x y : ℕ} {xs ys : List ℕ}
          → xs ~ ys
          → x ∷ y ∷ xs ~ y ∷ x ∷ ys
  ~-trans : {xs ys zs : List ℕ}
          → xs ~ ys
          → ys ~ zs
          → xs ~ zs

-- B.1) Demostrar que "~" es reflexiva:

~-refl : {xs : List ℕ} → xs ~ xs
~-refl {[]} = ~-empty
~-refl {x ∷ xs} = ~-cons (~-refl {xs})

-- Definimos operadores auxiliares para poder hacer razonamiento ecuacional
-- con permutaciones:

_~⟨_⟩_ : (xs : List ℕ)
       → {ys : List ℕ} → xs ~ ys
       → {zs : List ℕ} → ys ~ zs
       → xs ~ zs
_ ~⟨ p ⟩ q = ~-trans p q

_~∎ : (xs : List ℕ) → xs ~ xs
_ ~∎ = ~-refl

-- B.2) Demostrar que "~" es simétrica:

~-sym : {xs ys : List ℕ} → xs ~ ys → ys ~ xs
~-sym ~-empty       = ~-empty
~-sym (~-cons p)    = ~-cons (~-sym p)
~-sym (~-swap p)    = ~-swap (~-sym p)
~-sym (~-trans p q) = ~-trans (~-sym q) (~-sym p)

-- B.3) Demostrar que "~" es una congruencia con respecto a la concatenación de listas:

~-++ : {xs ys xs' ys' : List ℕ}
     → xs ~ xs'
     → ys ~ ys'
     → xs ++ ys ~ xs' ++ ys'
~-++ {xs}             {ys} {xs'}               {ys'} ~-empty         q = q
~-++ {x ∷ xs}         {ys} {x' ∷ xs'}          {ys'} (~-cons p)      q = ~-cons (~-++ p q)
~-++ {x₁ ∷ (x₂ ∷ xs)} {ys} {x'₁ ∷ (x'₂ ∷ xs')} {ys'} (~-swap p)      q = ~-swap (~-++ p q)
~-++ {xs}             {ys} {xs'}               {ys'} (~-trans p₁ p₂) q = ~-trans (~-++ p₁ q) (~-++ p₂ ~-refl)

-- B.4) Demostrar que una lista invertida es permutación de la lista original:

~-push : {x : ℕ} {xs : List ℕ} → (xs ++ (x ∷ [])) ~ x ∷ xs
~-push {x} {[]} = ~-refl
~-push {x} {x₁ ∷ xs} = 
      x₁ ∷ (xs ++ (x ∷ [])) 
    ~⟨ ~-cons ~-push ⟩ 
      x₁ ∷ x ∷ xs
    ~⟨ ~-swap ~-refl ⟩ 
      x ∷ x₁ ∷ xs
    ~∎

~-reverse : {xs : List ℕ} → reverse xs ~ xs
~-reverse {[]}     = ~-empty
~-reverse {x ∷ xs} =
    reverse (x ∷ xs)
  ~⟨ ~-refl ⟩
    reverse xs ++ (x ∷ [])
  ~⟨ ~-++ (~-reverse {xs}) ~-refl ⟩
    xs ++ (x ∷ [])
  ~⟨ ~-push ⟩
    x ∷ xs
  ~∎

----

-- Definimos una función que vale 1 si dos números son iguales, y 0 si no.
iguales? : ℕ → ℕ → ℕ
iguales? x y with x ≟ y
... | yes _ = 1
... | no  _ = 0

-- Definimos una función que cuenta el número de apariciones de un
-- número natural en una lista.
cantidad-apariciones : ℕ → List ℕ → ℕ
cantidad-apariciones x []       = zero
cantidad-apariciones x (y ∷ ys) = iguales? x y + cantidad-apariciones x ys

-- Definimos un predicado xs << ys
-- que es verdadero si cada natural z
-- aparece en xs a lo sumo tantas veces como aparece en ys:

_<<_ : List ℕ → List ℕ → Set
xs << ys = (z : ℕ) → cantidad-apariciones z xs ≤ cantidad-apariciones z ys

-- B.5) Demostrar las siguientes propiedades de "<<":

<<-empty : [] << []
<<-empty = λ z → _≤_.z≤n

<<-refl : {xs : List ℕ} → xs << xs
<<-refl z = ≤-refl    -- útil: Data.Nat.Properties.≤-refl 

<<-cons : {x : ℕ} {xs ys : List ℕ} → xs << ys → x ∷ xs << x ∷ ys
<<-cons {x} xs<<ys z = +-monoʳ-≤ (iguales? z x) (xs<<ys z)    -- útil:   +-monoʳ-≤ (iguales? z x) ?

<<-swap : {x y : ℕ} {xs ys : List ℕ} → xs << ys → x ∷ y ∷ xs << y ∷ x ∷ ys
<<-swap {x} {y} xs<<ys z = 
  let 
    a = +-monoʳ-≤ (iguales? z x) (xs<<ys z) 
    b = +-monoʳ-≤ (iguales? z y) (xs<<ys z) 
    c = +-monoʳ-≤ (iguales? z x + iguales? z y) (xs<<ys z) 
  in {!   !}
-- útil: Data.Nat.Properties.+-monoʳ-≤

<<-trans : {xs ys zs : List ℕ} → xs << ys → ys << zs → xs << zs
<<-trans xs<<ys ys<<zs z = ≤-trans (xs<<ys z) (ys<<zs z)    -- útil: Data.Nat.Properties.≤-trans

-- B.6) Usando los lemas de B.5, demostrar que la relación "~" es
-- correcta con respecto a "<<".

~-correcta : {xs ys : List ℕ}
           → xs ~ ys 
           → xs << ys 
~-correcta                           ~-empty       = <<-empty
~-correcta {x ∷ xs} {x ∷ ys}         (~-cons p)    = <<-cons {x} {xs} {ys} (~-correcta {xs} {ys} p)
~-correcta {x ∷ y ∷ xs} {y ∷ x ∷ ys} (~-swap p)    = <<-swap {x} {y} {xs} {ys} (~-correcta p)
~-correcta {xs}     {ys}             (~-trans {xs} {zs} {ys} p q) = <<-trans {xs} {zs} {ys} (~-correcta p) (~-correcta q)
