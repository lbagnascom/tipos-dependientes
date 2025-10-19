
----
---- Práctica 3: Estructura de ω-grupoide y transporte
----

open import Data.Empty
       using (⊥; ⊥-elim)
open import Data.Bool
       using (Bool; true; false)
open import Data.Nat
       using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties
       using (+-comm)
open import Data.Product
       using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality
       using (_≡_; refl; cong)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

---- Parte A ----

-- Considerar las siguientes definiciones de la composición de caminos (transitividad)
-- e inversa de un camino (simetría). Son equivalentes a sym y trans pero cambiando
-- la notación.

_∙_ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ refl = refl

_⁻¹ : {A : Set} {x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

-- A.1) Demostrar que la reflexividad es el neutro de la composición de caminos
-- a izquierda y a derecha.

∙-refl-left : {A : Set} {x y : A} {p : x ≡ y}
            → refl ∙ p ≡ p
∙-refl-left {p = refl} = refl

∙-refl-right : {A : Set} {x y : A} {p : x ≡ y}
             → p ∙ refl ≡ p
∙-refl-right {p = refl} = refl

-- A.2) Demostrar que la composición de caminos es asociativa.

∙-assoc : {A : Set} {x y z w : A} {p : x ≡ y} {q : y ≡ z} {r : z ≡ w}
        → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙-assoc {A} {x} {y} {z} {w} {p = refl} {q} {r} = 
  begin
    (refl ∙ q) ∙ r 
  ≡⟨ cong (λ pp → pp ∙ r) ∙-refl-left ⟩ 
    q ∙ r
  ≡⟨ ∙-refl-left ⁻¹ ⟩ 
    refl ∙ (q ∙ r)
  ∎

-- A.3) Demostrar que la inversa es efectivamente la inversa, a izquierda y a derecha.

∙-⁻¹-left : {A : Set} {x y : A} {p : x ≡ y}
            → (p ⁻¹) ∙ p ≡ refl
∙-⁻¹-left {p = refl} = refl

∙-⁻¹-right : {A : Set} {x y : A} {p : x ≡ y}
            → p ∙ (p ⁻¹) ≡ refl
∙-⁻¹-right {p = refl} = refl

-- A.4) Usando las propiedades anteriores y sin hacer pattern matching sobre los caminos,
-- completar la demostración de que la inversa es involutiva:

⁻¹-involutive : {A : Set} {x y : A} {p : x ≡ y}
              → (p ⁻¹) ⁻¹ ≡ p
⁻¹-involutive {A} {x} {y} {p} =
    (p ⁻¹) ⁻¹
  ≡⟨ ∙-refl-right ⁻¹ ⟩
    ((p ⁻¹) ⁻¹) ∙ refl
  ≡⟨ cong (λ pp → ((p ⁻¹) ⁻¹) ∙ pp) (∙-⁻¹-left ⁻¹) ⟩
    ((p ⁻¹) ⁻¹) ∙ ((p ⁻¹) ∙ p)
  ≡⟨ ∙-assoc ⁻¹ ⟩
    (((p ⁻¹) ⁻¹) ∙ (p ⁻¹)) ∙ p
  ≡⟨ cong (λ pp → pp ∙ p) ∙-⁻¹-left ⟩
    refl ∙ p
  ≡⟨ ∙-refl-left  ⟩
    p
  ∎

-- A.5) Usando las propiedades anteriores y sin hacer pattern matching sobre los caminos,
-- demostrar las siguientes propiedades de cancelación a izquierda y a derecha:

∙-cancel-left : {A : Set} {x y z : A} {p : x ≡ y} {q q' : y ≡ z}
             → p ∙ q ≡ p ∙ q'
             → q ≡ q'
∙-cancel-left {A} {x} {y} {z} {p} {q} {q'} pq≡pq' =
  begin
    q
  ≡⟨ ∙-refl-left ⁻¹ ⟩
    refl ∙ q
  ≡⟨ cong (λ r → r ∙ q) (∙-⁻¹-left ⁻¹) ⟩
    ((p ⁻¹) ∙ p) ∙ q
  ≡⟨ ∙-assoc ⟩
    (p ⁻¹) ∙ (p ∙ q)
  ≡⟨ cong (λ r → (p ⁻¹) ∙ r) pq≡pq' ⟩
    (p ⁻¹) ∙ (p ∙ q')
  ≡⟨ ∙-assoc ⁻¹ ⟩
    ((p ⁻¹) ∙ p) ∙ q'
  ≡⟨ cong (λ r → r ∙ q') (∙-⁻¹-left) ⟩
    refl ∙ q'
  ≡⟨ ∙-refl-left ⟩
    q'
  ∎

∙-cancel-right : {A : Set} {x y z : A} {p p' : x ≡ y} {q : y ≡ z}
               → p ∙ q ≡ p' ∙ q
               → p ≡ p'
∙-cancel-right {A} {x} {y} {z} {p} {p'} {q} pq≡p'q = 
    begin
      p
    ≡⟨ ∙-refl-right ⁻¹ ⟩
      p ∙ refl
    ≡⟨ cong ((λ r → p ∙ r)) (∙-⁻¹-right ⁻¹) ⟩
      p ∙ (q ∙ (q ⁻¹))
    ≡⟨ ∙-assoc ⁻¹ ⟩
      (p ∙ q) ∙ (q ⁻¹)
    ≡⟨ cong (λ r → r ∙ (q ⁻¹)) pq≡p'q ⟩
      (p' ∙ q) ∙ (q ⁻¹)
    ≡⟨ ∙-assoc ⟩
      p' ∙ (q ∙ (q ⁻¹))
    ≡⟨ cong (λ r → p' ∙ r) (∙-⁻¹-right) ⟩
      p' ∙ refl
    ≡⟨ ∙-refl-right ⟩
      p'
    ∎

-- A.6) Usando las propiedades anteriores y sin hacer pattern matching sobre los caminos,
-- demostrar las siguientes propiedades, que caracterizan a la inversa a izquierda y
-- a derecha:

⁻¹-univ-left : {A : Set} {x y z : A} {p : x ≡ y} {q : y ≡ x}
             → p ∙ q ≡ refl
             → p ≡ q ⁻¹
⁻¹-univ-left {A} {x} {y} {z} {p} {q} p∙q≡refl = 
    let 
      p∙q≡q⁻¹∙q = 
        begin
          p ∙ q
        ≡⟨ p∙q≡refl ⟩
          refl
        ≡⟨ ∙-⁻¹-left ⁻¹ ⟩
          (q ⁻¹) ∙ q
        ∎
    in ∙-cancel-right p∙q≡q⁻¹∙q

-- Otra demo:
    -- begin
    --   p
    -- ≡⟨ ∙-refl-right ⁻¹ ⟩
    --   p ∙ refl
    -- ≡⟨ cong (λ r → p ∙ r) (∙-⁻¹-right ⁻¹) ⟩
    --   p ∙ (q ∙ (q ⁻¹))
    -- ≡⟨ ∙-assoc ⁻¹ ⟩
    --   (p ∙ q) ∙ (q ⁻¹)
    -- ≡⟨ cong (λ r → r ∙ (q ⁻¹)) p∙q≡refl ⟩
    --   refl ∙ (q ⁻¹)
    -- ≡⟨ ∙-refl-left ⟩
    --   (q ⁻¹)
    -- ∎


⁻¹-univ-right : {A : Set} {x y z : A} {p : x ≡ y} {q : y ≡ x}
              → p ∙ q ≡ refl
              → q ≡ p ⁻¹
⁻¹-univ-right  {A} {x} {y} {z} {p} {q} p∙q≡refl =
  let 
      p∙q≡p∙p⁻¹ = 
        begin
          p ∙ q
        ≡⟨ p∙q≡refl ⟩
          refl
        ≡⟨ ∙-⁻¹-right ⁻¹ ⟩
          p ∙ (p ⁻¹)
        ∎
  in ∙-cancel-left p∙q≡p∙p⁻¹

-- A.7) Usando las propiedades anteriores y sin hacer pattern matching sobre los caminos,
-- demostrar la siguiente propiedad de conmutación entre la composición de caminos y
-- la inversa:

∙-⁻¹-comm : {A : Set} {x y z : A} {p : x ≡ y} {q : y ≡ z}
             → (p ∙ q)⁻¹ ≡ (q ⁻¹) ∙ (p ⁻¹)
∙-⁻¹-comm {A} {x} {y} {z} {p} {q} =
    let
      isinverse-p∙q = 
        begin
          ((q ⁻¹) ∙ (p ⁻¹)) ∙ (p ∙ q)
        ≡⟨ ∙-assoc ⟩
          (q ⁻¹) ∙ ((p ⁻¹) ∙ (p ∙ q))
        ≡⟨ cong (λ r → (q ⁻¹) ∙ r) (∙-assoc ⁻¹) ⟩
          (q ⁻¹) ∙ (((p ⁻¹) ∙ p) ∙ q)
        ≡⟨ cong (λ r → (q ⁻¹) ∙ (r ∙ q)) (∙-⁻¹-left) ⟩
          (q ⁻¹) ∙ (refl ∙ q)
        ≡⟨ cong (λ r → (q ⁻¹) ∙ r) (∙-refl-left) ⟩
          (q ⁻¹) ∙ q
        ≡⟨ ∙-⁻¹-left ⟩
          refl
        ∎
    in
      (⁻¹-univ-left {A} {z} {x} {y} isinverse-p∙q) ⁻¹

---- Parte B ----

-- Usamos los booleanos para representar bits (false = 0 ; true = 1).
-- Consideramos la siguiente función auxiliar:
_+bit_ : Bool → ℕ → ℕ
false +bit n = n
true  +bit n = suc n

-- Consideramos el siguiente tipo de datos para codificar naturales en binario:
data Bin : Set where
  binzero : Bin
  addbit  : Bin → Bool → Bin

-- Donde:
-- ─ b0 representa el 0
-- ─ Si x : Bin, entonces addbit x b es el número que resulta de agregar el bit b a la derecha
--   (es decir, "b +bit (2 * x)").
-- Por ejemplo,
--   addbit (addbit (addbit binzero true) false) false
-- codifica el número (100)₂ = 4.

2* : ℕ → ℕ
2* n = n + n

-- B.1) Definir la función que convierte un número representado en binario a natural:
bin2nat : Bin → ℕ
bin2nat binzero      = zero
bin2nat (addbit x b) = b +bit (2* (bin2nat x))


-- B.2) Definir la función sucesor sobre números naturales representados en binario:
binsuc : Bin → Bin
binsuc binzero          = addbit binzero true
binsuc (addbit x false) = addbit x true
binsuc (addbit x true)  = addbit (binsuc x) false

-- B.3) Usando binsuc, definir la función que convierte un número natural a su representación binaria:
nat2bin : ℕ → Bin
nat2bin zero = binzero
nat2bin (suc n) = binsuc (nat2bin n)

b2n·bsuc≡suc·b2n : {b : Bin} → bin2nat (binsuc b) ≡ suc (bin2nat b)
b2n·bsuc≡suc·b2n {binzero} = refl
b2n·bsuc≡suc·b2n {addbit x false} = refl
b2n·bsuc≡suc·b2n {addbit x true} = 
  begin
    bin2nat (binsuc (addbit x true))
  ≡⟨⟩
    bin2nat (addbit (binsuc x) false)
  ≡⟨⟩
    false +bit (2* (bin2nat (binsuc x)))
  ≡⟨⟩
    2* (bin2nat (binsuc x))
  ≡⟨ cong 2* (b2n·bsuc≡suc·b2n {x}) ⟩
    2* (suc (bin2nat x))
  ≡⟨⟩
    suc (bin2nat x) + suc (bin2nat x)
  ≡⟨⟩
    suc ((bin2nat x) + suc (bin2nat x))
  ≡⟨ cong suc (+-comm (bin2nat x) (suc (bin2nat x))) ⟩
    suc ((suc (bin2nat x)) + (bin2nat x))
  ≡⟨⟩
    suc (suc ((bin2nat x) + (bin2nat x)))
  ≡⟨⟩
    suc (suc (2* (bin2nat x)))
  ≡⟨⟩
    suc (true +bit (2* (bin2nat x)))
  ≡⟨⟩
    suc (bin2nat (addbit x true))
  ∎


-- B.4) Demostrar que bin2nat es la inversa a izquierda de nat2bin:
nat2bin2nat : (n : ℕ) → bin2nat (nat2bin n) ≡ n
nat2bin2nat zero = refl
nat2bin2nat (suc n) =
  begin
    bin2nat (nat2bin (suc n))
  ≡⟨⟩
    bin2nat (binsuc (nat2bin n))
  ≡⟨ b2n·bsuc≡suc·b2n {nat2bin n} ⟩
    suc (bin2nat (nat2bin n))
  ≡⟨ cong suc (nat2bin2nat n) ⟩
    suc n
  ∎

+bit-comm-suc : {r : Bool} → {n : ℕ} → (r +bit (suc n)) ≡ suc (r +bit n)
+bit-comm-suc {false} = refl
+bit-comm-suc {true}  = refl

-- B.5) Definir la siguiente función, que descompone un número natural en su cociente y su resto
-- en la división por 2:
divmod2 : (n : ℕ) → Σ[ q ∈ ℕ ] Σ[ r ∈ Bool ] n ≡ r +bit (q + q)
divmod2 zero          = zero , false , refl
divmod2 (suc zero)    = zero , true , refl
divmod2 (suc (suc n)) = 
  let 
    (q' , r , n≡q+q+r) = divmod2 n 
    q = suc q'
  in
    q , r , 
    (begin
      suc (suc n)
    ≡⟨ cong (λ x → suc (suc x)) n≡q+q+r ⟩
      suc (suc (r +bit (q' + q'))) 
    ≡⟨ cong suc (+bit-comm-suc ⁻¹) ⟩
      suc (r +bit (suc (q' + q'))) 
    ≡⟨ +bit-comm-suc ⁻¹ ⟩
      r +bit (suc (suc (q' + q')))
    ≡⟨⟩
      r +bit (suc (q + q'))
    ≡⟨ cong (λ x → r +bit (suc x)) (+-comm q q') ⟩
      r +bit (suc (q' + q))
    ≡⟨⟩
      r +bit (q + q)
    ∎
    )

---- Parte C ----

-- Recordemos el operador de transporte:
transport : {A : Set} (B : A → Set) {x y : A} (p : x ≡ y) → B x → B y
transport _ refl b = b

-- C.1) Demostrar que transportar por la familia (B ∘ f) vía el camino p
-- equivale a transportar por la familia B vía el camino (cong f p).
transport-compose : {A A' : Set} (f : A → A') (B : A' → Set) {x y : A} (p : x ≡ y) (b : B (f x))
           → transport (λ x → B (f x)) p b ≡ transport B (cong f p) b
transport-compose {A} {A'} f B {x} {y} refl b = 
  begin
    transport (λ x' → B (f x')) refl b
  ≡⟨⟩
    b
  ≡⟨⟩
    transport B refl b
  ≡⟨⟩
    transport B (cong f refl) b
  ∎

-- C.2) Demostrar que transportar vía la composición de dos caminos
-- equivale a transportar separadamente vía cada uno de ellos.
transport-∙ : {A : Set} (B : A → Set) {x y z : A} (p : x ≡ y) (q : y ≡ z) (b : B x)
           → transport B (p ∙ q) b ≡ transport B q (transport B p b)
transport-∙ {A} B {x} {y} {z} refl refl b = refl 

--  Otra forma con un único pattern matching
  -- begin
  --   transport B (refl ∙ q) b 
  -- ≡⟨ cong (λ h → transport B h b) ∙-refl-left  ⟩
  --   transport B q b
  -- ≡⟨⟩
  --   transport B q (transport B refl b)
  -- ∎

-- C.3) Demostrar que transportar por una familia constante es la identidad.
transport-const : {A : Set} (B₀ : Set) {x y : A} (p : x ≡ y) (b : B₀)
                → transport (λ _ → B₀) p b ≡ b
transport-const {A} B₀ {x} {y} refl b = refl
-- De qué otra forma se podría demostrar?

-- C.4) Demostrar que transportar por una familia de caminos corresponde a componer: 
transport-path-left : {A : Set} {x y z : A} (p : x ≡ y) (q : x ≡ z)
                    → transport (λ a → a ≡ z) p q ≡ (p ⁻¹) ∙ q
transport-path-left {A} {x} {y} {z} refl refl = refl

-- C.5) Similar pero con la composición a derecha:
transport-path-right : {A : Set} {x y z : A} (p : x ≡ y) (q : z ≡ x)
                     → transport (λ a → z ≡ a) p q ≡ q ∙ p
transport-path-right {A} {x} {y} {z} refl refl = refl

---- Parte D ----

-- Definimos una familia `Fin n` indexada por `n : ℕ`.
-- Informalmente, `Fin n` es el tipo finito cuyos elementos son {0, 1, ..., n}.
data Fin : (n : ℕ) → Set where
  -- finZero es el único habitante de Fin 1
  finZero : Fin zero
  -- Si x es un habitante de Fin n,
  -- entonces finSuc x es un habitante de Fin (suc n).
  finSucc  : {n : ℕ} → Fin n → Fin (suc n)

-- D.1) Definir la suma:
sumaFin : {n m : ℕ} → Fin n → Fin m → Fin (n + m)
sumaFin finZero     y = y
sumaFin (finSucc x) y = finSucc (sumaFin x y)

-- D.2) Demostrar que la suma es conmutativa:
sumaFin-comm : {n m : ℕ} (x : Fin n) (y : Fin m) → sumaFin x y ≡ transport Fin (+-comm m n) (sumaFin y x)
sumaFin-comm {zero} {m} finZero y = {!   !}
sumaFin-comm {n} {m} (finSucc x) y = {!   !}

