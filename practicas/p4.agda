
open import Data.Unit
       using (⊤; tt)
open import Data.Empty
       using (⊥; ⊥-elim)
open import Data.Bool
       using (Bool; true; false)
open import Data.Nat
       using (ℕ; zero; suc; _+_)
open import Data.Sum
       using (_⊎_; inj₁; inj₂)
open import Data.Product
       using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary.PropositionalEquality
       using (_≡_; refl; sym; trans; cong)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

-- Definimos la composición:
infixr 80 _∘_
_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(g ∘ f) a = g (f a)

-- Parte A --

-- Recordemos la definición del tipo de datos de las listas:

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

-- Recordemos la definición de algunas funciones básicas:

map : {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- A.1) Demostrar que map conmuta con la concatenación:
map-++ : {A B : Set} {f : A → B} {xs ys : List A}
       → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ {A} {B} {f} {[]} {ys} = refl
map-++ {A} {B} {f} {x ∷ xs} {ys} = cong (f x ∷_) (map-++ {A} {B} {f} {xs} {ys})

-- A.2) Demostrar que map conmuta con la composición:
map-∘ : {A B C : Set} {f : A → B} {g : B → C} {xs : List A}
       → map (g ∘ f) xs ≡ map g (map f xs)
map-∘ {A} {B} {C} {f} {g} {[]} = refl
map-∘ {A} {B} {C} {f} {g} {x ∷ xs} = cong ((g ∘ f) x ∷_) (map-∘ {A} {B} {C} {f} {g} {xs})

-- Definimos el siguiente predicado que se verifica si un elemento
-- aparece en una lista:

_∈_ : {A : Set} → A → List A → Set
x ∈ []       = ⊥
x ∈ (y ∷ ys) = (x ≡ y) ⊎ (x ∈ ys)

-- A.3) Demostrar que si un elemento aparece en la concatenación de
-- dos listas, debe aparecer en alguna de ellas:
∈-++ : ∀ {A : Set} {z : A} {xs ys : List A}
       → z ∈ (xs ++ ys)
       → (z ∈ xs) ⊎ (z ∈ ys)
∈-++ {A} {z} {[]}     {ys} z∈xs++ys = inj₂ z∈xs++ys
∈-++ {A} {z} {x ∷ xs} {ys} (inj₁ z≡x) = inj₁ (inj₁ z≡x)
∈-++ {A} {z} {x ∷ xs} {ys} (inj₂ z∈xs++ys) with (∈-++ {A} {z} {xs} {ys} z∈xs++ys)
...    | inj₁ z∈xs = inj₁ (inj₂ z∈xs)
...    | inj₂ z∈ys = inj₂ z∈ys

-- A.4) Demostrar que si un elemento z aparece en una lista xs,
-- su imagen (f z) aparece en (map f xs):
∈-map : ∀ {A B : Set} {f : A → B} {z : A} {xs : List A}
        → z ∈ xs
        → f z ∈ map f xs
∈-map {A} {B} {f} {z} {[]} ()
∈-map {A} {B} {f} {z} {x ∷ xs} z∈xs with z∈xs
...    | inj₁ z≡x  = inj₁ (cong f z≡x)
...    | inj₂ z∈xs = inj₂ (∈-map {A} {B} {f} {z} {xs} z∈xs)

-- Definimos el siguiente predicado que se verifica si todos los
-- elementos de una lista son iguales:

todos-iguales : {A : Set} → List A → Set
todos-iguales []             = ⊤
todos-iguales (x ∷ [])       = ⊤
todos-iguales (x ∷ (y ∷ ys)) = (x ≡ y) × todos-iguales (y ∷ ys)

-- A.5) Demostrar:
todos-iguales-map : {A B : Set} {f : A → B} {xs : List A}
                  → todos-iguales xs
                  → todos-iguales (map f xs)
todos-iguales-map {A} {B} {f} {[]}     tod-ig-xs       = tod-ig-xs
todos-iguales-map {A} {B} {f} {x ∷ []} tod-ig-xs       = tod-ig-xs
todos-iguales-map {A} {B} {f} {x ∷ (y ∷ ys)} (x≡y , tod-ig-ys) = cong f x≡y 
                                                               , todos-iguales-map {A} {B} {f} {y ∷ ys} tod-ig-ys

-- Parte B --

-- Definimos siguiente el tipo de las equivalencias de tipos.
--
-- Nota: estrictamente hablando, usamos la condición que afirma
-- que la función "to" tiene una quasi-inversa y no que es una
-- equivalencia.

record _≃_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : (a : A) → from (to a) ≡ a
    to∘from : (b : B) → to (from b) ≡ b

open _≃_

-- B.1) Demostrar que la equivalencia de tipos es reflexiva, simétrica y transitiva:

≃-refl : ∀ {A} → A ≃ A
≃-refl = record { 
    to = λ x → x ; 
    from = λ x → x ; 
    from∘to = λ a → refl ; 
    to∘from = λ b → refl 
    }

≃-sym : ∀ {A B} → A ≃ B → B ≃ A
≃-sym A≃B = record { 
    to = from A≃B ; 
    from = to A≃B ; 
    from∘to = to∘from A≃B ; 
    to∘from = from∘to A≃B 
    }

≃-trans : ∀ {A B C} → A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C = 
    let 
        from∘to-A≃C x = 
            begin
                (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x) 
            ≡⟨⟩
                from A≃B (from B≃C (to B≃C (to A≃B x)))
            ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
                from A≃B (to A≃B x)
            ≡⟨ from∘to A≃B x ⟩
                x
            ∎
        
        to∘from-A≃C x = 
            begin
                (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) x) 
            ≡⟨⟩
                to B≃C (to A≃B (from A≃B (from B≃C x)))
            ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C x)) ⟩
                to B≃C (from B≃C x)
            ≡⟨ to∘from B≃C x ⟩
                x
            ∎
    in
    record { 
            to = to B≃C ∘ to A≃B ;
            from = from A≃B ∘ from B≃C ;
            from∘to = λ a → from∘to-A≃C a ;
            to∘from = λ a → to∘from-A≃C a
    }

-- B.2) Demostrar que el producto de tipos es conmutativo, asociativo,
-- y que ⊤ es el elemento neutro:

×-comm : {A B : Set} → (A × B) ≃ (B × A)
×-comm = record { 
    to = λ p → proj₂ p , proj₁ p ; 
    from = λ p → proj₂ p , proj₁ p  ; 
    from∘to = λ a → refl ; 
    to∘from = λ b → refl 
    }

×-assoc : {A B C : Set} → (A × (B × C)) ≃ ((A × B) × C)
×-assoc = record {
    to = λ p → ((proj₁ p , proj₁ (proj₂ p)) , proj₂ (proj₂ p)) ;
    from = λ p → proj₁ (proj₁ p) , (proj₂ (proj₁ p) , proj₂ p) ;
    from∘to = λ a → refl;
    to∘from = λ b → refl 
    }

×-⊤-neut : {A : Set} → (A × ⊤) ≃ A
×-⊤-neut = record { 
    to = proj₁ ; 
    from = _, tt ; 
    from∘to = λ a → refl ; 
    to∘from = λ b → refl 
    }

-- B.3) Demostrar que la suma de tipos es conmutativa, asociativa,
-- y que ⊥ es el elemento neutro:

⊎-comm₀ : {A B : Set} → (A ⊎ B) → (B ⊎ A)
⊎-comm₀ A⊎B with A⊎B
... | inj₁ a = inj₂ a
... | inj₂ b = inj₁ b

⊎-comm₁ : {A B : Set} {x : A ⊎ B} → ⊎-comm₀ (⊎-comm₀ x) ≡ x
⊎-comm₁ {A} {B} {x} with x
... | inj₁ a = refl
... | inj₂ b = refl

⊎-comm : {A B : Set} → (A ⊎ B) ≃ (B ⊎ A)
⊎-comm {A} {B} = 
    record { 
        to = ⊎-comm₀ {A} {B}; 
        from = ⊎-comm₀ {B} {A} ; 
        from∘to = λ a → ⊎-comm₁ ; 
        to∘from = λ b → ⊎-comm₁ 
    }

⊎-assoc₀ : {A B C : Set} → (A ⊎ (B ⊎ C)) → ((A ⊎ B) ⊎ C)
⊎-assoc₀ {A} {B} {C} A⊎-B⊎C with A⊎-B⊎C
... | inj₁ a = inj₁ (inj₁ a)
... | inj₂ (inj₁ b) = inj₁ (inj₂ b)
... | inj₂ (inj₂ c) = inj₂ c

⊎-assoc₁ : {A B C : Set} → ((A ⊎ B) ⊎ C) → (A ⊎ (B ⊎ C))
⊎-assoc₁ {A} {B} {C} A⊎B-⊎C with A⊎B-⊎C
... | inj₁ (inj₁ a) = inj₁ a
... | inj₁ (inj₂ b) = inj₂ (inj₁ b)
... | inj₂ c = inj₂ (inj₂ c)

⊎-assoc₂ : {A B C : Set} → {x : A ⊎ (B ⊎ C)} → ⊎-assoc₁ (⊎-assoc₀ x) ≡ x
⊎-assoc₂ {A} {B} {C} {A⊎-B⊎C} with A⊎-B⊎C
... | inj₁ a        = refl
... | inj₂ (inj₁ b) = refl
... | inj₂ (inj₂ c) = refl

⊎-assoc₃ : {A B C : Set} → {x : (A ⊎ B) ⊎ C} → ⊎-assoc₀ (⊎-assoc₁ x) ≡ x
⊎-assoc₃ {A} {B} {C} {A⊎B-⊎C} with A⊎B-⊎C
... | inj₁ (inj₁ a) = refl
... | inj₁ (inj₂ b) = refl
... | inj₂ c        = refl


⊎-assoc : {A B C : Set} → (A ⊎ (B ⊎ C)) ≃ ((A ⊎ B) ⊎ C)
⊎-assoc = record { 
    to = ⊎-assoc₀ ; 
    from = ⊎-assoc₁ ; 
    from∘to = λ a → ⊎-assoc₂ ; 
    to∘from = λ b → ⊎-assoc₃ 
    }

case-to : {A : Set} → (A ⊎ ⊥) → A
case-to A⊎⊥ with A⊎⊥
... | inj₁ a = a
... | inj₂ ()

inj₁∘case-to : {A : Set} {x : A ⊎ ⊥} → inj₁ (case-to x) ≡ x
inj₁∘case-to {A} {A⊎⊥} with A⊎⊥
... | inj₁ a = refl
... | inj₂ ()

case-to∘inj₁ : {A : Set} {a : A} → case-to (inj₁ a) ≡ a
case-to∘inj₁ {A} {a} = refl

⊎-⊥-neut : {A : Set} → (A ⊎ ⊥) ≃ A
⊎-⊥-neut {A} = record {
    to = case-to ; 
    from = inj₁ ; 
    from∘to = λ a → inj₁∘case-to ; 
    to∘from = λ b → case-to∘inj₁ 
    }

-- B.5) Demostrar las siguientes "leyes exponenciales".
--
-- Nota:
-- Si leemos ⊥     como el cero 0,
--           ⊤     como el uno 1,
--           A ⊎ B como la suma A + B,
--           A × B como el producto A ∙ B,
--         y A → B como la potencia B ^ A,
-- las leyes dicen que:
--   A^0       = 1
--   A^1       = A
--   C^(A + B) = C^A ∙ C^B
--   C^(A ∙ B) = (C^B)^A

exp-cero : {A : Set} → (⊥ → A) ≃ ⊤
exp-cero = {!!}

exp-uno : {A : Set} → (⊤ → A) ≃ A
exp-uno = {!!}

exp-suma : {A B C : Set} → ((A ⊎ B) → C) ≃ ((A → C) × (B → C))
exp-suma = {!!}

exp-producto : {A B C : Set} → ((A × B) → C) ≃ (A → B → C)
exp-producto = {!!}

-- B.5) Demostrar la generalización dependiente:

exp-producto-dep : {A : Set} {B : A → Set} {C : (a : A) → B a → Set}
                          → ((p : Σ[ a ∈ A ] B a) → C (proj₁ p) (proj₂ p))
                            ≃
                            ((a : A) (b : B a) → C a b)
exp-producto-dep = {!!}

-- Parte C --

-- En este ejercicio vamos a demostrar que un compilador
-- minimalista es correcto.

-- Una expresión aritmética es una constante o la suma de dos expresiones:

data Expr : Set where
  e-const : ℕ → Expr
  e-add   : Expr → Expr → Expr

-- Definimos una función para evaluar una expresión aritmética:

eval : Expr → ℕ
eval (e-const n)   = n
eval (e-add e₁ e₂) = eval e₁ + eval e₂

-- Definimos una máquina de pila con 2 instrucciones,
-- una para meter un elemento en la pila y otra para
-- sumar los dos elementos del tope de la pila. Si no
-- argumentos suficientes, la instrucción no tiene efecto.

data Instr : Set where
  i-push : ℕ → Instr
  i-add  : Instr

-- Un programa es una lista de instrucciones.
-- Definimos una función para ejecutar un programa
-- sobre una pila de números naturales:

run : List Instr → List ℕ → List ℕ
run []                stack             = stack
run (i-push n ∷ prog) stack             = run prog (n ∷ stack)
run (i-add ∷ prog)    []                = run prog []          -- (No hay argumentos suficientes).
run (i-add ∷ prog)    (n ∷ [])          = run prog (n ∷ [])    -- (No hay argumentos suficientes).
run (i-add ∷ prog)    (m ∷ (n ∷ stack)) = run prog ((n + m) ∷ stack)

-- Definimos el compilador como una función que recibe
-- una expresión aritmética y la convierte en una lista
-- de instrucciones:

compile : Expr → List Instr
compile (e-const n)   = i-push n ∷ []
compile (e-add e₁ e₂) = (compile e₁ ++ compile e₂) ++ (i-add ∷ [])

-- Demostrar que el compilador es correcto:

compile-correct : {e : Expr}
                → run (compile e) [] ≡ eval e ∷ []
compile-correct = {!!}

