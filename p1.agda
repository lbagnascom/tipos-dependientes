{-
Desde el punto de vista logico:
- flip representa una propiedad nomás, no?
- compose representa el combinar dos implicaciones (al estilo transitividad)

Desde el punto de vista computacional:
- flip dice que no importa el orden de los argumentos
- compose permite componer funciones
-}

flip : {A B C : Set} -> (A -> B -> C) -> B -> A -> C
flip f x y = f y x

compose : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
compose f g x = f (g x)

data Bool : Set where
    false : Bool
    true : Bool

recBool : {C : Set} -> C -> C -> Bool -> C
recBool x y true = x
recBool x y false = y

not : Bool -> Bool
not = recBool false true

{-Para computar not true o not false usamos C-c C-n (compute normal form)-}

data _×_ (A B : Set) : Set where
    _,_ : A -> B -> A × B

recProduct : {A B C : Set} -> (A -> B -> C) -> A × B -> C
recProduct f (x , y) = f x y

{-Dentro de un goal, podemos separar por casos usando C-c C-c (nos pide decir sobre qu'e variable queremos) -}
{-Dentro de un goal, podemos decir que lo queremos completar usando C-c C-SPACE -}
{-Si no saco los { ?} del goal podemos decirle que haga refine C-c C-e (refine es mas que esto igual) -}

indProduct : {A B : Set} {C : (A × B) -> Set} -> 
             ((a : A) (b : B) -> (C (a , b))) -> ((x : A × B) -> C x)
indProduct p (x , y) = p x y

proj₁ : {A B : Set} -> A × B -> A
proj₁ = recProduct (λ x _ -> x)

proj₂ : {A B : Set} -> A × B -> B
proj₂ = recProduct (λ _ y -> y)

item₃ : {A B : Set} {C : A × B -> Set} -> 
        ((x : A × B) -> C x) -> ((a : A) (b : B) -> (C (a , b)))
item₃ p a b = p (a , b)
-- curry

item₄ : {A B : Set} {C : A × B -> Set} -> 
        ((a : A) (b : B) -> (C (a , b))) -> ((x : A × B) -> C x)
item₄ = indProduct 
-- uncurry

{-
Los tipos quedan:
item₃ : (A × B -> C) -> (A -> B -> C)
item₄ : (A -> B -> C) -> (A × B -> C)

Son recProduct y el constructor _,_ 
-}

data ⊥ : Set where

⊥-elim : {C : Set} -> ⊥ -> C
⊥-elim ()

falsoImpTodo : {A B : Set} -> (A -> ⊥) -> A -> B
falsoImpTodo aImpBot a = ⊥-elim (aImpBot a)

data ⊤ : Set where
    tt : ⊤

indUnit : {C : ⊤ -> Set} -> C tt -> (x : ⊤) -> C x
indUnit p tt = p

data ∑ (A : Set) (B : A -> Set) : Set where
    _,_ : (a : A) -> B a -> ∑ A B

∑-elim : {A : Set} {B : A -> Set} {C : ∑ A B -> Set} -> 
         ((a : A) -> (b : B a) -> C (a , b)) -> ((x : ∑ A B) -> C x)
∑-elim p (a , x) = p a x

proj₁∑ : {A : Set} {B : A -> Set} -> (x : ∑ A B) -> A
proj₁∑ = ∑-elim (λ a b -> a)

proj₂∑ : {A : Set} {B : A -> Set} -> (x : ∑ A B) -> B (proj₁∑ x)
proj₂∑ = ∑-elim (λ a b -> b)

-- Versión verbose
-- proj₂∑ : {A : Set} {B : A -> Set} -> (x : ∑ A B) -> B (proj₁∑ x)
-- proj₂∑ {A} {B} x = ∑-elim {A} {B} {(λ x -> B (proj₁∑ x))} (λ a b -> b) x

axDebil : {A B : Set} {C : A -> (B -> Set)} ->
    ((a : A) -> (∑ B (C a))) -> 
    (∑ (A -> B) (λ f -> ((a : A) -> C a (f a))))
axDebil = {!   !}