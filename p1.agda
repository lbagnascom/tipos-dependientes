

{-
Desde el punto de vista logico:
- flip representa  
- compose representa el combinar dos implicaciones (al estilo transitividad)

Desde el punto de vista computacional:
- flip
- compose

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
recProduct f (x , x₁) = f x x₁

{-Dentro de un goal, podemos separar por casos usando C-c C-c (nos pide decir sobre qu'e variable queremos) -}
{-Dentro de un goal, podemos decir que lo queremos completar usando C-c C-SPACE -}
{-Si no saco los { ?} del goal podemos decirle que haga refine C-c C-e (refine es mas que esto igual) -}

indProduct : {A B : Set} -> {C : A × B -> Set} -> 