open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

data List (A : Set) : Set where
    [] : List A
    _::_ : A -> List A -> List A

data Maybe (A : Set) : Set where
    None : Maybe A
    Some : A -> Maybe A

-- agregamos el maybe para poder definir el head ya que
-- como las funciones deben ser totales, no podemos definir una que solo esté definida con lista no vacía 
head : {A : Set} -> List A -> Maybe A
head [] = None
head (x :: _) = Some x


--------------------------------------------------------------------------------

data Vec (A : Set) : (n : ℕ) → Set where
    []   : Vec A 0
    _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

vec-head : {A : Set} {n : ℕ} -> Vec A (suc n) → A
vec-head (x :: _) = x

_++_ : {A : Set} {n m : ℕ} -> Vec A n -> Vec A m -> Vec A (n + m)
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)


transport :  {A : Set} (B : A → Set) {x y : A} (p : x ≡ y) → B x → B y
transport _ refl b = b


reverse : {A : Set} {n : ℕ} -> Vec A n -> Vec A n
reverse [] = []
reverse {A} {suc n} (x :: xs) = transport (Vec A) (+-comm n 1) (reverse xs ++ (x :: [])) 

-- Vamos a querer transportar 



-- transport-hell
reverse-++ : {A : Set} {n m : ℕ} {xs : Vec A n} {ys : Vec A m}
    → reverse (xs ++ ys) ≡ transport (Vec A) (+-comm m n) (reverse ys ++ reverse xs)
reverse-++ {A} {n} {m} {xs} {ys} = {!  !}


-- en Agda podemos definir variables generalizables como
-- variable A B : Set
-- variable n m : ℕ


lema : {A : Set} {n n' : ℕ} {x : A} {xs : Vec A n}
    → (p : n ≡ n')
--    → (q : suc n ≡ suc n')
-- Por qué es necesario q?
    →  x :: transport (Vec A) p xs ≡ transport (Vec A) (cong suc p) (x :: xs)
lema refl = refl

-- Lo que antes dijo de hacer REWRITE son lo que Coq tiene como implicit coersions?