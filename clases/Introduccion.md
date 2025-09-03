## Temas
- Juicios y Proposiciones
- Tipos:
	- Bool ($\mathbb{2}$)
	- Nat ($\mathbb{N}$)
	- Producto ($\times$)
- Tipo de las funciones ($\to$)
- Tipo de las funciones **dependientes** ($\Pi$)
- Tipo de Suma
- Tipo de Suma Dependiente ($\Sigma$)
- Ejercicios en Agda
## Juicios y Proposiciones

> Remarca la diferencia entre un juicio y una proposicion. El juicio es una afirmacion de cualquier tipo (i.e: *0 nat, $\Gamma$ ctx, P(x) es verdadero*) y uno ve que es verdadero dandole una justificacion (en forma de arbol del juicio). Una proposicion es una formula (dentro de la LPO). Solemos notar la afirmacion "P(x) es verdadero" como $\vdash P(x)$ 

Una diferencia entre la teoria de conjuntos y la teoria de tipos (o este aproach donde se hace una diferencia entre los juicios y las proposiciones) es que el simbolo $\in$ pertenece a los simbolos de predicado (por lo que podria aparecer multiples veces dentro de una proposicion) mientras que el simbolo $:$ esta definido como parte de los juicios en nuestro sistema. Esto da pie a explicar de que forma son los juicios:
- Juicio de formacion de contexto?: $\Gamma\ \textbf{ctx}$
- Juicio de tipado: $\Gamma \vdash t : \tau$
- Juicio de "igualdad?" $\Gamma \vdash t \equiv q : \tau$ (donde $\tau$ es el tipo de $t$ y $q$)

> Dato de color: a la igualdad definida a la altura de juicio se la llama *judgmental equality* (mas declarativo imo)

## Tipo de las funciones 
En el punto de vista de la teoria de conjuntos se la puede pensar como una funcion que te lleva de un conjunto a otro. En su punto de vista dentro de la logica proposicional, podemos pensarlo como una implicacion.

> En clase armamos todos los juicios correspondientes al tipo funcion. No lo escribimos como una macro que utiliza un tipo $\Pi$ (como yo pense que ibamos a hacer). Esto fue asi porque no se puede agregar las restricciones que nos interesan para hacer esto? Deberiamos poder expresar que el tipo no tiene a la variable (que liga el $\Pi$) libre dentro del tipo que tiene en su "cuerpo". Pareceria que no hay problema con esto, despues lo comento al definir el tipo de las funciones dependientes

## Tipo de las funciones dependientes
No tiene mucho misterio [[Dependent types and dependent functions]]

> Es como el tipo funcion pero donde el codominio puede depender del argumento de esta 

Representa el "para todo"

## Tipo Suma ($\sqcup$) (Either)
> Para demostrar una propiedad de un elemento de (A+B) bastaria ver que podemos demostrar la misma propiedad para (in1 a) y para (in2 b)

Este tipo representa la union disjunta en la teoria de conjuntos (suele notarse como $\sqcup$) y representa el $\lor$ en la logica proposicional.

## Tipo de Suma dependiente
> $\Sigma$ es a $A \times B$ es lo que $\Pi$ es a $A\to B$
> Representa el "existe"

El tipo $\Sigma_{a:A}B$ se puede pensar como el tipo con las tuplas que tienen en su primer elemento un elemento de $A$ y en su segundo elemento le proposicion $B(a)$. Basicamente, el elemento de $A$ junto a la demo de que cumple $B$
## Ejercicios en Agda
Durante la clase definimos:
- Tipo de datos Bool
	- not
- Tipo de datos `List (A : Set)`
	- `length` es asociativo con `++` (asi se dice?)
- Tipo de dato Producto
	- Proyecciones $\pi_1$ $\pi_2$
	- Asociatividad
	- Distributividad
- Tipo de la suma dependiente ($\Sigma$)
	- Demostramos una variante del axioma de eleccion (Actually, esta variante es algo mas debil)
### Notas

> En la teoria que venimos viendo no existe el pattern-matching, lo que si existe es el principio de induccion. Usando este podemos definir el concepto de pattern-matching

- Pablo (no es fan) usa Agda con Emacs por tener un modo de Agda que es lo que recomiendan oficialmente. Aun asi menciono la existencia de una extension para nvim (encontre esto https://github.com/agda/cornelis)
- El universo $\mathcal{U}$ se nota como Set
- El tipo de las funciones A->B se escribe como siempre pero el tipo de las funciones dependientes $\Pi_{a:A}B$ en Agda se nota (a:A)->B
- Al definir postulados, el motor no busca una demostracion. Los acepta directamente
- Al definir terminos (cuando no hay ninguna keyword en especial) Agda intenta chequear que la expresion definida es del tipo que se dice. Aca es cuando entra el papel del demostrador interactivo
- Podemos escribir `?` para decirle a Agda que ahi deberia haber "una cosa". Por ejemplo: en la demostracion de que el 4 es par podemos empezar la demo con `ParS ? ?` y al pedirle que chequee la expresion va a crear dos **agujeros**
- Se puede notar que un argumento esta implicito usando `{}`. Por ejemplo: `{n : Nat} -> ...` . A una funcion definida con parametros implicitos se le pueden pasar usando `f {A}` 
- A diferencia de Haskell es necesario cuantificar las variables de tipo 
	- `length : {A : Set}`
- Si le ponemos llaves a la lambda nos permite hacer pattern-matching
