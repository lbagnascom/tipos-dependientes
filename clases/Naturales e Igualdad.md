Hasta ahora vimos:
- $\mathcal{U}$
- $\mathbb{0}, \mathbb{1}, +, \times, \to$
- $\mathbb{2}, \Pi_{x:A}B, \Sigma_{x:A}B$

Notar que $\mathbb{1}$ y $\mathbb{2}$ son logicamente equivalentes, es decir $\mathbb{1} \iff \mathbb{2}$
Pero esto vale para cualquier par de tipos que tengan al menos un habitante, ya que no le presta atencion a las demostraciones. No es *proof relevant*. Esta nocion se refina cuando hablamos de la equivalencia entre tipos.

- Generalizamos la nocion de $\times$ usando $\Pi$
- Generalizamos la nocion de $+$ usando $\Sigma$
- Podemos definir la negacion $\neg$ usando como $\neg A :\equiv A \to \mathbb{0}$

> Ver la similitud entre las reglas de $\Sigma$ y las reglas del $\exists$ en deduccion natural.

### $\Sigma$

- Definimos las reglas de formacion, introduccion, eliminaicon del tipo $\Sigma$
- Definimos los proyectores $\pi_1(t), \pi_2(t)$

### Naturales
- Presento las tipicas reglas de formacion e introduccion de los naturales
- Tambien mostro que existe una version alternativa de construir los naturales dada por la regla $S : \mathbb{N} \to\mathbb{N}$
- Definimos la regla de eliminacion como la de recursion primitiva.
$$
\begin{aligned}
\Sigma \vdash rec_N\ :\ & \Pi_{C:U}\ C \to (N \to C \to C) \to N \to C \\
rec_N\ C\ c_0\ c_s\ 0 &\equiv c_0\\
rec_N\ C\ c_0\ c_s\ (S n) &\equiv c_s n (rec_N C c_0 c_s n) \\
\end{aligned}
$$

Definimos el + con su definicion clasica y dejo como ejercicio: definir \*, pred, $\dot-$ (resta saturada, no pasa por abajo del 0).

En vez de postular el principio de recursion primitiva para la eliminacion podemos definir la recursion iterativa. Esto cumpliria $iter_N C c_0 c_s n = c_s (\dots c_s (c_0))$ con $c_s$ aplicada $n$ veces

Demostro que el principio de iteracion y el de recursion estructural son equivalentes (ejercicio de teorica de plp).

> El principio de recursion primitiva ($rec_N$) se puede definir usando el principio de iteracion ($iter_N$). Simplemente definimos rec en terminos de iter. Si quisieramos demostrar que son realmente iguales habria que demostrar que dan lo mismo siempre. Esto se puede demostrar dentro del sistema

### Funcion de Ackerman
$$ 
\begin{aligned}
\mathcal{A}(0, n) &\equiv S(n) \\
\mathcal{A}(S(m), 0) &\equiv 1 \\
\mathcal{A}(S(m), S(n)) &\equiv \mathcal{A}(m, \mathcal{A}(S(m), n))
\end{aligned}
$$
> Prop: $\mathcal{A}$ es definible en MLTT. (mientras que no lo es en PR clasica)

Demo: 
A(S(m), n) = A(m,  ... A(m, 1)) aplicando A(m, ..) n veces.

Entonces, podemos definir (usando rec + iter o usando iter 2 veces) la funcion de Ackerman.

O sea, las funciones primitivas recursivas dentro de MLTT son mas que las primitivas recursivas clasicas.

#### Teorema (en informal)
No puede existir un lenguaje de programacion que exprese a todas y solo las funciones totales computables.

Demo:
Supongamos que existiera y consideremos el codigo $I$ de un interprete tal que $\Phi_I(<p,x>)$ es el resultado de evaluar un programa $p$ sobre la entrada $x$. 
Sea $p_1,p_2, \dots$ una enumeracion de todos los programas (hacemos diagonalizacion). 
Definimos la funcion: $f : \mathbb{N} \to \mathbb{N}$
$$
f(n) = \Phi_I(<p_n, n>) + 1
$$
Como f es total computable. Sea $p_m$ el programa que la computa.
$$
f(m) = \Phi_I(<p_m, m>)
$$
Absurdo

Como conclusion:
- Cuando haces un lenguaje de programacion o bien computas unicamente las totales computables o bien no. Si vos queres permitir tener funciones parciales, vas a tener que colar funciones no computables (o sea, se cuelgan) como en Haskell.
- Agda no tiene todas las totales computables por un tema de Soundness.

#### Principio de induccion / eliminacion independiente
Es basicamente el principio de induccion que ya conocemos pero usando un $C$ tipo dependiente $C : \mathbb{N} \to \mathcal{U}$.
