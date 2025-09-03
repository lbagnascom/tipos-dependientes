# Repaso
- Recordamos el tipo de la igualdad
	- sym
	- trans
- Estructura de $\omega$ grupoide
	- Qué es un Grupo
	- Path con composición es un $\omega$ grupoide
	- Propiedades
	- Teorema
	- Wiskering
- Transporte

### Estructura de $\omega$ grupoide
#### Grupo 
Un grupo es (X, $\cdot$, e, $-^{-1}$), o sea
- Es un conjunto X junto a:
- una operación $\cdot$ asociativa que se mantiene en el grupo,
- un elemento identidad de la operación (e) y
- todo elemento tiene un elemento inverso en la operación ($-^{-1}$)

Nosotros vamos a ver que
> El tipo de los caminos $p:x=_A y$ junto a la operación de composición (\*) forman un grupo (y más...).

### Grupoide
> A groupoid can be seen as a group with a partial function replacing the binary operation.

#### Propiedades
Los 3 requisitos para que sea un Grupo?
1. Si $p: x=_A y$ entonces
	- $refl_x \cdot p =_{(x=_A y)} p$
	- $p \cdot refl_y =_{(x=_A y)} p$
2. Si $p: x=_A y$, $q: y=_A z$  $r: z=_A w$ (3 caminos) entonces
	- $(p \cdot q) \cdot r =_{(x=_A w)} p \cdot (q \cdot r)$
3. Si $p: x=_A y$ entonces
	- $p \cdot p^{-1} =_{(x=_A x)} refl_x$ 
	- $p^{-1}\cdot p =_{(y=_A y)} refl_y$ 

Extras para que sea un grupoide?:
- $(p \cdot q)^{-1} = p^{-1} \cdot q^{-1}$
- $(p^{-1})^{-1} = p$

Para demostrar las props hay que recordar/observar la regla de cómputo de $=_A$.

En particular:
- $refl_x^{-1} = refl_x$
- $refl_x \cdot p = p$

> Nuestra teoría trabaja módulo igualdad definicional.

### Teorema (Eckmann-Hilton)
- Si $A:\mathcal{U}, a : A$
	- $\Omega (A, a) :\equiv (a =_A a)$
	- Lo llamamos loop space al $\Omega$. Es así porque es el espacio de los caminos que se van a sí mismo
- Si a está implícito, lo notamos $\Omega(A)$
- Definimos el loop space de orden 2
	- $\Omega^2(A) :\equiv \Omega(\Omega(A, a), refl_a)$
	- $\Omega^2(A) :\equiv (refl_a =_{a=_A a} refl_a)$
El teorema dice que la transitividad (o composición) es conmutativa (para $\Omega^2$).
- Si tenemos dos caminos p y q (conectados), podemos usar la transitividad para decir que $p \cdot q$  es un camino compuesto. En general no es fácil pensar en cómo valdría que, por lo tanto, podes hacer un camino componiendo $q \cdot p$

#### Teorema
La transitividad para
- $\cdot : \Omega^2(A) \to \Omega^2(A) \to \Omega^2(A)$
es conmutativa (o sea, $a \cdot b = b \cdot a$)

#### Demostración
Para la demo definimos unas operaciones (wiskering) para poder componer caminos de distintas dimensiones (por ejemplo, un camino "simple" compuesto con un camino entre caminos).

> Ver que $\alpha$ es un camino entre los caminos $p$ y $q$. Importante recordar para las próximas definiciones

Si $\alpha : p=_{x=_A y}q$ y $r : y=_{A}z$ entonces definimos
- $\alpha \cdot_R r : p \cdot r =_{x=_A z} q \cdot r$
- $q \cdot_L \beta : q \cdot r =_{x=_A z} q \cdot s$

Definimos el wiskering right por inducción en $r$. Si $r\equiv refl_y$ entonces, 
- $y\equiv z$
- $\alpha \cdot_R refl_y : p = q$ 
- $\alpha \cdot_R refl_y :\equiv \alpha$ 
Y el left se define análogamente

Ahora podemos definir la "composición horizontal"
- $\alpha * \beta :\equiv (\alpha \cdot_R r) \cdot (q \cdot_L \beta)$
Y también otra "composición horizontal" en el otro sentido
- $\alpha *' \beta :\equiv (p \cdot_L \beta) \cdot (\alpha \cdot_R s)$

Para terminar, queremos ver qué pasa en el caso particular de $\Omega^2(A)$ que se da cuando
- $x\equiv y\equiv z\equiv a$
- $p\equiv q\equiv r\equiv s \equiv refl_a$

En ese caso:
- $\alpha * \beta \equiv \alpha \cdot \beta$
- $\alpha *' \beta \equiv \beta \cdot \alpha$
Entonces, para ver que $\alpha \cdot \beta = \beta \cdot \alpha$ vamos a demostrar que
- $\alpha * \beta \equiv \alpha *' \beta$
Esto lo demostramos por inducción en $\alpha, \beta$ 
- $p\equiv q, \alpha \equiv refl_p$
- $r\equiv s, \beta \equiv refl_r$
Reemplazando en $*$ y en $*'$
- $\alpha * \beta \equiv (refl_p \cdot_R r) \cdot (p \cdot_L refl_r)$
- $\alpha *' \beta \equiv (p \cdot_L refl_r) \cdot (refl_p \cdot_R r)$
Ahora haciendo inducción en $p$ y en $r$
- $x\equiv y\equiv z$
- $p\equiv refl_x$
- $r\equiv refl_x$
Y reemplazando de vuelta
- $\alpha * \beta \equiv (refl_{refl_x} \cdot_R refl_x) \cdot (refl_x \cdot_L refl_{refl_x})$
- $\alpha *' \beta \equiv (refl_x \cdot_L refl_{refl_x}) \cdot (refl_{refl_x} \cdot_R refl_x)$
Notar que la parte izquierda es igual ya que
- Por def de $\cdot_R$: $(refl_{refl_x} \cdot_R refl_x) \equiv refl_{refl_x}$
- Por def de $\cdot_L$: $(refl_x \cdot_L refl_{refl_x}) \equiv refl_{refl_x}$

# Transporte
Si tenemos $A : \mathcal{U}$ y $B : A \to \mathcal{U}$  y si $x=_A y$ y $b : B x$
entonces hay un elemento  "correspondiente" a $b$ en $B y$ 
### Propiedad del transporte
$$
\text{transport}\ B\ x\ x\ refl_x \equiv id_{B x}
$$ En el libro de HoTT se nota
Si $p : x=_A y$ entonces $p^* : B x \to B y$
- $p^* :\equiv \text{transport}\ B\ x\ y\ p$
- $(refl_x)^* = id$

