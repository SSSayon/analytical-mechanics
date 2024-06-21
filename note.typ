#import "conf/conf.typ": *
#show: conf

#set math.vec(gap: 0.8em)
#set math.mat(gap: 0.6em)

#align(center, text("Notes on Analytical Mechanics", size: 15pt))

#align(center, "Sayon")

#align(center, "2024 spring")

教材: V. I. Arnold, _Mathematical methods of classical mechanics_

1. Newtonian mechanics

2. Lagrangian mechanics
  - variational principle 变分法

3. Hamiltonian mechanics
  - symplectic structure 辛结构

4. Integrable systems

5. Nonintegrability

6. Relativity


#line(length: 100%)

Kepler's 3 laws

1. Each planet moves on an elliptical orbit with the sun at one focus.

2. The area swept by the planet within unit time is a constant. (angular momentum conservation)

3. The ratio of the cube of the semimajor and the square of the period is a constant. ($a^3/T^2$ = const)

\
The principles of relativity and determinacy:

A. space($RR^3$) and time($RR$)

B. Galileo's principle of relativity
#pad(left: 1em)[
There exist coordinate systems (called inertial 惯性的) with the following properties:
- All the laws of nature at all moments of time are the same in all inertial coordinate systems
- All coordinate systems in uniform rectilinear motion w.r.t. an inertial one are themselves inertial 相对于惯性坐标系作匀速直线运动的坐标系是惯性的
]

C. Newton's principle of determinacy
#pad(left: 1em)[
  The initial state of a mechanical system (the totality of positions and velocities of its points of some moment) uniquely determines all its motion.
]


\
_Galileo structure_

1. The universe - a four-dim affine space (仿射空间) $A^4$. The points of $A^4$ are called world points or events. The parallel displacements of $A^4$ constitute a vector space $RR^4$. 

2. Time - a linear map $t: RR^4 -> RR$. If $t(a-b) = 0, a, b in A^4$, we say $a$ and $b$ are simultaneous events.

3. The distance between simultaneous events $a$ and $b$: $quad rho(a,b) = sqrt(angle.l a-b\, a-b angle.r)$

\
The _Galileo group_ is the group of all transformations preserving the Galileo structure. 

The elements of Galileo group are called _Galilean transformations_. \ Thus, Galilean transformations are #underline("affine transformations") of $A^4$ which preserve #underline("intervals of time") and #underline("the distance between simultaneous events"). (保持时间间隔和同时事件距离)

Three types of elements of Galileo group: (在伽利略坐标空间 $(t,arrow(x)) in (RR, RR^3)$ 下)

1. uniform motion: $g_1(t, arrow(x)) = (t, arrow(x)+arrow(v) t)$, $arrow(v) in RR^3$ velocity

2. translation: $g_2(t, arrow(x)) = (t+s, arrow(x) + arrow(s))$, $forall t in RR, arrow(x) in RR^3$

3. rotation: $g_3(t, arrow(x)) = (t, G arrow(x))$, $G: RR^3 -> RR^3$ orthogonal transformation


\
Newton mechanics
$ m dot.double(x) = arrow(F) (x, dot(x), t) $

1. By the time translation, we get that the equation $(dif^2 x(t+s))/(dif (t+s)^2)$ does not depend on $t$ explicitly
2. By the space translation, we get that the equation depends only on relative positions
3. By the rotation, we get $F(G x, G dot(x)) = G dot.c F(x, dot(x))$, $G$ orthogonal transformation of $RR^3$

$ m_1 dot.double(x)_1 = (G m_1 m_2 (x_1 - x_2))/(||x_1 - x_2||^3) $
$ m_2 dot.double(x)_2 = (G m_1 m_2 (x_2 - x_1))/(||x_1 - x_2||^3) $

#pagebreak()
#line(length: 100%)
Chapter 02
#line(length: 100%)
#set math.equation(numbering: "(1)")

*Systems of 1 degree of freedom:* discribe by
$ dot.double(x) = f(x), x in RR $ <1_deg_of_freedom>

Kinetic energy: $T = 1/2 dot(x)^2$

Potential energy: $U(x) = - display(integral_(x_0)^x f(t) dif t)$

Total energy: $E = T + U$

\
*Thm.* For a system evolving according to @1_deg_of_freedom, its total energy is conserved. 

_Proof._ $dot(E) = dot(T) + dot(U) = dot(x) dot.double(x) + (-f(x)) dot(x) = 0$ 

\
Setting $y=dot(x)$, we convert @1_deg_of_freedom into 
$ cases(dot(x) = y, dot(y) = f(x)) $

Phase space (plane): the space $RR^2$ of $x$ and $y$
\ Phase point: a point in the phase plane
\ Phase curve: the image of a solution in the plane space

\
_Example: Harmonic oscillator_ 谐振子
#align(center, $dot.double(x) = -x$)

$display(==> cases(dot(x)=y, dot(y)=-x) quad ==> vec(x, y)' = mat(0,1;-1,0) vec(x, y) )$
#v(0.4em)
$K = 1/2 dot(x)^2 = 1/2 y^2, U = -integral (-x) dif x = 1/2 x^2 ==> E = 1/2(x^2 + y^2)$

#figure(
  image("img/harmonic_oscillator.svg", width: 30%)
)

\
More generally, we consider 
#align(center, $display(E = 1/2 y^2 + U(x))$)

$==> y = plus.minus sqrt(2(E-U(x)))$

_从 $U$ 画相图的方法:_
\ Rules: (1) $y = - sqrt(2(E-U(x)))$ has the same monotonicity as $U$.
     \ #h(29.5pt) (2) In the upper half plane $y>0$, $y =dot(x)$, this means, points move to the right. 
     \ #h(29.5pt) (3) If the $E$-level set ${1/2 y^2 + U(x) = E}$ does not contains any critial point of $E$, then the level set is an entire periodic orbit.
     \ #h(29.5pt) (4) If the $E$-level set contains a critial point $x_t$ of $E$ and if the critial point is nondegenerate, then depending on the sign of $U''(x_t)$, it gives a _saddle_ if $U''(x_t)<0$ and a _center_ if $U''(x_t)>0$.

#figure(
  image("img/phase_curve.svg", width: 40%)
)

如图所示, $E_2$-level set 包含了一个 saddle, $E_4$-level set 包含了两个 center.

#v(0.5em)
$display(cases(dot(x) = y, dot(y) = -U'(x)))$ , suppose $x^*$ is a critical point.

The linearized equation
$display(cases(delta dot(x) = delta y, delta dot(y) = -U''(x^*)) quad i.e. vec(delta dot(x), delta dot(y)) = mat(0,1;-U''(x^*),0) vec(delta x, delta y))$
// 局部极大值, 则两个特征值 加起来等于 0, 乘起来小于 0, 则是两个纯虚数 

\
#line(length: 100%)
*Systems of 2 degree of freedom:*

*N$dot.double(upright(bold(o)))$ther's law:* _symmetry (invariance under a continuous group)_ implies conservation law.

We say s system has _2 degrees of freedom_ if it satisfies the equation
$ dot.double(bold(x)) = bold(f)(bold(x)), bold(x) in RR^2 $


A system is called _conservative_ (保守系统) if there exists a function $U: RR^2 -> RR$ s.t. 
$ bold(F) = -nabla U $

The equation is 
$ dot.double(bold(x)) = -nabla U(bold(x)) $

We define the total energy as $E = 1/2||bold(y)||^2+U(bold(x)), bold(y) = dot(bold(x))$. 

*Thm.* A conservative system has the law of energy conservation. 

\
*Def.* The motion of a point in a _central field_ (中心力场) on a plane is defined by 
$ dot.double(bold(r)) = Phi(r) bold(hat(e)_r) $

*Def.* We define the _angular momentum_ by
$ bold(M) = bold(r) times dot(bold(r)) $

*Thm.* For a point moving in a central field, the angular momentum is conserved.

\
$bold(r) = r bold(hat(e)_r)$

#figure(
  image("img/polar_coordinate.svg", width: 35%)
)

#line()
*Lemma.* $dot(bold(r)) = dot(r) bold(hat(e)_r) + r dot(phi) bold(hat(e))_phi, quad bold(dot.double(r)) = (dot.double(r)-r dot(phi)^2)bold(hat(e)_r) + (2 dot(r) dot(phi)+r dot.double(phi))bold(hat(e))_phi.$

_Proof._ $bold(r) = r bold(hat(e)_r)$, 

$display(dot(bold(r)) = dot(r) bold(hat(e)_r) + r (dif hat(bold(r)))/(dif t) = dot(r) bold(hat(e)_r) + r (dif bold(hat(r)))/(dif phi) dot(phi) = dot(r) bold(hat(e)_r) + r dot(phi) bold(hat(e))_phi)$

$dot.double(bold(r)) = ...$

可以用复数证, $(r e^(i phi))' = dot(r) e^(i phi) + r dot(phi) i e^(i phi), quad (r e^(i phi))'' = (dot.double(r) - r dot(phi)^2)e^(i phi) + (2 dot(r) dot(phi) + r dot.double(phi)) i e^(i phi)$ 即为该引理.
#line()

$bold(M) = bold(r) times bold(dot(r)) &= bold(r) times (dot(r) bold(hat(e)_r) + r dot(phi) bold(hat(e))_phi) \
&= r bold(hat(e)_r) times r dot(phi) bold(hat(e))_phi = r^2 dot(phi) bold(hat(e)_r) times bold(hat(e))_phi = r^2 dot(phi)$

Kepler's second law is exactly the angular momentum conservation.


\
*Thm.* Consider a point moving in a central field with the equation $bold(dot.double(r)) = -nabla U(bold(r)), bold(r) in RR^2$ where $U = U(||bold(r)||) = U(r)$. Then the radius $r$ satisfies a system of 1 degree of freedom with effective potential
$ V(r) = U(r) + M^2/(2r^2) $

_(Reducing a motion in a central field to a system of 1 degree of freedom)_

_Proof._ By the equation of motion, we have $bold(dot.double(r)) = -(partial U)/(partial r)hat(bold(e))_r$.

由引理 $display(==> cases(dot.double(r) - r dot(phi)^2 = -(partial U)/(partial r), 2 dot(r) dot(phi)+r dot.double(phi)=0 &==>dif/(dif t)(r^2 dot(phi))=0))$

According to the angular momentum conservation (上面一行又再次给出了),

$r^2 dot(phi) = M ==> dot(phi) = display(M/r^2)$

$==> display(dot.double(r) = -(partial U)/(partial r) + r (M/r^2)^2 = - partial/(partial r)(U+M^2/(2r^2)) = -partial/(partial r) V)$, where $display(V = U+M^2/(2r^2))$.

注. The total energy in the derived 1-dim problem $display(E_1 = dot(r)^2/2+V(r))$ is _the same_ as the total energy in the original problem $display(E = (||bold(dot(r))||^2)/2 + U(bold(r)))$, since
#align(center, $display((||bold(dot(r))||^2)/2 = (dot(r)^2)/2 + (r^2 dot(phi)^2)/2 = (dot(r)^2)/2 + M^2/(2 r^2))$)

\
#line(length: 100%)

*Kepler problem:* $U = -k/r ==>$

$ V(r) = U(r) + M^2/(2 r^2) = -k/r + M^2/(2 r^2) $

#figure(
  image("img/V-r.svg", width: 35%)
)
\
$display(E = 1/2 dot(r)^2 + V(r) ==> (dif r)/(dif t) = plus.minus sqrt(2 (E-V(r))))$

又由 angular momentum 守恒 $==> display((dif phi)/(dif t) = M/r^2)$

$display(==> (dif phi)/(dif r) = (M\/r^2)/(sqrt(2(E-(-k/r+M^2/(2 r^2))))))$

$display(==> phi &= integral dif phi = integral (M\/r^2)/(sqrt(2(E+k/r-M^2/(2 r^2)))) dif r = dots.c \
&= arccos((M/r-k/M)/(sqrt(2E+k^2/M^2))) = arccos((M^2/(k r)-1)/sqrt(1+(2 E M^2)/k^2)))$

记 $p := M^2/k, quad e := sqrt(1+(2 E M^2)/k^2)$ (eccentricity, 离心率)


$display(==> (p/r-1)/e = cos phi ==> r = p/(1+e cos phi))$

$ r = p/(1+e cos phi) $
- when $0<e<1$ i.e. $E<0$, the orbit is an ellipse
- when $e=1$ i.e. $E=0$, the orbit is a parabola
- when $e>1$ i.e. $E>0$, the orbit is a hyperbola

$a$: semi-major, $b$: semi-minor

$==> 2a = p/(1+e)+p/(1-e) = (2p)/(1-e^2)$

$==> a = p/(1-e^2) = k/(2|E|), b = a sqrt(1-e^2) = M/sqrt(2|E|)$

\
Kepler's third law: $display(a^3/T^2) = "const"$

$pi a b = integral_0^T M/2 dif t = 1/2 M T ==> T = dots.c = 2 pi a^(3/2) k^(-1/2)$.

\
#line(length: 100%)

*Axially symmetric field* 轴对称场

*Def.* A vector field in $RR^3$ is said to be _axially symmetric_ if it is invariant under the group of rotations which fixes every point in the axis.

We choose the $z$-axis to be the axis fixed by the group of rotations.

*Lemma.* If a field is conservative and axially symmetric, then its potential energy $U$ has the form $U(r,z)$, independent of $phi$.

_证明. 见作业_

*Thm.* For a particle moving in a conservative and axially symmetric field, then $ M_z = angle.l hat(bold(e))_z, bold(r) times dot(bold(r)) angle.r $ is conserved (角动量 $bold(M)$ 在 $z$ 方向的分量守恒).

_Proof._ $dot(M_z) = angle.l hat(bold(e))_z, bold(r) times dot.double(bold(r)) angle.r = angle.l hat(bold(e))_z, bold(r) times bold(F) angle.r = 0$

(_由引理, $bold(F) = - nabla U(r,z)$ lies in the plane spanned by $hat(bold(e))_z$ and $bold(r)$._)

#line(length: 100%)
*The two-body problem*

$ m_1 dot.double(bold(r_1)) = - (partial U)/(partial bold(r_1)) \
  m_2 dot.double(bold(r_2)) = - (partial U)/(partial bold(r_2)) $

where $U = U(|bold(r_1)-bold(r_2)|)$.

*Thm.* The time variation of the relative distance $bold(r) = bold(r_1) - bold(r_2)$ in the two body problem is the same as the motion of a point mass $m = (m_1 m_2)/(m_1+m_2)$ in a field with potential $U(|bold(r|))$.

_Proof._ $m_1 m_2 dot.double(bold(r)) = m_1 m_2 bold(dot.double(r)_1) - m_1 m_2 bold(dot.double(r)_2) = -m_2 (partial U)/(partial bold(r_1)) + m_1 (partial U)/(partial bold(r_2)) = -(m_1+m_2) (partial U)/(partial bold(r))$.


#pagebreak()
#line(length: 100%)
*Lagrangian mechanics*

Chapter 03  - Calculus of variations 变分法
#line(length: 100%)

Lagrangian mechanics: variational principle

$quad arrow.t.b quad$ Legendre transformation

Hamiltonian mechanics: symplectic structure

\
Functional 泛函: A function on the space of curves.

$ Phi(gamma) = integral_a^b L(x(t), dot(x)(t), t) dif t $

where $gamma:[a,b] -> RR^n$ is a $C^1$ curve.

Lagrangian $L: underbrace(RR^n times RR^n, "phase space") times RR -> RR$ is a $C^2$ function.

$Phi: E -> RR$ functional, $E$ is the space of $C^1$ curves in $RR^n$ .

\
*Def.* A functional $Phi: E -> RR$ is said to be _differentiable_ at $gamma_0$, if there exist a linear functional $F: E -> RR$ s.t. 
$ Phi(gamma_0+h) -Phi(gamma_0) = F dot.c h + o(h) $ 

F is called the _differential_ of $Phi$ at $gamma_0$.

*Thm.* Assume $L$ is $C^2$, then $Phi(gamma) = display(integral_a^b L(x(t), dot(x)(t), t) dif t)$ is differentiable. Its differential is given by
$ F dot.c h = integral_a^b ((partial L)/(partial x) - dif/(dif t) (partial L)/(partial dot(x)))_(gamma_0) h(t) dif t + lr((partial L)/(partial dot(x)) h mid(|))_a^b $

_Proof._ 用分部积分公式.

$display( Phi(gamma+h)-Phi(gamma)
  &= integral_a^b L(x+h, dot(x)+dot(h),t) dif t - integral_a^b L(x, dot(x),t) dif t \
  &= integral_a^b (cancel(L(x,dot(x),t)) + lr((partial L)/(partial x)mid(|))_gamma h + lr((partial L)/(partial dot(x))mid(|))_gamma dot(h) + o(h) - cancel(L(x, dot(x),t))) dif t \
  &= integral_a^b (lr((partial L)/(partial x)mid(|))_gamma h + lr((partial L)/(partial dot(x))mid(|))_gamma dot(h)) dif t + o(h) \
  &= integral_a^b (lr((partial L)/(partial x)mid(|))_gamma h - lr(dif/(dif t)(partial L)/(partial dot(x))mid(|))_gamma h) dif t + lr(lr((partial L)/(partial dot(x))mid(|))_gamma h mid(|))_a^b + o(h). \
)$

\
*Def.* A curve $gamma$ is called an extremal (极点) of $Phi$ if $F|_gamma dot.c h = 0, forall h in E$.

*Thm.* Let $E_0$ be the space of curves. $gamma:[a,b] -> RR^n, gamma(a) = x_0, gamma(b) = x_1$ with fixed points. Then $gamma$ is an extremal of $Phi$ if and only if
$ (partial L)/(partial x) - dif/(dif t) (partial L)/(partial dot(x)) = 0 "along" gamma $ <E-L>

We call @E-L _the Euler-Lagrange equation_.

_Proof._ Since we consider only curves with fixed endpoints in $E_0$ i.e. $gamma_1=gamma_0+h$ has the same points as $gamma_0$, this implies $h=0$ at $t=a,b$.

Thus the differential of $Phi$ reads

#align(center, $display(F_gamma dot.c h = integral_a^b lr(((partial L)/(partial x) - dif/(dif t) (partial L)/(partial dot(x)))mid(|))_(gamma(t)) h(t) dif t)$)

#line()
*Lemma.* If a continuous function $f:[a,b] -> RR$ satisfies $display(integral_a^b f(t)h(t) dif t = 0)$, $forall h$ continuous with $h(a)=h(b)=0$, then $f(t) equiv 0$. 
#line()

which finishes the proof.

\
*Thm.* A curve is an extremal of $Phi$ iff the Euler-Lagrangian equation is satisfied along $gamma$.

\
_Example. a free mass (不受力的质点静止或匀速直线运动)_

$U=0, quad L = T = 1/2 m (dot(x)_1^2+dot(x)_2^2+dot(x)_3^2)$

$==> 0 = dif/(dif t) (partial L)/(partial x_i) = m dot.double(x)_i ==> x_i = A_i t + B_i$.


\
#line(length: 100%)
*Hamilton's principle of least action:*
$ underbrace(m dot.double(x) = -nabla U(x)\, quad x in RR^3 " Newton eqn", "Mechanical systems") $
*Thm.* Motions of the mechanical system _coincide with_ extremals of the functional 
$ Phi(gamma) = integral_a^b L(gamma(t), dot(gamma)(t), t) dif t $
where $L(x, dot(x)) = 1/2 m dot(x)^2 - U(x). quad$ (Kinetic energy - potential energy)

_证明. 显然_

\
*Def.* Given Lagrangian $L(x, dot(x), t), x in RR^n$, we call 

$x$ the generalized coordinates/positions, 

$dot(x)$ the generalized velocities,

$(partial L)/(partial dot(x)) = p$ the generalized momentum,

$(partial L)/(partial x)$ the generalized forces

#line()
_Example: central field_

#align(center, $dot(bold(r)) = dot(r)bold(hat(e)_r) + r dot(phi) bold(hat(e))_phi$)

Kinetic energy $T = 1/2 m||dot(bold(r))||^2 = 1/2 m (dot(r)^2 + r^2 dot(phi)^2)$

Potential energy $U(r)$

Lagrangian $L(r, phi, dot(r), dot(phi)) = T - U = 1/2 m (dot(r)^2 + r^2 dot(phi)^2) - U(r)$

$attach(==>, t: "E-L" ) display(cases(
m dot.double(r) = m r dot(phi)^2 - (partial U)/(partial r) & ==> m dot.double(r) = M^2/(m r^3) - (partial U)/(partial r), 
dif/(dif t) (m r^2 dot(phi))= 0 & ==> m r^2 dot(phi)=M "angular momentum conservation"))$
#line()

\
*Def.* If the Lagrangian does not depend on a generalized coordinate $x_1$ i.e. $(partial L)/(partial x_1) = 0$, we say $x_1$ is a _cyclic coordinate_.

*Thm.* The existence of a cyclic  generalized coordinate $x_1$ implies the corresponding generalized momentum $(partial L)/(partial dot(x)_1)$ is a conserved quantity.

\
#line(length: 100%)
*Legendre transformation:*

Let $f: RR-> RR$ be a convex function (额外假设 $C^2$, $f''>0$), the _Legendre transformation_ of $f$ is
$ f^*(y) = sup_x (x y - f(x)) $

#figure(
  image("img/legendre.svg", width: 28%)
)

Suppose the $sup$ is attained at $x_0$, we have $lr(dif/(dif x) (x y - f(x))mid(|))_x_0 = 0 ==> y = f'(x_0)$

\
*Prop.* Let $f$ be a convex function, then its Legendre transformation is still convex.

_Proof._ 

#align($display(f^*(lambda y_1 + (1-lambda) y_2 ) &= sup_x ((lambda y_1 + (1-lambda)y_2)x-f(x)) 
\ &= sup_x lr([lambda(y_1 x -f(x))+(1-lambda)(y_2 x -f(x))]) 
\ &<= lambda sup_x (y_1 x -f(x)) +(1-lambda) sup_x (y_2 x- f(x)) 
\ &= lambda f^*(y_1) + (1-lambda) f^*(y_2). 
)$, center)

\
*Prop.* Suppose $f:RR -> RR$ is $C^2$, strictly convex. Suppose the $sup$ in the definition of $f^*(x)$ is attained at $x_0$ satisfying $y_0 = f'(x_0)$. Then we have 
$ x_0 = (f^*)'(y_0), quad f''(x_0) dot.c (f^*)''(y_0) = 1 $

_Proof._ By assumption, we have $f^*(y_0) = x_0 y_0 -f(x_0)$, where $x_0 = (f')^(-1)(y_0)$

$==> (f^*)'(y_0) = (partial f^*)/(partial x_0) (partial x_0)/(partial y_0) + (partial f^*)/(partial y_0) = (partial x_0)/(partial y_0) (y_0-f'(x_0)) + x_0 = x_0$

_注. 说明 $f'$ 与 $(f^*)'$ 互为反函数._
 
\
*Prop.* The Legendre transformation is involutive, i.e. $(f^*)^* = f$.

_Proof._ 若假设 $f in C^2$, 则由上一命题容易证明 (_略_).
#line()
#italic([$display(h(t) = sup_p (p t - sup_x (p x - f(x))))$, 对每个 $t$,\
对每个 $p$, $display(p t - sup_x (p x - f(x)))$ 的几何意义为 $f(x)$ 的斜率为 $p$ 的切线在 $t$ 处的函数值 (如下图), 再结合 $f(x)$ 是凸函数, 故这些切线都在 $f(x)$ 图像下方, 这些点的 $sup$ 正是 $f(t)$.])

#figure(
  image("img/legendre_involutive.svg", width: 80%)
)

#line()


For a convex function multi variables $f: RR^n -> RR$, we define its Legendre transformation
$ f^*(y) = sup_x (angle.l x, y angle.r - f(x)) $

\
#line(length: 100%)
*Hamiltonian mechanics:*

Given a Lagrangian $L(x, dot(x)): RR^n times RR^n -> RR$, suppose $L$ is (strictly) convex in $dot(x)$. Let the _Hamiltonian_
$ H(x, y) = sup_(dot(x)) (angle.l y, dot(x) angle.r - L(x, dot(x))) $
be the Legendre transformation of $L$ w.r.t $dot(x)$. 

By the involutivity, we have 
#align(center, $L(x, dot(x)) = display(sup_y) (angle.l dot(x),y angle.r - H(x, y))$)

When the $sup$ is attained, we have 
$ cases(y &= (partial L)/(partial dot(x)) &quad "generalized momentum"\
dot(x) &= (partial H)/(partial y)) $

#align(
$display(attach(==>, t: "E-L") cases(
  dot(y) = dif/(dif t) (partial L)/(partial dot(x)) = (partial L)/(partial x) = - (partial H)/(partial x) &quad("why?"),
  dot(x) = (partial H)/(partial y)   
))$, center)

We get _the Hamiltonian canonical equations_
$ cases(dot(x) = (partial H)/(partial y), dot(y) = -(partial H)/(partial x)) $

\
#line()
_Example._ $L(x, dot(x)) = 1/2 m angle.l A dot(x), dot(x) angle.r - U(x)$

$y = (partial L)/(partial dot(x)) = m A dot(x) ==> dot(x) = 1/m A^(-1) y$

$H(x,y) = angle.l y, dot(x) angle.r-L(x, dot(x)) = ... = underbrace(1/(2 m) angle.l y\, A^(-1) y angle.r, "Kinetic energy") + underbrace(U(x), "Potential energy")$
#line()
( Lagrangian: 动能 $-$ 势能 $==>$ 有变分法 \
Hamiltonian: 动能 $+$ 势能 $==>$ 有辛结构 )

\
*Thm.* For mechanical systems (where kinetic energy $K= 1/2 m angle.l A dot(x), dot(x) angle.r$ is a quadratic form w.r.t. $dot(x)$ ), the Hamiltonian is the total energy.

*Thm.* (energy conservation) If $H$ does not depend on $t$ explicitly, then along any orbit $(x(t), y(t))$, we have $H(x(t),y(t)) equiv$ const.

_Proof._ $dif/(dif t) H(x(t),y(t)) = (partial H)/(partial x) dot(x) + (partial H)/(partial y) dot(y) = (partial H)/(partial x) (partial H)/(partial y) + (partial H)/(partial y) (-(partial H)/(partial x)) = 0$.

\
#line(length: 100%)
*Cyclic coordinates:*

*Def.* If a generalized coordinate $x_1$ does not enter $H$ i.e. $(partial H)/(partial x_1) = 0$, we call $x_1$ a _cyclic coordinate_. \ ( We also have $(partial L)/(partial x_1) = 0$ ) 

*Prop.* Suppose $x_1$ is a cyclic coordinate of $H$. Then the corresponding $y_1$ is a conserved quantity.

_Proof._ $dot(y)_1 = -(partial H)/(partial x_1) = 0$

#italic([于是每一个 cyclic coordinate 都能将 $n$ 个坐标减少到 $n-1$ 个 ( $2n$ 个一阶方程 $==> 2(n-1)$ 个 ), 最后由 $dot(x)_1 = (partial H)/(partial y_1) (y_1, tilde(x), tilde(y),t)$ 积分出 $x_1$ 即可.])

\
#line(length: 100%)
*Liouville theorem*

*Thm.* The Hamiltonian flow _preserves volume_ of the phase space. 
#line()
phase space: $RR^n times RR^n$ \
phase flow: the one-parameter group of transformations of the phase space
$ g^t: RR^n times RR^n &-> RR^n times RR^n \
(x(0), y(0)) &|-> (x(t),y(t)) $
where $(x(t), y(t))$ solves the Hamiltonian equation.

For any given $t_0$, $g^(t_0)$ is a diffeomorphism (微分同胚) on $RR^n times RR^n$

#figure(
  image("img/liouville.svg", width: 30%)
)

$"Vol"(D) = "Vol"(g^t (D))$
#line()


_Proof of Liouville theorem._ Let $D(t) := g^t (D(0))$, $v(t) := "Vol"(D(t))$.

Suppose we are given a system of $dot(x) = f(x)$. Then $g^t (x) = x + f(x) t + O(t^2) quad (t -> 0)$

$v(t) = integral_D(t) dif x = integral_D(0) det (partial g^t)/(partial x) dif x = integral_D(0) det(I + (partial f)/(partial x) t + O(t^2)) dif x quad (t -> 0)$

#line()
*Lemma1.* For any matrix $A$, we have 
#align(center, [$det(I+t A) = 1 + t tr(A) + O(t^2) quad (t -> 0)$])
#line()

$==> v(t) = integral_D(0) (1 + t tr((partial f)/(partial x)) + O(t^2)) dif x = integral_D(0) (1 + t nabla dot.c f + O(t^2)) dif x$

$==> display(lr((dif v)/(dif t)mid(|))_(t=0) = integral_D(0) nabla dot.c f dif x)$

#line()
*Lemma2.* If $nabla dot.c f equiv 0$ (divergence free), then $g^t$ preserves volume.

_Proof._ Since $t=t_0$ is no worse than $t=0$, we have
#align(center, $display(lr((dif v)/(dif t)mid(|))_(t=t_0) = integral_D(t_0) nabla dot.c f dif x)$)

$==> (dif v)/(dif t) equiv 0 ==> v(t) equiv$ const.
#line()

For our Hamiltonian flow, we have $display(cases(dot(x) = (partial H)/(partial y), dot(y) = -(partial H)/(partial x)))$

$==> nabla dot.c f = nabla dot.c (dot(x), dot(y)) = nabla dot.c ((partial H)/(partial y), -(partial H)/(partial x)) = sum (partial)/(partial x_i)(partial H)/(partial y_i)-(partial)/(partial y_i)(partial H)/(partial x_i) = 0$,

which finishes the proof.

\
#line(length: 100%)
*Thm.* (Poincar$acute(upright(e))$ recurrence, _加强版本_) Let $f: X -> X$ be a diffeomorphism #underline("preserving the volume") where $X$ is a domain with $"Vol"(X)<oo$. Then for any $A subset X$ with $"Vol"(A)>0$, we have a.e. $x in A$, $exists {n_k}_(k=0)^oo$ s.t. $f^(n_k) (x) in A$.

_Proof._ We first prove that there is one point $x in A$ and $n in NN$ s.t. $f^n (x) in A$.

Consider $A, f(A), f^2 (A), ...$, since $f$ preserves volume, we have $"Vol"(A) = "Vol"(f(A)) = ...$

Since $"Vol"(A)>0$, let $N = floor(("Vol"(X))/("Vol"(A))) + 1$, $exists n_1<n_2 in NN$ s.t. $f^(n_1) (A) sect f^(n_2) (A) eq.not emptyset$

$==> A sect f^(n_2-n_1) (A) eq.not emptyset$ (_这一步需要单射_).

_修改以上证明 (考虑 $A, f^(-1) (A), ...$) , 就不需要单射条件了._

余下证明见作业.

\
#line(length: 100%)
*holonomic constraints*

_Example._ $L_N: RR^2 times RR^2 -> RR$

$T = 1/2 (dot(q)_1^2+dot(q)_2^2), quad U_N = 1/2 N dot(q)_2^2 + U_0(q_1, q_2)$

$L_N = T - U_N$

$H_N = 1/2 (dot(q)_1^2+dot(q)_2^2) + U_N (bold(q)) = E "(total energy)  fixed as" N -> oo$

$==> q_2 -> 0$ as $N -> oo$ ( 不然 $1/2 N dot(q)_2^2$ 项趋于无穷 )

Consider initial condition $(*)$:

#align(center, $q_1(0) &= q_1^0, quad &dot(q)_1(0) &= dot(q)_1^0, \ q_2(0) &= 0, quad &dot(q)_2 (0) &= 0$)

*Thm.* Let $q_1 = phi_N (t)$ be the evolution of $q_1$ under the initial condition $(*)$, then the limit 
#align(center, $display(lim_(N->oo) phi_N (t)-> psi(t))$) 
exists, where $q_1 = psi(t)$ satisfies the E-L equation
$ (partial L_*)/(partial q_1) = dif/(dif t) (partial L_*)/(partial dot(q)_1), $
where 
$ L_*(q_1, dot(q)_1) = T mid(|)_(q_2=dot(q)_2=0) - U_0 mid(|)_(q_2=0) $
_即: 被很大的势场限制住的运动, 其 Lagrangian 相当于不考虑这个势场的势能以及限制曲面法向的动能._


\
*Def.* (holonomic constraints) Let $Gamma$ be an $m$-dim surface in $RR^(3n)$ of points $bold(r_1), ..., bold(r_n) in RR^3$ with masses $m_1, ..., m_n$ respectively. Let $bold(q) = (q_1, ..., q_m)$ be coordinates on $Gamma$, $bold(r_i) = bold(r_i) (bold(q))$. The system discribed by
$ dif/(dif t) (partial L)/(partial dot(bold(q))) = (partial L)/(partial bold(q)), quad L = 1/2 sum m_i bold(r)_i^2 - U(bold(q)) $
is called _a system of $n$ points with $3n-m$ ideal holonomic coordinates_.

_Example._ $bold(r)_i in SS^2 subset RR^3, quad q = (theta, phi)$ is the spherical coordinates, \
$bold(r)_i = (cos theta_i cos phi_i, cos theta_i sin phi_i, sin theta_i)$

\
#line(length: 100%)
*Differentiable manifold*

*Def.* A set $M$ is called a _manifold_ if $M$ is given a finite or countable collection of charts such that each point lies in at least one chart. 

chart (坐标卡): $(U, phi)$, where $U subset RR^n$ is an open set, $phi$ is an one-to-one map from $U$ to some subset of $M$. 

In the overlaping region of two charts, $phi_j^(-1) circle.tiny phi_i [phi_i^(-1) (V_i sect V_j)] subset U_j$

$==> phi_j^(-1) circle.tiny phi_i$ is a map from an open subset of $RR^n$ to another open subset of $RR^n$.

We say $M$ is a _differentiable manifold_ if $phi_j^(-1) circle.tiny phi_i$ is differentiable for all $i,j$

\
#line()
注. *Projective space*
$ RR PP^n  = {"all lines going through" O "in" RR^(n+1)} $
_作业题._ $S O(3)$ homeomorphic to $RR PP^3$.
#line()

\
*Tangent space*

We say two curves $phi(t), psi(t)$ are equivalent at $x$ if $phi(0) =psi(0) =x$ and $display(lim_(t->0) (phi(t)-psi(t))/t = 0)$ in some chart.

*Def.* A tangent vector to a manifold $M$ at $x$ is an equivalent class of curves $phi(t)$ with $phi(0)=x$.

tangent space (切空间) $T_x M$: the set of tangent vectors to $M$ at $x$.

tangent bundle (切丛) $T M = display(union.big_(x in M) T_x M)$

\
*Riemannian manifold*: a manifold endowed with a Riemannian metric (_各点 metric 要是同一个_).

A _Riemannian metric_ on a manifold $M$ is given by a positive definite quadratic form on $T_x M$ at each point $x in M$:
$ T_x M &times T_x M &&-> RR \ (u &, v) &&|-> angle.l u,v angle.r_x = angle.l A_x u, v angle.r $

$||v||_x = sqrt(angle.l u\,v angle.r_x), quad v in T_x M$

For a curve $gamma: [0, 1] -> M$, its length is given by $display(ell(gamma)=integral_0^1 sqrt(angle.l dot(gamma)(t)\, dot(gamma)(t) angle.r_gamma(t)) dif t)$

*Derivative map*:

Let $f: M -> N$ be a map between two manifolds. The derivative of $f$ at point $x in M$ is the linear map of the tangent spaces
$ D f_x = f_(*x): T_x M -> T_(f(x)) N, $
which is given in the following way: 

$forall v in T_x M$, consider a curve $phi: RR->M$ with $phi(0)=x,dot(phi)(0)=v$, then $ display(f_(*x) (v) = lr(dif/(dif t)f(phi(t))mid(|))_(t=0))$.

_注. $f_(*x)(v)$ 的值与 $phi$ 的选取无关._

_注. $f_(*x)$ 是线性的._

\
#line(length: 100%)
*How to solve a system with holonomic constraints:*

1. Find $Gamma subset RR^(3n)$, $bold(r)_1, ..., bold(r)_n in RR^3$, $bold(r)_i = bold(r)_i (bold(q))in Gamma$, $bold(q) = (q_1, ..., q_m) in RR^m$

2. Kinetic energy
#align(center, $display(T = 1/2 sum m_i bold(dot(r))_i^2 = 1/2 sum m_i lr(|(D bold(r)_i)/(D bold(q)) dot.c bold(dot(q))|)^2 = 1/2 sum a_(i j) (bold(q)) dot(q)_i dot(q)_j)$)

3. Solve E-L equation $L = T - U(bold(q))$

\
_Example._ motion of a particle of mass $1$ on a surface of revolution in $RR^3$

Introduce polar coordinates $(r, phi)$ on $RR^2$

$Gamma$ is given by $(r(z), phi, z), z in [a, b], phi in [0, 2 pi]$.

$x &= r(z) cos phi &==> dot(x) &= r_z dot(z) cos phi &- r sin phi space dot(phi) \
y &= r(z) sin phi &==> dot(y) &= r_z dot(z) sin phi &+ r cos phi space dot(phi)$

$==> T = 1/2 (dot(x)^2 + dot(y)^2 + dot(z)^2) = ... = 1/2 ((1 + r_z^2) dot(z)^2 + r^2(z) dot(phi)^2)$

$L (= T) = L(phi,z,dot(phi),dot(z)): T Gamma -> RR$ does not depend on $phi$ explicitly ( $phi$ is a cyclic coordinate)

$==> dif/(dif t) (partial L)/(partial dot(phi)) = (partial L)/(partial phi) = 0 ==> (partial L)/(partial dot(phi)) = r^2 dot(phi) = "const"$

Let $alpha$ be the angle formed by $bold(v)$ with $z$-axis, then the horizontal component of the velocity is \ $r dot(phi) = |bold(v)| sin alpha$ (_看下图理解_)

#figure(
  grid(
    columns: (1fr, 1fr),
    align: bottom,
    image("img/clairaut-1.png", width: 75%),
    image("img/clairaut-2.png", width: 100%)
  )
)

By energy conservation, $|bold(v)|$ is a constant $==> underbrace(r sin alpha= r^2 dot(phi) |bold(v)|^(-1) = "const", "Clairaut's theorem")$

\
_Example._ bead on a rotating circle

a bead with mass $1$ moves along a vertical circle of radius $1$ which rotates with angular velocity $omega$.

$Gamma: bold(r) = (sin(theta) cos(omega t), sin(theta) sin(omega t), cos(theta))$ ( $theta in [-pi, pi]$ measured from the highest point )

$T = 1/2 |dot(bold(r))|^2 = 1/2 (omega^2 sin^2 theta + dot(theta)^2), quad U = g cos theta$

$==> L = T - U = underbrace(1/2 dot(theta)^2) + underbrace(1/2 omega^2 sin^2 theta - g cos theta)$

与一个 $1$-dim system 相同: $T' = 1/2 dot(q)^2, U' = A cos q - B sin^2 q$, where $A = g, B=  1/2 omega^2$

- 当 $2B < A$ 即 $omega^2 r < g$ 时 ($r=1$), $q = plus.minus pi$ (最低点) 是一个稳定点. (此时大圈转的很慢, 符合生活常识.)

- 当 $2B > A$ 时, $q = plus.minus pi$ 将不再是稳定点, 但在 $(-pi, pi)$ 中新出现了两个稳定点, 分别对应 $cos q = - A/(2B) = - g/(omega^2 r)$, 如下图所示.

#figure(
  image("/img/bead_on_circle.png", width: 65%)
)

\
#line(length: 100%)
*N$dot.double(upright(bold(o)))$ther's law*

_以下考虑的是$underbrace("自治系统", L(q,dot(q)) : T M -> RR)$. $underbrace("非自治系统", L(q,dot(q),t) : T M times RR-> RR)$也存在类似定理, 见作业._

$M$ manifold, $L: T M -> RR$ a smooth function, $h: M -> M$ a smooth map

*Def.* A Lagrangian system $L: T M -> RR$ _admits_ the map $h$ if for any $v in T_x M$ we have 
$ L(x, v) = L(h(x), D h(x) v) $

*Thm.*(N$dot.double(upright(o))$ther) If the system $L: T M -> RR$ admits the $1$-parameter group of diffeomorphism \ $h^s: M -> M, s in RR$, then the Lagrangian system _admits a first integral_ $I: T M -> RR$
$ I(q, dot(q)) = lr((partial L)/(partial dot(q)) (dif h^s (q))/(dif s) mid(|))_(s=0) $

_注. $I$ 的表达式中两部分应该是行向量乘列向量，得到个数量 (或写成向量点积)._

_Proof._ Let $phi(t)$ be a solution to the E-L equation, $Phi(t,s):=h^s (phi(t))$

By assumption, $L(Phi(t,s), dif/(dif t) Phi(t,s)) = L(phi(t), dot(phi)(t))$

Take $dif/(dif s)$ on both sides, $0 = (partial L)/(partial q) (dif Phi)/(dif s) + (partial L)/(partial dot(q)) dif/(dif s) dif/(dif t) Phi$

By the E-L equation $dif/(dif t) (partial L)/(partial dot(q)) (Phi(t,s), dif/(dif t) Phi(t,s)) = (partial L)/(partial q) (Phi(t,s), dif/(dif t) Phi(t,s))$

$==> 0 = dif/(dif t) (partial L)/(partial dot(q)) (dif Phi)/(dif s) + (partial L)/(partial dot(q)) dif/(dif t) dif/(dif s) Phi = dif/(dif t) ((partial L)/(partial dot(q)) (dif Phi)/(dif s)) $

$==> display((partial L)/(partial dot(q)) (dif h^s)/(dif s))$ is a conserved quantity.

(_抄自教材, 其实没懂_) In fact, the first integral $I = (partial L)/(partial dot(q))q'$ is _the rate of change of $L(v)$_ when the vector $v in T_x M$ varies inside $T_x M$ with velocity $(dif h^s (x))/(dif s)|_(s=0)$

\
_Example._ points with masses $m_i$, $L = 1/2 sum m_i bold(dot(x))_i^2 - U(bold(x))$

1. Suppose the system admits the translation along $bold(e)_1$: $h^s (bold(x)_i) = bold(x)_i + bold(e)_1 s$

#h(12.5pt) By Nother's thm, $I = sum (partial L)/(partial dot(bold(x))_i) (dif h^s)/(dif s) = sum m_i angle.l dot(bold(x))_i, bold(e)_1 angle.r = underbrace(sum m_i dot(x)_(i 1), "动量" bold(e)_1"分量") quad$ is conserved

#h(12.5pt) i.e. translation invariance $==>$ momentum conservation

2. Suppose $L$ admits rotations around $bold(e)_1$ 

#h(12.5pt) Let $h^s$ be the rotation around $bold(e)_1$-axis by angle $s$, then $(dif h^s)/(dif s) (bold(x)_i) = bold(e)_1 times bold(x)_i$ (_思考_)

#h(12.5pt) $==> I = sum (partial L)/(partial dot(bold(x))_i) (dif h^s)/(dif s) (bold(x)_i) = sum m_i angle.l bold(dot(x))_i, bold(e)_1 times bold(x)_i angle.r = underbrace(sum m_i angle.l bold(x)_i times bold(dot(x))_i\, bold(e)_1 angle.r, "角动量在" bold(e)_1 "的投影") space$ conserved

#h(12.5pt) i.e. rotation invariance $==>$ angular momentum conservation

#pagebreak()

#line(length: 100%)
Chapter 05 Oscillations
#line(length: 100%)

*Linearization* 
$ (dif bold(x))/(dif t)  = bold(f) (bold(x)), bold(x) in RR^n $

A point $bold(x)_0$ is called an equilibrium (平衡点) or fixed point if $bold(x)(t) equiv bold(x)_0$ is a solution. In other words, $bold(f) (bold(x)_0) =0$.

Consider $L = T - U(bold(q)), quad T = 1/2 sum a_(i j) (bold(q)) dot(q)_i dot(q)_j$

The point $bold(q)_0, dot(bold(q))_0$ is an equilibrium iff $dot(bold(q))_0 = 0$ and $bold(q)_0$ is a critical point of $U$ i.e. $lr((partial U)/(partial bold(q)) mid(|))_(bold(q)_0) = 0$

#figure(
  image("/img/oscil-linear-tmp.jpg")
)

#figure(
  image("/img/handwritten/handwritten_1.jpg")
)
#figure(
  image("/img/handwritten/handwritten_2.jpg")
)
#figure(
  image("/img/handwritten/handwritten_3.jpg")
)
#figure(
  image("/img/handwritten/handwritten_4.jpg")
)

#pagebreak()

#line(length: 100%)
Chapter 07 Differential forms
#line(length: 100%)

*Forms on $RR^n$*

- $1$-form: linear functional on $RR^n$

#h(1em) The space of 1-forms is denoted by $(RR^n)^* tilde.equiv RR^n$

- $2$-form: $omega^2: RR^n times RR^n -> RR$ bilinear, anti-symmetric

#h(1em) $omega^2: (u,v) = angle.l A u , v angle.r, quad A$ anti-symmetric

- $k$-form: k-linear, skew-symmetric

#line()

*Exterior product*

1. The exterior product of 2 $1$-forms $omega_1, omega_2 in Lambda^1 RR^n$:
$ (omega_1 and omega_2) (xi_1, xi_2) = mat(delim: "|", omega_1(xi_1), omega_1(xi_2); omega_2(xi_1), omega_2(xi_2)) $

2. The exterior product of k $1$-forms $omega_1, ..., omega_k in Lambda^1 RR^n$

$ (omega_1 and ... and omega_k)(xi_1, ..., xi_k) = mat(delim: "|", omega_1(xi_1), ..., omega_1(xi_k); dots.v, dots.down, dots.v; omega_k (xi_1), ..., omega_k (xi_k)) = det(omega_i (xi_j)) $

Next, given $k$-form $omega^k$ and $l$-form $omega^l$, we define their exterior product

$ (omega^k and omega^l)(xi_1, ..., xi_(k+l)) = display(sum_("all permutations")) (-1)^nu omega^k (xi_(i_1), ..., xi_(i_k)) omega^l (xi_(i_(k+1)), ..., xi_(i_(k+l))) $

properties of exterior product
- skew-symmetry: $omega^k and omega^l = (-1)^(k l) space omega^l and omega^k$
- distributivity
- associativity

We shall prove the equivalence of the definition of $omega^k and omega^l$ and the exterior product of $1$-forms. (omitted)

Remark. $omega^1 and omega^1 = 0$, but $omega^2 and omega^2$ is in general not. Actually, $omega^(2k+1) and omega^(2k+1)=0$.

#line()

*pull-back* 拉回 (behavior under mappings)

Let $f: RR^n -> RR^m$ be a linear map, $omega^k$ be a $k$-form on $RR^m$. Then
$ (f^* omega^k) (xi_1, ..., xi_k) := omega^k (f(xi_1), ..., f(xi_k)) $
is a $k$-form on $RR^n$

#line()

*Differential forms*

We generalize the notion of forms from $RR^n$ to a manifold $M$

Let $f: M -> RR$ be a differentiable function, recall the differential $dif f(x)$ is a linear functional $T_x M -> RR$ given by:

#h(1em) Given $xi in T_x M$, let a smooth curve $gamma: (-epsilon, epsilon) -> M$ s.t. $gamma(0)=x, gamma'(0) = xi$, then 
#align(center, $dif_x f(xi) = lr(dif/(dif t) mid(|))_(t=0) f(gamma(t)) = angle.l dif_x f, gamma'(0) angle.r = angle.l dif_x f, xi angle.r$)

*Def.* A differential $1$-form on $M$ is a smooth map $omega: T M -> RR$ linear on each $T_x M$.

*Thm.* Give $RR^n$ coordinates $x_1, ..., x_n$. Then _every_ differential $1$-form $omega: T RR^n -> RR$ can be written as 
$ omega = a_1(x_1, ..., x_n) dif x_1 + ... + a_n (x_1, ..., x_n) dif x_n, $ 
where $dif x_i (xi) = xi_i, space xi=(xi_1,...,xi_n) in RR^n$, and $a_i (x)$ are smooth functions.

*Def.* A differential $k$-form $omega^k|_x$ at a point $x in M$ is a $k$-form on the tangent space $T_x M$, i.e. a $k$-linear, skew-symmetric function of $k$ vectors $xi_1,...,xi_k in T_x M$.

*Thm.* Give $RR^n$ coordinates $x_1, ..., x_n$. Then _every_ differential $k$-form $omega^k$ on $T RR^n$ has the form 
$ omega^k = sum_(i_1<...<i_k) a_(i_1,...,i_k) (x_1, ..., x_n) dif x_(i_1) and ... and dif x_(i_k) $

#line(length: 100%)

*Integration of differential forms*

We shall prove a general Stokes formula
$ integral_(partial Omega) omega = integral_Omega dif omega $
or written as $angle.l omega, partial Omega angle.r = angle.l dif omega, Omega angle.r$, i.e. $partial$ and $dif$ are dual.

#line()

1. The integration of a differential $1$-form along a curve

#h(14pt) Let $gamma: [0, 1] -> M$ be a smooth curve and $omega^1$ a $1$-form. We define 
$ integral_gamma omega^1 = lim_(Delta->0) sum_i omega^1 (xi_i) $
#h(14pt) There, we partition $[0,1]$ into intervals $Delta_i=[t_i,t_(i+1)]$, $xi_i = dif gamma|_(t_i)(Delta_i) in T_gamma(t_i) M$, 这里把 $Delta_i$ 看成向量. 见下图.

#figure(
  grid(
    columns: (1fr, 1fr),
    align: bottom,
    image("img/integral_of_form-1.png", width: 75%),
    image("img/integral_of_form-2.png", width: 75%)
  )
)

2. The integration of a differential $k$-form along a $k$-dim surface

#h(14pt) 定义与 $1$-form 类似, 将曲面划分为小块, 每块用平行多面体代替. 见上图.

3. (_special case_) The integration of a differential $k$-form on oriented $RR^k$

#h(14pt) Let $x_1,...,x_k$ be a oriented coordinate system of $RR^k$. \
#h(13pt) Then every $k$-form has the form $omega^k = a(x_1, ..., x_k) dif x_1 and ... and dif x_k$ \
#h(14pt) Let $D$ be a bounded convex polyhedron in $RR^k$. We define
$ integral_D omega^k = integral_D a(x_1,...,x_k) dif x_1 ... dif x_k $
#h(14pt) 其中右式理解为通常的 Riemann 积分.

#h(14pt) 注. 这一定义与上面的一般定义相容, 因为此时 $D$ 的 tangent space 仍是 $D$ 本身.

#line()

上面只能定义 $k$-form 在 $k$-dim 曲面上的积分. 为定义一般的 $k$-form on $n$-dim space 的积分, 自然地, 通过_拉回_来定义.

*The behavior of differential forms under mappings*

Let $f: M -> N$ be a differentiable map between manifolds. Let $omega$ be a differential $k$-form on $N$. Then there is a well-defined differential $k$-form on $M$:

$ (f^* omega) (xi_1, ..., xi_k) := omega (f_*(xi_1), ..., f_*(xi_k)), quad forall xi_1,...,xi_k in T_x M $

其中 $f_*$ 是 $f$ 的微分.

*Integration of a $k$-form on $n$-dim manifolds*

*Def.* A $k$-dim _cell_ $sigma$ on $M$ is a triple $sigma = (D, f, O r)$, where
- $D$: a convex polyhedron in $RR^k$
- $f: D -> M$ a differentiable map
- $O r$: an orientation on $RR^k$

*Def.* The integration of a $k$-form $omega^k$ on a cell $sigma$ is defined as
$ integral_sigma omega^k = integral_D f^* omega^k $

*Def.* A _chain_ (链) of dim $k$ on a manifold $M$ consists of a finite collection of $k$-dim cells $sigma_1,...,sigma_r$ and integers $m_1,...,m_r$ called _multiplicities_. Denote it by $C_k = m_1 sigma_1 + ... + m_r sigma_r$.
$ integral_C_k = sum m_i integral_sigma_i omega $

*Def.* Let $sigma = (D, f, O r)$ be a cell of dim $k$, we define its _boundary_ $partial sigma$ to be a collection of cells of dim $k-1$,
$ partial sigma = sum sigma_i, quad sigma_i = (D_i, f_i, O r_i), $
where $D_i$ are faces of $D$, $f_i = f|_D_i$.

Let $e_1,...,e_k$ be a basis of $RR^k$. At each point of $D_i$, we choose an outer normal (外法向). An orientation on $D_i$ is a choice of basis $f_1,...,f_(k-1)$, we require $(n, f_1,...,f_(k-1))$ to have the same orientation as $(e_1,...,e_k)$.

#line(length: 100%)

*Exterior differentiation*

To see the divergence we assume the domain $Omega$ is very small.

Suppose $Omega$ is the parallelepiped (平行六面体) spanned by $epsilon xi_1, epsilon xi_2, epsilon xi_3$

The _divergence_ is obtained as the limit
$ lim (integral_(partial Omega_epsilon) omega^2)/(epsilon^3 V), quad V = det(xi_1,xi_2,xi_3) $

*Def. (exterior derivative)* (_omitted, see page 189 _)

*Thm.* Let $omega^k$ be a $k$-form, then there exists a unique $(k+1)$-form $Omega$ on $T M$, given as 
$ F(epsilon xi_1,...,epsilon xi_(k+1)) = epsilon^(k+1) Omega(xi_1,...,xi_(k+1)) + o(epsilon^(k+1)) quad (epsilon -> 0) $
where $F=integral_sigma omega^k$, $sigma$ be the boundary of the parallelepiped spanned by $(epsilon xi_1,...,epsilon xi_(k+1))$.

Moreover, if $omega^k = sum a_(i_1,...,i_k) dif x_i_1 and ... and dif x_i_k$, then $ Omega = dif omega^k = sum dif a_(i_1,...,i_k) and  dif x_i_1 and ... and dif x_i_k $

_注. 这基本给出了 stokes 公式._

_Example._ $omega^2 = A dif y and dif z + B dif z and dif x + C dif x and dif y$, then $Omega = dif omega^2 = "div"(A,B,C) dif x and dif y and dif z$.

_Proof._ 只证最简单的 $1$-form $omega^1 = a(x_1,x_2) dif x_1$.

Given $xi,eta$ (small enough) shown as below, we calculate $F(xi,eta) = integral_sigma omega^1$, where $sigma$ is the boundary of the parallelogram spanned by $eta,xi$.

#figure(
  image("img/stokes.png", width: 35%)
)

$display(
integral_sigma omega^1 
&= integral_0^1 (a(xi t) - a(xi t + eta))xi_1 - (a(eta t) - a(eta t + xi))eta_1 dif t & (xi_i = dif x_i (xi), eta_i = dif x_i (eta))& \
&= integral_0^1 -(cancel((partial a)/(partial x_1)eta_1)+(partial a)/(partial x_2)eta_2)xi_1 + (cancel((partial a)/(partial x_1)xi_1)+(partial a)/(partial x_2)xi_2)eta_1 dif t &+ o(||xi||^2 + ||eta||^2) \
&&("derivative taken at" x_1=x_2=0) \
&= (partial a)/(partial x_2) (eta_2 xi_1 - xi_1 eta_2) +  o(||xi||^2 + ||eta||^2)
)$

$==> Omega(xi, eta) = (partial a)/(partial x_2) (eta_2 xi_1 - xi_1 eta_2) ==> Omega = (partial a)/(partial x_2) dif x_2 and dif x_1 = dif omega^1$. 

*Thm. (Stokes formula)* Let $omega$ be a $k$-form, $Omega$ be a chain of dim $k+1$.  Then $ integral_(partial Omega) omega= integral_Omega dif omega $

_Proof. See page 192, using the thm above._

#line()

*Def.* We say a differential form $omega$ is _closed_ if $dif omega = 0$.

A closed form, when integrated on a boundary, is always 0.

*Def.* A differential $k$-form $omega$ is called _exact_ if there exists a $(k-1)$-form $alpha$ s.t. $dif alpha = omega$.

For any differential form, we have $dif^2 omega = 0 ==>$ an exact form is closed.

Dually, for any chain $Omega$, $partial^2 Omega = 0$.

#pagebreak()

#line(length: 100%)
Chapter 08 Symplectic manifolds
#line(length: 100%)

A _symplectic manifold_ $(M^(2n),omega^2)$ is an even dimensional manifold $M^(2n)$ endowed with a closed nondegenerate differential $2$-form $omega^2$.

nondegenerate: $forall xi,eta in T_x M, omega^2|_x (xi,eta) = angle.l A xi, eta angle.r$, where $A$ is nondegenerate and anti-symmetric.

_Example._ $RR^(2n), quad x_1,...,x_n,y_1,...,y_n, quad omega^2 = dif y_1 and dif x_1 + ... + dif y_n and dif x_n$

The most important symplectic manifold for us is $T^* M$ (_cotangent bundle_, 余切丛), $ T^* M = union.big_(x in M) T_x^* M $
where $T_x^* M$ is the _cotangent space_ of $M$ at $x$, i.e. the space of $1$-forms on $T_x M$. 

#line()

The Lagrangian mechanics happens on $T M$, $ L: T M -> RR $

The Hamiltonian mechanics happens on $T^* M$, $ H: T^* M -> RR $

$H(p, q) = display(sup_(dot(q))) (angle.l p, dot(q) angle.r - L(dot(q), q)), quad p in T_q M$

The generalized momentum $p$ is a linear functional on $T_q M$.

#line()

On $T^* M$, there is _a natual symplectic form_ 
$ omega^2 = dif p and dif q = sum dif p_i and dif q_i $

$omega^2 = dif omega^1$, where $omega = p dif q$ is a $1$-form on $T^* M$.

Let $q$ be coordinates on $M$, $p$ be coordinates on $T_q^* M$. 

Let $N = T^* M$, $omega = p dif q$ is a 1-form on $N$. At point $x=(p,q) in N$,

$
omega|_x: &T_x N &&-> RR \
&(p dif q) xi &&= p dot.c xi_q
$

#line()

We next introduce the Hamiltonian vector field.

*Def.* To every vector $xi in T_x M$, where $(M,omega^2)$ is a symplectic manifold. We can associate a $1$-form $ omega_xi^1 (eta) = omega^2 (eta,xi), forall eta in T_x M $

This induces an isomorphism between $T_x M$ and $T_x^* M$, $xi |-> omega_xi^1$

We denote this isomorphism as $I$:
$ I: &T_x^*M &-> &T_x M \
&omega_xi^1 = omega^2 (dot.c, xi) &|-> &xi $

By the nondegeneracy, $omega^2 (eta,xi) = angle.l A eta, xi angle.r = angle.l eta, A^T xi angle.r$, thus $omega_xi^1$ is exactly the vector $A^T xi$.

Let $H: M -> RR$ be a function, then $dif H$ is a $1$-form on $T^* M$. By the isomorphism, there exists a vector field on $M$ denoted by $X_H = I dif H$, called the Hamiltonian vector field.

_但反过来, 每个 $M$ 上的 vector field 不一定是一个函数的微分. 如果是, 我们定义_:

*Def.* We say a vector field $X_H$ a _Hamiltonian vector field_, if there exists $H$ s.t. $omega(dot.c, X_H) = dif H$.

_Example._ $RR^2, quad (y,x), quad omega = dif y and dif x, quad H:RR^2->RR$ a Hamiltonian function

设 $H$ 对应的 Hamiltonian vector field 为 $X$, 则由定义有 $omega(xi, X) = dif H(xi)$

$==> mat(delim: "|", xi_y, X_y; xi_x, X_x) = (partial H)/(partial y) xi_y + (partial H)/(partial x) xi_x ==> X = (X_y, X_x) = (-(partial H)/(partial x), (partial H)/(partial y))$

#line()

Given Hamiltonian vector field $X_H$, we define the _Hamiltonian flow_ by solving the ODE
$ dot(x) = X_H (x), quad x in N = T^*M $
denoted by 
$ g^t: N &-> N \
x &|-> g^t x $

_Example._ 上面那个例题中, $H$ 导出的 Hamiltonian flow 便由 
#align(center, $(dot(y), dot(x)) = (-(partial H)/(partial x), (partial H)/(partial y))$) 
给出, 这即是 Hamiltonian canonical equation.

*Thm.* A Hamiltonian flow preserves the symplectic structure
$ (g^t)^* omega = omega $
_Proof. See page 204._ 
// TODO

#line()

*Law of energy conservation*

*Thm.* Let $H: M -> RR$ be a Hamiltonian function, then it is constant under the corresponding Hamiltonian flow (with Hamiltonian function $H$).

_Proof._ $space dif/(dif t) H(g^t x) = dif H (X_H) = omega(X_H, X_H) =0$.

\
#line(length: 100%)
 
*The algebraic structure of Hamiltonian mechanics*

#line()

*The commutator of vector fields*

Let $A(z)$ be a vector field on $RR^n$, we have the ODE $dot(z) = A(z)$.

Let $a^t$ be the flow of the ODE.

*Def.* Given a smooth function $phi: RR^n -> RR$, the Lie derivative of $phi$ along the vector field $A$ is defined as
$ (cal(L)_A phi) (z) = lr(dif/(dif t)mid(|))_(t=0) phi(a^t z) = dif phi dot.c A = sum A_i partial/(partial z_i) phi $
We denote
$ cal(L)(A) := A_1 (z) partial/(partial z_1) + ... + A_n (z) partial/(partial z_n) $

*Lemma.* The operator $cal(L)_B cal(L)_A - cal(L)_A cal(L)_B$ is a #underline("first order") linear operator.

_Proof._ 
#align(center, $display(
  cases(cal(L)_B cal(L)_A phi = sum_i B_i partial/(partial z_i) (sum_j A_j partial/(partial z_j) phi) = sum_(i,j) lr((B_i (partial A_j)/(partial z_i) (partial phi)/(partial z_j) + cancel(B_i A_j (partial^2 phi)/(partial z_i partial z_j) phi))),
  cal(L)_A cal(L)_B phi = sum_i A_i partial/(partial z_i) (sum_j B_j partial/(partial z_j) phi) = sum_(i,j) lr((A_i (partial B_j)/(partial z_i) (partial phi)/(partial z_j) + cancel(A_i B_j (partial^2 phi)/(partial z_i partial z_j) phi))))
) "(指相减时消掉)"$)

$==> (cal(L)_B cal(L)_A - cal(L)_A cal(L)_B) phi = sum_(i,j) (B_i (partial A_j)/(partial z_i) - A_i (partial B_j)/(partial z_i)) partial/(partial z_j) phi =: sum_(i,j) [A,B]_j space partial/(partial z_j) phi = [A,B] dot.c dot(phi)$

We denote $ [A,B]_j := sum_i (B_i (partial A_j)/(partial z_i) - A_i (partial B_j)/(partial z_i)) $

*Def.* The _commutator_ of two vector field $A$ and $B$ is the vector field $C$ for which
$ cal(L)_C = cal(L)_B cal(L)_A - cal(L)_A cal(L)_B $
denoted by $ C = [A, B] $

*Prop.* For all smooth vector fields $A,B,C$, we have

(1) linearity: $[a A + b B, C] = a[A,C] + b[B,C]$\
(2) anti-symmetry: $[A,B] = -[B,A]$\
(3) _Jacobi identity:_ $[[A,B],C] + [[B,C],A] + [[C,A],B] = 0$

These implies the space of $C^oo$ vector fields forms a _Lie algebra_.

*Thm.* Let $a^t, b^t$ be the flows generated by vector fields $A,B$ respectively. Then the flows _commute_ iff the commutator of the vector field vanish, i.e.
$ a^t circle.tiny b^s = b^s circle.tiny a^t <==> [A,B]=0 $

_Proof._ We first have 
$display(lr(partial^2/(partial s partial t)mid(|))_(t=s=0) (phi(a^t b^s z) - phi(b^s a^t z)) = (cal(L)_B cal(L)_A - cal(L)_A cal(L)_B) phi) = [A,B] dot.c dot(phi)$ 

This proves "$==>$".

For the "$<==$" part, if $[A,B]=0$, then $phi(a^t b^s z) - phi(b^s a^t z) = o(s^2 + t^2) quad (s,t-> 0)$

We partition the ractangle $[0,t) times [0,s)$ into $N^2$ equal small ractangles.

We deform the path of $b^s a^t$ into $a^t b^s$ by $N^2$ steps. The total error is $o(1)$.

Letting $N -> oo$, we get $phi(a^t b^s z) = phi(b^s a^t z), forall phi$.

#line()

*Poisson bracket*

*Def.* Let $F, H$ be two functions on a symplectic manifold $(M, omega)$, the _Poisson bracket_ ${F, H}$ is defined as the derivative of $F$ along the Hamiltonian flow of $H$,
$ {F,H}(z) = lr(dif/(dif t)mid(|))_(t=0) F(g_H^t z) = dif F (X_H) = underbrace(omega(X_H,X_F), "注意"F"和"H"的位置是反的") $
Since $omega$ is anti-symmetric, ${F,H} = -{H,F}$.

_Example._ $RR_((x,y))^2, quad omega = dif y and dif x$

$quad quad quad quad cases(dot(x) = (partial F)/(partial y), dot(y) = -(partial F)/(partial x)) quad cases(dot(x) = (partial H)/(partial y), dot(y) = -(partial H)/(partial x))$

$==> {F,H}(z) = lr(dif/(dif t)mid(|))_(t=0) F(g_H^t z) = (partial F)/(partial x) dot(x) + (partial F)/(partial y) dot(y) = (partial F)/(partial x) (partial H)/(partial y) - (partial F)/(partial y) (partial H)/(partial x)$.

*Prop.* The Poisson bracket has the following properties: $forall H_1,H_2,H_3 in C^oo (M)$, we have

(1) linearity \
(2) anti-symmetry \
(3) _Jacobi identity:_ ${{H_1, H_2}, H_3} + {{H_2, H_3}, H_1} + {{H_3, H_1}, H_2} = 0$ 

Thus, the space of $C^oo (M)$ also forms a Lie algebra under the Poisson bracket.

*Thm.* Let $Beta,Gamma$ be two Hamiltonian vector field with Hamiltonians $beta, gamma$. Then $[Beta,Gamma]$ is a Hamiltonian vector field whose Hamiltonian is exactly ${beta,gamma}$.

_Proof._ Let ${beta, gamma} = delta$. 

$forall alpha$, by Jacobi identity, we have
${alpha,delta} = {alpha, {beta, gamma}} = {{alpha, beta}, gamma} - {{alpha,gamma}, beta}$.

${{alpha, beta}, gamma} = cal(L)_Gamma {alpha,beta} = cal(L)_Gamma cal(L)_Beta alpha, space {{alpha,gamma}, beta} = cal(L)_Beta {alpha,gamma} = cal(L)_Beta cal(L)_Gamma alpha$

Let $Delta$ be the Hamiltonian vector field of $delta$, then ${alpha, delta} = cal(L)_Delta alpha$

$==> cal(L)_Delta = cal(L)_Gamma cal(L)_Beta - cal(L)_Beta cal(L)_Gamma = cal(L)_[Beta,Gamma]$

\
#line()

*Symplectic transformation*

_Example._ $H: RR^2-> RR, H(y,x) = 1/2 (y^2 + x^2)$, Hamiltonian equation $cases(dot(y) = -x, dot(x) = y)$

Let $cases(x= r sin theta, y= r cos theta) space$ be the polar coordinates.

$==> cases(dot(r) = ... = 0, dot(theta) = ... = 1)$

$H(r,theta) = 1/2 r^2$, if Hamiltonian equation holds, $cases(dot(r) = -(partial H)/(partial theta) = 0, dot(theta) = (partial H)/(partial r) = r)$, contradicts! \
_问题在于这一变换并不是辛变换!_ \
Instead of $(r, theta)$, we use $(I, theta)$, where $I = r^2/2$. Then $H=I, cases(dot(I) = -(partial H)/(partial theta) = 0, dot(theta) = (partial H)/(partial I) = 1) space$ agrees.

#figure(
  image("/img/handwritten/handwritten_5.jpg")
)
#figure(
  image("/img/handwritten/handwritten_6.jpg")
)
#figure(
  image("/img/handwritten/handwritten_7.jpg")
)
#figure(
  image("/img/handwritten/handwritten_8.jpg")
)
#figure(
  image("/img/handwritten/handwritten_9.jpg")
)
#figure(
  image("/img/handwritten/handwritten_10.jpg")
)
#figure(
  image("/img/handwritten/handwritten_11.jpg")
)
#figure(
  image("/img/handwritten/handwritten_12.jpg")
)
#figure(
  image("/img/handwritten/handwritten_13.jpg")
)
#figure(
  image("/img/handwritten/handwritten_14.jpg")
)
#figure(
  image("/img/handwritten/handwritten_15.jpg")
)
#figure(
  image("/img/handwritten/handwritten_16.jpg")
)
#figure(
  image("/img/handwritten/handwritten_17.jpg")
)
#figure(
  image("/img/handwritten/handwritten_18.jpg")
)
#figure(
  image("/img/handwritten/handwritten_19.jpg")
)

#pagebreak()



