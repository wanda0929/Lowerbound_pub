# Can JAN22's CZ exposure $2.947$ be proved analytically?

## Verdict

The value has to be identified correctly before trying to prove it:

| JAN22 problem | Pulse reported by JAN22 | $\Omega_{\max}T_R$ |
|---|---:|---:|
| two-qubit CZ | time-optimal, $T\Omega_{\max}=7.612$ | $2.957$ |
| two-qubit CZ | lowest exposure found, evaluated at $T\Omega_{\max}=30$ | $2.947$ |
| three-qubit $C_2Z$ | time-optimal Pulse 1 / Pulse 2 | $6.90$ / $7.52$ |
| three-qubit $C_2Z$ | lowest exposure found near $T\Omega_{\max}=16.74$ | $6.431$ |

JAN22 obtained $2.947$ with GRAPE.  The paper does **not** prove that it is a
lower bound, does not prove convergence as $T\to\infty$, and does not give an
exact pulse that attains the rounded decimal.  Calling $2.947$ a proven lower
bound would therefore reverse the logical direction of the numerical result.
More decisively, the investigation reported here found a lower-exposure pulse
and then certified the existence of an exact nearby CZ pulse with exposure
strictly below $2.935887$.  Thus $2.947$ is now mathematically excluded as the
lower bound for this model.

Let

$$
C_*:=\inf_{\text{exact global CZ pulses}}\Omega_{\max}T_R.
$$

What can presently be stated rigorously is

$$
\boxed{
2.48007<C_{\rm fib}
\leq C_*<2.935887,
}
\tag{1}
$$

where the exact-fiber analytical constant is

$$
C_{\rm fib}
=2\int_0^1c_{\rm fib}(r)\,dr
=2.480079367706997\ldots.
$$

The strict decimal inequality $C_{\rm fib}>2.48007$ is enclosed with Arb
interval arithmetic.  It sharpens the companion-state constant

$$
\begin{aligned}
C_{\rm comp}
&=\frac{\sqrt2}{2}\left(\sqrt3+\frac\pi3\right)
+2\int_{\pi/3}^{\pi/2}\sqrt{\cos\vartheta}\,d\vartheta\\
&=2.465455191694189\ldots.
\end{aligned}
$$

The first inequality is proved below without GRAPE.  It embeds the blockaded
two-atom sector and the symmetric square of the one-atom sector into the same
three-level space, where their overlap must travel from $+1$ to $-1$.  The
exact-fiber refinement retains both sector populations in the overlap
constraint, as well as exact loop closure and the CZ phase.  It strictly
strengthens the earlier Schmidt-entropy theorem
$(7\sqrt2-5)/3=1.6331649788\ldots$.  The upper inequality is a separate
computer-assisted theorem: interval propagation and a Krawczyk inclusion
prove an exact closing CZ root near a new 396-segment pulse and enclose its
exposure below $2.935887$.  There is still an approximately $0.455807$ gap.
Closing it
requires an exposure-weighted Hamilton--Jacobi--Bellman calibration not
contained in JAN22 or in the Petrosyan paper.

### What the published sources actually provide

The distinction above survives a source-by-source audit:

- **JAN22** gives the rounded value $2.947$ at one finite duration,
  $T\Omega_{\max}=30$, after GRAPE optimization.  It gives neither a
  convergence theorem in $T$ nor PMP costates for that exposure objective.
- The authors' public
  [Figshare pulse archive](https://doi.org/10.6084/m9.figshare.19658427)
  contains `01_cz.csv`, the time-optimal CZ pulse, and
  `04_c2z_minimal_time_in_r.csv`, the minimum-exposure three-qubit pulse.  It
  does **not** contain the minimum-exposure two-qubit CZ pulse associated with
  $2.947$.  Thus even the candidate trajectory needed to reverse-engineer a
  sharp certificate is absent from the published data.
- **The new upper certificate in this chapter** starts from the published
  time-optimal pulse, refines it for exposure, and then uses interval
  arithmetic rather than optimizer residuals to prove an exact nearby CZ
  solution with cost below $2.935887$.
- The August 2026 revision of the **Petrosyan** paper proves the finite-$B$
  Bell-preparation floor $(1+\pi/2)/B$.  It explicitly says that the authors
  did not find a special perfect-entangling gate near that floor; their gate
  searches instead gave average exposure $\gtrsim\pi/B$, and they identify
  the strong-blockade regime as an open challenge.
- **Fromonteil et al.** formulate the correct global HJB state space and
  certify the time-optimal CZ result by numerical characteristics.  Their
  running cost is time, not Rydberg exposure.
- **Astolfi, Jandura, and Pupillo** reduce time-optimal PMP extremals to a
  semianalytical quartic-potential problem.  PMP supplies necessary extremal
  conditions and is combined with numerical optimization; it does not solve
  the exposure objective or provide a global lower-bound certificate.
- **Naceur and Balada Gaggioli** give a differential-moment SDP hierarchy for
  rigorous outer reachability and optimal-time bounds.  This June 2026
  preprint is the first published framework found in this audit that can be
  adapted directly into a *global certificate generator* for the JAN22
  exposure problem.  It does not study Rydberg exposure, however, and its
  public code does not yet extract or rationalize the dual HJB/SOS
  certificate needed for a tight lower theorem.

No source in this chain contains a hidden proof of $2.947$, and Equation (1)
now proves that no such lower-bound theorem can exist for the stated model.
Determining $C_*$ remains a new optimal-control problem.

## The exact CZ optimization problem

At infinite blockade, the four computational inputs split into three types.
The $|00\rangle$ input is stationary.  The two one-active-atom inputs follow
the same effective two-level system, while $|11\rangle$ follows a collectively
enhanced one:

$$
H_k(t)=\frac{\sqrt{k}}2
\left[
\Omega(t)|g_k\rangle\langle r_k|
+\Omega(t)^*|r_k\rangle\langle g_k|
\right],
\qquad k=1,2,
\tag{2}
$$

with one shared control satisfying $|\Omega(t)|\leq\Omega_{\max}$.  Write

$$
|\psi_k(t)\rangle=g_k(t)|g_k\rangle+r_k(t)|r_k\rangle,
\qquad p_k(t)=|r_k(t)|^2.
$$

An exact gate requires both systems to close,

$$
r_1(T)=r_2(T)=0,
$$

and their return phases to obey

$$
g_1(T)=e^{i\xi_1},\qquad
g_2(T)=e^{i\xi_2},\qquad
\xi_2-2\xi_1=\pi\pmod{2\pi}.
\tag{3}
$$

JAN22's four-input average is exactly

$$
T_R=\frac14\int_0^T\left(2p_1(t)+p_2(t)\right)dt.
\tag{4}
$$

Thus the tight-bound problem is not a single population transfer.  One laser
must close two Bloch-sphere loops with incommensurate angular speeds
$1:\sqrt2$, while producing the nonlinear phase combination in Equation (3).
Any proof that prices only one of those requirements will be loose.

## What transfers from the Petrosyan proof—and what does not

Doultsinos, Delakouras, and Petrosyan consider two atoms with the finite
interaction

$$
H_{\mathrm{int}}=B|rr\rangle\langle rr|
$$

and prove the entanglement-preparation bound

$$
T_r\geq\frac{1+\pi/2}{B}.
\tag{5}
$$

Their 2026 revision also explains how the same floor applies to an averaged
two-qubit gate error under their finite-$B$ assumptions.  It does not give the
JAN22 constant.  In JAN22's strict blockade limit,

$$
\Omega_{\max}T_r
\geq
\left(1+\frac\pi2\right)\frac{\Omega_{\max}}B
\longrightarrow0.
\tag{6}
$$

The reason is physical: the Petrosyan proof charges population in the
$|rr\rangle$ channel through which $B|rr\rangle\langle rr|$ creates
entanglement.  Strict blockade removes that channel altogether.  The bounded
laser projected into the one-Rydberg manifold becomes the relevant nonlocal
resource.

The transferable idea is **cost per unit progress**:

1. find a coordinate that every successful gate must change;
2. bound its speed by the mechanism that generates the change;
3. divide instantaneous Rydberg cost by the maximum progress speed; and
4. integrate every unavoidable level crossing.

The next section applies that method and produces a rigorous floor.  It also
shows quantitatively why entanglement alone cannot reach the certified
$2.935887$ upper edge.

## A Petrosyan-inspired theorem: $C_*\geq1/\sqrt2$

### Force one ebit with one input

Apply an exact CZ gate, including an arbitrary removable one-qubit phase
$\theta$, to

$$
|++\rangle=\frac12(|00\rangle+|01\rangle+|10\rangle+|11\rangle).
$$

The output is

$$
\frac12\left(
|00\rangle+e^{i\theta}|01\rangle
+e^{i\theta}|10\rangle-e^{2i\theta}|11\rangle
\right).
\tag{7}
$$

The two conditional vectors on the second atom are orthogonal and have equal
norm, so Equation (7) has one ebit across the atom--atom cut.  Let

$$
S(t)=-\log_2 c_1(t)^2
$$

be the min-entropy, with $c_1$ the largest Schmidt coefficient.  This
evolution must cross every value from $S=0$ to $S=1$.

### Isolate the interaction created by blockade projection

Let $R_A=|r\rangle\langle r|$ and $Q_A=I-R_A$, with analogous operators for
atom $B$.  If $h_A$ and $h_B$ are the unprojected local laser Hamiltonians,
then

$$
\|h_A\|=\|h_B\|=\frac{|\Omega|}{2}.
$$

The ideal-blockade projector is
$\Pi=I-R_A\otimes R_B$.  Projection turns the otherwise local drive into

$$
\begin{aligned}
H
&=\Pi(h_A\otimes I+I\otimes h_B)\Pi\\
&=h_A\otimes Q_B+Q_A\otimes h_B\\
&=\underbrace{h_A\otimes I+I\otimes h_B}_{H_{\rm loc}}
+\underbrace{(-h_A\otimes R_B-R_A\otimes h_B)}_{H_{\rm int}}.
\end{aligned}
\tag{8}
$$

The first two terms cannot change Schmidt coefficients.  All change of $S$
is generated by $H_{\rm int}$.

### Bound entropy speed by population

Write the instantaneous Schmidt decomposition as

$$
|\Psi\rangle=\sum_{i=1}^{m}c_i|u_i\rangle|v_i\rangle,
\qquad m\leq3,
$$

where rank three—not rank two—is possible because each atom temporarily uses
$|0\rangle$, $|1\rangle$, and $|r\rangle$.  Define

$$
a_i=\langle u_i|R_A|u_i\rangle,
\quad
b_i=\langle v_i|R_B|v_i\rangle,
\quad
P_A=\sum_i c_i^2a_i,
\quad
P_B=\sum_i c_i^2b_i.
\tag{9}
$$

Strict blockade gives $P=P_A+P_B$.  Differentiation of the min-entropy gives

$$
|\dot S|
\leq\frac{2}{(\ln2)c_1}
\sum_{i>1}c_i
|\langle u_1v_1|H_{\rm int}|u_iv_i\rangle|.
\tag{10}
$$

Projector Cauchy--Schwarz and Equation (8) imply

$$
|\langle u_1v_1|H_{\rm int}|u_iv_i\rangle|
\leq\frac{|\Omega|}{2}
\left(\sqrt{a_1a_i}+\sqrt{b_1b_i}\right).
\tag{11}
$$

Because at most two indices satisfy $i>1$, Cauchy--Schwarz and
$2xy\leq x^2+y^2$ give

$$
\sum_{i>1}c_i\sqrt{a_1a_i}
\leq\frac{P_A}{\sqrt2c_1},
\qquad
\sum_{i>1}c_i\sqrt{b_1b_i}
\leq\frac{P_B}{\sqrt2c_1}.
\tag{12}
$$

Combining Equations (10)--(12),

$$
\boxed{
|\dot S|
\leq
\frac{\Omega_{\max}}{\sqrt2(\ln2)c_1^2}P.
}
\tag{13}
$$

For the input $|++\rangle$, block orthogonality makes its instantaneous
Rydberg population equal to JAN22's averaged integrand:

$$
P(t)=\frac14(0+p_1+p_1+p_2)
=\frac14(2p_1+p_2).
\tag{14}
$$

Let $\tau$ be the first time $S(\tau)=1$.  Since $c_1^2=2^{-S}$ before that
first crossing, Equations (13)--(14) give

$$
\begin{aligned}
T_R
&\geq\frac{\sqrt2\ln2}{\Omega_{\max}}
\int_0^\tau2^{-S}|\dot S|dt\\
&\geq\frac{\sqrt2\ln2}{\Omega_{\max}}
\int_0^1 2^{-s}ds
=\frac{1}{\sqrt2\Omega_{\max}}.
\end{aligned}
\tag{15}
$$

This proves the baseline estimate $C_*\geq1/\sqrt2$.  It is pulse-shape and
duration independent, but it uses only the entangling action of CZ.  It throws
away the much more expensive requirement that the two $1:\sqrt2$ systems
close simultaneously with the correct relative phase.  That is why it is far
below the certified upper edge.  It is also only the first rung: the exact
state structure gives the stronger left inequality in Equation (1), proved
next.

### A finite-dimensional route to a stronger intermediate bound

There is a more faithful Petrosyan-style minimization that may improve
Equation (15) without yet solving the full tight-bound problem.  For the
$|++\rangle$ witness, write the two sector states as

$$
(g_1,r_1),\qquad(g_2,r_2),
\qquad |g_k|^2+|r_k|^2=1.
$$

In the one-atom basis $(|0\rangle,|1\rangle,|r\rangle)$, the exact bipartite
coefficient matrix is

$$
M=\frac12
\begin{pmatrix}
1 & g_1 & r_1\\
g_1 & g_2 & r_2/\sqrt2\\
r_1 & r_2/\sqrt2 & 0
\end{pmatrix}.
\tag{16}
$$

Its singular values are the Schmidt coefficients, so
$S=-\log_2\sigma_{\max}(M)^2$.  Define the exact cost-per-entropy-speed
envelope

$$
G_{\rm CZ}(s)=
\inf_{\substack{|g_k|^2+|r_k|^2=1\\
                 -\log_2\sigma_{\max}(M)^2=s}}
\frac{(2|r_1|^2+|r_2|^2)/4}
     {\max_{|\Omega|\leq\Omega_{\max}}|\dot S|/\Omega_{\max}}.
\tag{17}
$$

The same coarea argument used by Petrosyan would then give the rigorous
finite-dimensional bound

$$
C_*\geq\int_0^1G_{\rm CZ}(s)\,ds.
\tag{18}
$$

Unlike the estimate leading to Equation (15), Equation (17) retains the exact
sector weights, the strict-blockade zero in the lower-right corner of $M$, and
the common $1:\sqrt2$ drive.  Proving an explicit lower envelope for
$G_{\rm CZ}$ is therefore a concrete route to a larger fully analytical
bound.  Before phase gauges it has six real state variables; two local phase
gauges reduce it to four, and fixing $s$ leaves a three-dimensional algebraic
level set.  It is not a pulse search.

It still cannot by itself prove tightness: minimizing separately on each
entropy level discards whether the minimizing states join into one reachable
trajectory that closes both sectors.  The global HJB calibration below is
what restores that information.

## A Schmidt-entropy theorem: $C_*\geq(7\sqrt2-5)/3$

Equation (17) can be bounded analytically without solving its full
four-variable, gauge-reduced minimization.  The resulting constant is still
not tight, but it is more than twice the first $1/\sqrt2$ estimate.  The
companion-state theorem in the next section supersedes it while using a
different progress coordinate.

### Exact Schmidt-speed identity

The matrix $M$ in Equation (16) is complex symmetric.  Its Takagi
factorization is

$$
M=\sum_j c_j u_j u_j^T,
\qquad c_1\geq c_2\geq c_3\geq0,
\qquad \lambda:=c_1^2=2^{-S}.
\tag{19}
$$

Write the leading Takagi vector in the local basis
$(|0\rangle,|1\rangle,|r\rangle)$ as

$$
u_1=(u_0,u_1,u_r)^T,
\qquad
a=|u_0|^2,
\quad b=|u_1|^2,
\quad z=|u_r|^2.
\tag{20}
$$

An unprojected laser is local across the atom--atom cut and therefore cannot
change any $c_j$.  In coefficient-matrix language, ideal blockade changes
only one part of that local equation: it deletes the derivative of the
forbidden $M_{rr}$ entry.  Since
$M_{1r}=r_2/(2\sqrt2)$, the deleted term has magnitude
$|\Omega r_2|/(2\sqrt2)$.  First-order singular-value perturbation therefore
gives the exact maximum speed

$$
\boxed{
\max_{|\Omega|\leq\Omega_{\max}}|\dot S|
=
\frac{\Omega_{\max}|r_2|z}
     {\sqrt2(\ln2)\sqrt\lambda}.
}
\tag{21}
$$

This identity is much sharper than bounding the whole projected interaction
by its operator norm: it says that the entropy speed is controlled by the
specific two-active-atom Rydberg amplitude $r_2$ and the Rydberg weight $z$ of
the leading Schmidt vector.  At a Schmidt degeneracy, Equation (21) is read as
the corresponding upper Dini-derivative bound; this is sufficient for the
coarea argument below.

### Two structural constraints on the leading Schmidt vector

Set

$$
x=|r_1|^2,
\qquad y=|r_2|^2,
\qquad P=\frac{2x+y}{4}.
\tag{22}
$$

The reduced density matrix $\rho=MM^\dagger$ always has

$$
\rho_{00}=\frac14(1+|g_1|^2+|r_1|^2)=\frac12.
\tag{23}
$$

Its other two eigenvalues sum to $1-\lambda$, so each is no larger than
$1-\lambda$.  Expanding Equation (23) in the eigenbasis of $\rho$ gives, for
$\lambda>1/2$,

$$
\frac12
\leq \lambda a+(1-\lambda)(1-a),
\qquad\Longrightarrow\qquad
\boxed{a\geq\frac12.}
\tag{24}
$$

The $r$ row of the Takagi equation $M\overline{u_1}=\sqrt\lambda u_1$
gives a second constraint:

$$
2\sqrt{\lambda z}
\leq \sqrt{xa}+\sqrt{\frac{yb}{2}},
\qquad a+b+z=1.
\tag{25}
$$

Equations (24)--(25), together with $0\leq x,y\leq1$, imply the elementary
inequality

$$
\boxed{
\frac{P}{\sqrt y\,z}\geq2\lambda+\frac12.
}
\tag{26}
$$

For completeness, this minimization can be checked without a numerical
optimizer.  Put $q=\sqrt y$.  When the first term on the right of Equation
(25) is needed, the least admissible $x$ saturates that equation.  Substitution
into the left side of Equation (26) gives

$$
F(q)=
\frac{2\lambda}{a q}
-\frac{\sqrt{2\lambda b}}{a\sqrt z}
+\frac{q(1-z)}{4az}.
\tag{27}
$$

This convex function of $q$ is minimized either at $q=1$ or at
$q^2=8\lambda z/(1-z)$.  In both cases it decreases as
$b$ increases, so $b=1/2-z$ and $a=1/2$ give the relaxed minimum.  For the
$q=1$ branch, setting $t=\sqrt{1/(2z)-1}$ yields the explicit square

$$
F(1)=
\left(t-\sqrt{2\lambda}\right)^2
+2\lambda+\frac12.
\tag{28}
$$

For the interior branch, $z\leq1/(8\lambda+1)$ and

$$
F(q)=
\frac{\sqrt{2\lambda/z}}
{\sqrt{1-z}+\sqrt{1/2-z}}
\geq2\lambda+\frac12.
\tag{29}
$$

The last inequality follows by differentiating in $z$, evaluating at
$z=1/(8\lambda+1)$, and squaring; the remaining numerator is
$16m^3-12m^2+1>0$ for $m=2\lambda\in[1,2]$.  If Equation (25) can be
satisfied with $x=0$, it instead gives
$z\leq1/[2(8\lambda+1)]$ and the stronger
$F\geq4\lambda+1/2$.  These three cases prove Equation (26).  Notice that the
relaxation equality behind Equation (28),

$$
y=1,
\quad a=\frac12,
\quad z=\frac{1}{2(2\lambda+1)},
\quad x=\frac{\lambda}{2\lambda+1},
\tag{30}
$$

need not be a physical trajectory.  That deliberate loss of reachability is
why the resulting theorem remains below the GRAPE candidate.

### Integrate every entropy crossing

Combining Equations (21), (22), and (26) gives the pointwise price of changing
the min-entropy:

$$
\frac{P}
{\max|\dot S|/\Omega_{\max}}
\geq
\frac{\ln2}{\sqrt2}\sqrt\lambda(4\lambda+1),
\qquad \lambda=2^{-S}.
\tag{31}
$$

Every exact CZ trajectory carries the $|++\rangle$ witness from $S=0$ to
$S=1$.  Coarea therefore yields

$$
\begin{aligned}
C_*
&\geq
\frac{\ln2}{\sqrt2}
\int_0^1
\left(4\,2^{-3s/2}+2^{-s/2}\right)ds\\
&=
\boxed{\frac{7\sqrt2-5}{3}}
=1.6331649788\ldots.
\end{aligned}
\tag{32}
$$

This proof is pulse-shape independent, allows arbitrary duration and laser
phase, and uses no GRAPE data.  Numerically it closes only about 55% of the
distance to the certified upper edge.  The remaining gap is not a missing
factor: Equations (24)--(30) still minimize independently on each entropy
level and discard simultaneous reachability, both-sector closure, and the
prescribed winding of the CZ phase.  Those are exactly the global constraints
retained by the HJB problem below.

## A stronger companion-state theorem: $C_*\geq2.4654551916\ldots$

The two effective TLSs can be compared in one common three-level space.  This
exposes the precise dynamical term removed by perfect blockade and gives a
much more expensive progress coordinate than Schmidt entropy.

### Embed the two sectors in the same spin-1 space

Use dimensionless time $s=\Omega_{\max}t$ and
$u=\Omega/\Omega_{\max}$, so $|u|\leq1$.  Define two normalized vectors

$$
A=(g_2,r_2,0)^T,
\qquad
B=(g_1^2,\sqrt2g_1r_1,r_1^2)^T.
\tag{32a}
$$

$B$ is the symmetric square of the one-atom spinor, so

$$
\|B\|^2=(|g_1|^2+|r_1|^2)^2=1,
\qquad \|A\|=1.
\tag{32b}
$$

Both vectors share the same first coupling,

$$
H_0=\frac1{\sqrt2}
\begin{pmatrix}
0&u&0\\
\bar u&0&0\\
0&0&0
\end{pmatrix}.
\tag{32c}
$$

The symmetric-square vector has one additional coupling,

$$
iA'=H_0A,
\qquad
iB'=(H_0+H_1)B,
\qquad
H_1=\frac1{\sqrt2}
\begin{pmatrix}
0&0&0\\
0&0&u\\
0&\bar u&0
\end{pmatrix}.
\tag{32d}
$$

Thus $H_1$ is exactly the unblocked path to the two-Rydberg component that is
missing from the ideal-blockade sector.  This is the direct analogue of
isolating the entangling resource in the Petrosyan proof.

### An overlap forced from $+1$ to $-1$

Consider

$$
z=A^\dagger B
=\bar g_2g_1^2+\sqrt2\bar r_2g_1r_1,
\qquad q=\Re z.
\tag{32e}
$$

The common Hamiltonian $H_0$ cancels when differentiating the overlap.  Only
the blockade difference remains:

$$
\boxed{
z'=-iA^\dagger H_1B
=-\frac{i}{\sqrt2}\bar r_2u r_1^2.
}
\tag{32f}
$$

Initially $A=B=(1,0,0)^T$, so $q(0)=1$.  At every exact CZ endpoint,
$r_1=r_2=0$ and $g_2=-g_1^2$, so $A=-B$ and $q(S)=-1$.  With

$$
x=|r_1|^2,
\qquad y=|r_2|^2,
\qquad L=\frac{2x+y}{4},
\tag{32g}
$$

Equation (32f) gives

$$
|q'|\leq\frac{x\sqrt y}{\sqrt2}.
\tag{32h}
$$

The overlap also limits how large $x$ can be at a given $q$.  The first two
components of $B$ have squared norm $1-x^2$, hence

$$
|q|\leq|z|\leq\sqrt{1-x^2},
\qquad
x\leq X(q):=\sqrt{1-q^2}.
\tag{32i}
$$

This endpoint-sensitive constraint is what upgrades the elementary chord
bound.

### Exact pointwise cost minimization

For $x,y>0$,

$$
\frac{L}{x\sqrt y/\sqrt2}
=\frac{\sqrt2}{4}\left(\frac2{\sqrt y}+\frac{\sqrt y}{x}\right).
\tag{32j}
$$

At fixed $x$, the right side is minimized by $y=\min(2x,1)$; the resulting
answer decreases with $x$.  Relaxing to the largest value allowed by
Equation (32i), $x=X(q)$, therefore proves

$$
L\geq c(q)|q'|,
\tag{32k}
$$

where the even function $c$ is

$$
c(q)=
\begin{cases}
\dfrac{\sqrt2}{4}
\left(2+\dfrac1{\sqrt{1-q^2}}\right),
&|q|\leq\dfrac{\sqrt3}{2},\\[8pt]
(1-q^2)^{-1/4},
&\dfrac{\sqrt3}{2}\leq|q|\leq1.
\end{cases}
\tag{32l}
$$

The apparent endpoint divergence is integrable.  Let
$F(q)=\int_0^q c(v)\,dv$.  Integration along any admissible pulse—regardless
of reversals or repeated crossings—gives

$$
\Omega_{\max}T_R
=\int_0^S L\,ds
\geq\int_0^S\left|\frac{dF(q(s))}{ds}\right|ds
\geq F(1)-F(-1).
\tag{32m}
$$

Evaluating the one-dimensional integral, with $q=\sin\vartheta$ in its final
piece, proves

$$
\boxed{
\begin{aligned}
C_*&\geq C_{\rm comp}:=2\int_0^1c(q)\,dq\\
&=\frac{\sqrt2}{2}\left(\sqrt3+\frac\pi3\right)
+2\int_{\pi/3}^{\pi/2}\sqrt{\cos\vartheta}\,d\vartheta\\
&=2.465455191694189\ldots.
\end{aligned}
}
\tag{32n}
$$

### Why $2.465455\ldots$ is not a pulse recipe

The equality conditions prove that no individual admissible pulse can attain
$C_{\rm comp}$.  Equality in every step above would require

$$
x=\sqrt{1-q^2},
\qquad y=\min(2x,1),
\qquad |q'|=\frac{x\sqrt y}{\sqrt2}
\tag{32na}
$$

almost everywhere while $q$ crosses from $1$ to $-1$.  In the central region
$|q|<\sqrt3/2$, Equation (32na) forces $x>1/2$ and therefore $y=1$.  But
$y=|r_2|^2=1$ implies $g_2=0$.  The exact $k=2$ Schrödinger equation is

$$
ig_2'=\frac{u r_2}{\sqrt2}.
\tag{32nb}
$$

An absolutely continuous function that is zero on an interval has derivative
zero almost everywhere there.  Since $|r_2|=1$, Equation (32nb) then forces
$u=0$, and the exact companion identity gives $q'=0$.  The overlap therefore
cannot cross the central region while saturating the lower-bound chain.  This
contradiction remains valid for measurable and rapidly switching controls.
Consequently every individual exact CZ pulse satisfies

$$
\boxed{\Omega_{\max}T_R>C_{\rm comp}.}
\tag{32nc}
$$

This strict nonattainment statement does **not by itself** produce a uniform
$\epsilon>0$ with $C_*\geq C_{\rm comp}+\epsilon$: a sequence of increasingly
rapid pulses might in principle approach a bound that no single pulse
attains.  The exact-fiber refinement below supplies such a uniform
improvement by tightening one relaxed inequality.  It still does not retain
the complete shared-control trajectory.  Thus $2.465455\ldots$ is a rigorous
forbidden edge, not a waveform specification and not evidence that a pulse of
that cost exists.

This is a duration-independent analytical theorem.  It uses exact closure and
the full CZ sign, and it raises the certified lower/upper ratio from about 55%
to about 84%.  It is still not tight because the pointwise minimization in
Equation (32j) allows the populations $(x,y)$ to be chosen independently at
each overlap value; it does not require those choices to form one trajectory
under the shared $1:\sqrt2$ control.  The HJB calibration below is the
mechanism that restores that final reachability constraint.

### Exact-fiber refinement: $C_*\geq2.4800793677\ldots$

Equation (32i) used only the norm of the first two components of $B$.  The
actual overlap gives a sharper constraint that keeps both populations.  The
triangle inequality applied directly to Equation (32e) gives

$$
|z|\leq M(x,y):=(1-x)\sqrt{1-y}
+\sqrt{2x(1-x)y}.
\tag{32nd}
$$

This is a sharp upper fiber envelope: the two complex terms can be phase
aligned.  Define the nondecreasing function

$$
c_{\rm fib}(r):=
\inf_{\substack{0<x,y\leq1\\M(x,y)\geq r}}
\frac{\sqrt2}{4}
\left(\frac2{\sqrt y}+\frac{\sqrt y}{x}\right),
\qquad0\leq r<1.
\tag{32ne}
$$

The feasible sets shrink as $r$ increases, which proves monotonicity.  At the
instantaneous physical state, Equations (32f), (32g), and (32nd) imply

$$
L\geq c_{\rm fib}(|z|)|z'|
\geq c_{\rm fib}(|q|)|q'|.
\tag{32nf}
$$

If $x=0$ or $y=0$, then $z'=0$ and the truncated form of this inequality is
immediate.  To handle the integrable divergence at $|q|=1$ without writing an
ambiguous product $\infty\cdot0$, set
$c_N=\min(c_{\rm fib},N)$ and
$F_N(q)=\int_0^q c_N(|v|)\,dv$.  Every absolutely continuous pulse obeys

$$
\int_0^S L\,ds
\geq\int_0^S\left|\frac{dF_N(q(s))}{ds}\right|ds
\geq F_N(1)-F_N(-1).
\tag{32ng}
$$

Monotone convergence as $N\to\infty$ handles arbitrary backtracking and
proves the exact analytical theorem

$$
\boxed{
C_*\geq C_{\rm fib}:=2\int_0^1c_{\rm fib}(r)\,dr.
}
\tag{32nh}
$$

The remaining two-variable minimization has a one-parameter algebraic
solution.  Put

$$
B=\frac{2x}{1-x},
\qquad y=\sin^2\eta,
\qquad \tan\eta=\kappa\sqrt B.
\tag{32ni}
$$

Interior Lagrange stationarity on the active boundary $M(x,y)=r$ reduces to

$$
\kappa^3B^2-A(\kappa)B-Q(\kappa)=0,
\tag{32nj}
$$

where

$$
\begin{aligned}
A(\kappa)&=4\kappa^4-2\kappa^2-2\kappa
=2\kappa(\kappa-1)(2\kappa^2+2\kappa+1),\\
Q(\kappa)&=8\kappa^4-12\kappa^3+4\kappa^2+4\kappa-4
=4(\kappa-1)(2\kappa^3-\kappa^2+1).
\end{aligned}
\tag{32nk}
$$

For $0<\kappa<1$, both $A$ and $Q$ are negative, so Equation (32nj) has no
positive $B$.  For $\kappa>1$, both are positive and there is exactly one
positive root,

$$
B(\kappa)=
\frac{A(\kappa)+
\sqrt{A(\kappa)^2+4\kappa^3Q(\kappa)}}{2\kappa^3}.
\tag{32nl}
$$

No boundary point omitted here can be cheaper: $x=0$ or $y=0$ makes the ratio
infinite; $x=1$ is infeasible for $r>0$; at $y=1$, increasing $B$ lowers the
ratio and a small decrease of $\eta$ restores the active constraint; and the
constraint cannot be inactive because the ratio has no unconstrained
interior minimum.  These observations force every global minimizer into the
stationary branch above.  Differentiating Equation (32nj) gives

$$
B'=
\frac{2(2\kappa^3+\kappa+2)B+
\frac4\kappa(2\kappa^4-\kappa^2-2\kappa+3)}
{2\kappa^3B-A}>0,
\tag{32nla}
$$

because the denominator is the positive square root in Equation (32nl), and
both terms in the numerator are positive for $\kappa>1$.  To make the other
monotonicity claim checkable rather than graphical, put $h=\kappa-1$.  After
using Equation (32nj), the numerator of $d\log r/d\kappa$ is
$2[BP_B(h)+P_0(h)]/\kappa$, where

$$
\begin{aligned}
P_B(h)={}&32h^{10}+336h^9+1576h^8+4376h^7+7912h^6
+9580h^5\\
&+7682h^4+3890h^3+1118h^2+142h+4,\\
P_0(h)={}&64h^{10}+544h^9+2128h^8+5040h^7+7840h^6
+8200h^5\\
&+5764h^4+2628h^3+696h^2+72h.
\end{aligned}
\tag{32nlb}
$$

These polynomials are positive.  The corresponding denominator is

$$
2\kappa^2(B+2)(B\kappa+1)(B\kappa^2+1)
(-B\kappa^2+2\kappa^3-\kappa-1).
\tag{32nlc}
$$

Its last factor is $-(2\kappa^3B-A)/(2\kappa)<0$, while every other factor is
positive.  Hence $r'(\kappa)<0$.  Explicitly,

$$
\begin{aligned}
x(\kappa)&=\frac{B}{B+2},
&y(\kappa)&=\frac{\kappa^2B}{1+\kappa^2B},\\
r(\kappa)&=
\frac{2(1+\kappa B)}{(B+2)\sqrt{1+\kappa^2B}}
\end{aligned}
\tag{32nm}
$$

decreases strictly from $1$ to $0$ as $\kappa$ runs from $1$ to infinity.
Thus the branch supplies exactly one global minimizer for every
$0<r<1$.  Its endpoints satisfy

$$
B\sim2\sqrt{2(\kappa-1)},
\quad
c_{\rm fib}(r)\sim[2(1-r)]^{-1/4}
\quad(\kappa\downarrow1),
\tag{32nn}
$$

and $(x,y,r)\to(1,1,0)$ with
$c_{\rm fib}(0)=3\sqrt2/4$ as $\kappa\to\infty$.  This also proves that the
integral in Equation (32nh) is finite.  Substitution of Equations
(32nl)--(32nm) gives

$$
C_{\rm fib}=2.480079367706997\ldots.
\tag{32no}
$$

The analytical proof is the inequality and global minimization above, not a
pulse search.  The verifier
`verification/jan22_cz_exposure_fiber_bound.py` independently evaluates the
one-dimensional branch and uses 160-bit Arb lower sums to prove the strict
decimal statement

$$
\boxed{C_*>2.48007.}
\tag{32np}
$$

This refinement is still not tight.  Its minimizing population and phase
fiber may be selected separately at each $r$; those selected points need not
form one trajectory under the shared control.  Capturing that obstruction
requires the relative phase and velocity cone introduced below.

## A rigorous upper certificate below JAN22's $2.947$

The upper side of Equation (1) is stronger than another GRAPE result.  GRAPE
and direct collocation were used only to *discover* a 396-segment,
full-amplitude phase pulse.  Two independent propagators reproduce

$$
S=\Omega_{\max}T=7.73903668164599,
\qquad
\Omega_{\max}T_R=2.9358859021125854\ldots,
\tag{32o}
$$

with both Rydberg endpoint amplitudes below $6.5\times10^{-16}$ and CZ phase
residual below $2.6\times10^{-14}$.  Those floating-point residuals are strong
evidence, but are not yet an exact upper-bound proof.

### Why there are five independent endpoint equations

For a closed pulse, unitarity already fixes $|g_1|=|g_2|=1$.  It is therefore
rank-deficient to impose all four real components of closure and both real
components of $g_2+g_1^2=0$.  The independent terminal map is

$$
F=\left(
\Re r_1,\Im r_1,
\Re r_2,\Im r_2,
\Im\{g_2\overline{g_1^2}\}
\right)\in\mathbb R^5.
\tag{32p}
$$

At a zero of $F$, the last complex number has modulus one.  Its real sign
distinguishes the disconnected identity and CZ branches; the CZ branch has
$\Re\{g_2\overline{g_1^2}\}<0$.

### Interval existence proof

Fix 392 of the candidate's phase values exactly and retain the duration and
four phases as the five variables $v$.  Around a 100-digit approximation
$v_0$, take a five-dimensional interval box $X$ of radius $10^{-80}$.  Let
$C$ be an approximate inverse of $DF(v_0)$.  Arb ball arithmetic evaluates
the complete 396-segment trigonometric propagator, its derivative enclosure
$[DF(X)]$, and the Krawczyk map

$$
K(X)=v_0-CF(v_0)+\left(I-C[DF(X)]\right)(X-v_0).
\tag{32q}
$$

The verifier establishes both the strict inclusion and contraction bound

$$
K(X)\subset\operatorname{int}X,
\qquad
\left\|I-C[DF(X)]\right\|_\infty<1.20\times10^{-76}<1.
$$

The existence and uniqueness clauses of the Krawczyk theorem therefore prove
that $F$ has a unique **exact** zero in $X$; this is not an
optimizer-tolerance statement.  On the entire box, the same outward-rounded
calculation gives

$$
\begin{aligned}
\Re\{g_2\overline{g_1^2}\}
&\in-1\pm8.35\times10^{-79},\\
\Omega_{\max}T_R
&\in2.9358859021125700936667157351909\ldots
   \pm2.91\times10^{-79}.
\end{aligned}
\tag{32r}
$$

Consequently the exact root is on the CZ branch and

$$
\boxed{C_*<2.935887.}
$$

The candidate data, ordinary exact-segment cross-check, and 500-bit interval
proof are respectively
`verification/reference_data/jan22_cz_exposure_candidate_396.json`,
`verification/jan22_cz_exposure_candidate.py`, and
`verification/jan22_cz_exposure_interval_upper.py`.  This settles the upper
side rigorously and disproves $2.947$ as a lower bound.  It does **not** prove
that $2.935887$ is optimal; only a matching global lower calibration could do
that.

### Is the upper witness at least stationary?

This question matters before trying to force an HJB calibration through the
witness.  Fix its first phase to remove the global laser-phase gauge.  For the
remaining 395 phases and the duration, let $J_F$ be the Jacobian of the five
independent terminal residuals in Equation (32p), and let $g=\nabla C$ be the
exposure gradient.  First-order constrained stationarity requires a multiplier
$\lambda\in\mathbb R^5$ such that

$$
g+J_F^T\lambda=0.
\tag{32ra}
$$

Centered differences with steps from $2\times10^{-5}$ down to
$2\times10^{-7}$ give stable singular values

$$
\sigma(J_F)=(0.414221,0.228275,0.196449,0.087056,0.067375)
$$

and hence full row rank.  At step $10^{-6}$, the relative KKT residual is

$$
\frac{\|g+J_F^T\lambda\|_2}{\|g\|_2}
=8.26\times10^{-7}.
\tag{32rb}
$$

The projection of $g$ into the feasible tangent space $\ker J_F$ has the same
$2.53\times10^{-7}$ norm.  Thus no resolved first-order feasible descent
direction remains in this 396-segment discretization.  This is strong evidence
that the pulse is a constrained stationary point, not proof of local
minimality and certainly not proof of global optimality.  The reproducible
check is `verification/jan22_cz_exposure_stationarity.py`.

## Why the full complex companion overlap is still insufficient

A natural last attempt is to keep both $q=\Re z$ and $p=\Im z$ and seek a
two-dimensional calibration $W(z)$.  This cannot close the gap.  In fact,
every globally valid calibration depending only on $z$ obeys the ceiling

$$
\boxed{
|W(-1)-W(1)|
\leq\frac{5\pi}{2\sqrt2}-3
=2.553603672697957\ldots.
}
\tag{32s}
$$

Here is a direct proof.  For fixed $x=|r_1|^2$ and $y=|r_2|^2$, the arbitrary
laser phase makes the possible $z$-velocities an isotropic disk with radius

$$
v_z=\frac{x\sqrt y}{\sqrt2},
\qquad
\frac{L}{v_z}
=\frac{\sqrt2}{4}\left(\frac2{\sqrt y}+\frac{\sqrt y}{x}\right).
\tag{32t}
$$

At every complex $z$ of modulus $r\leq1/\sqrt2$, there is a physical state
with

$$
y=1,
\qquad
x=x_+(r):=\frac{1+\sqrt{1-2r^2}}2,
\qquad
R_1(r)=\frac{\sqrt2}{4}\left(2+\frac1{x_+(r)}\right).
$$

At every $1/\sqrt2\leq r\leq1$, another physical family has $y=2x$ and
aligned overlap terms, where $x=x(r)\in[0,1/2]$ is defined by

$$
r=(1-x)\sqrt{1-2x}+2x\sqrt{1-x},
\qquad
R_2(r)=\frac1{\sqrt{x(r)}}.
\tag{32u}
$$

A global $W(z)$ must satisfy its gradient inequality at **every** physical
state over the same $z$, including these cheaper fibers.  Integrating that
restriction along the real diameter gives

$$
\begin{aligned}
|W(-1)-W(1)|
&\leq2\left[
\int_0^{1/\sqrt2}R_1(r)\,dr
+\int_{1/\sqrt2}^1R_2(r)\,dr
\right]\\
&=2\left[
\frac\pi4+
\left(\frac{5\pi}{4\sqrt2}-\frac\pi4-\frac32\right)
\right]
=\frac{5\pi}{2\sqrt2}-3.
\end{aligned}
\tag{32v}
$$

The obstruction is visible on the certified candidate itself.  At its
midpoint,

$$
z\simeq-0.0000226+0.367573i,
\quad x\simeq0.895467,
\quad y\simeq0.449201,
\quad \frac{L}{|z'|}\simeq1.31965.
$$

The first cheaper fiber realizes the same $z$ with ratio $1.08845$.  Thus a
global function of $z$ is constrained by a state the candidate never visits
and cannot saturate on the candidate.  The missing information is not another
component of the overlap; it is the independent pair of populations and the
relative common-control phase.  Together with the CZ phase these form the
four-dimensional quotient used by the HJB equation below.  A two-coordinate
certificate that quantifies over the hidden coordinates is simply the full
four-dimensional HJB inequality in disguised form.

### The exact common-control reachability constraint

The two populations are not free to follow arbitrary paths.  Their common
laser gives an exact velocity ellipse that is absent from the companion
bound.  Define

$$
J=\bar g_1r_1g_2\bar r_2=P+iQ,
\qquad d=x(1-x),
\qquad A=u\bar g_1r_1=a+ib.
\tag{32w}
$$

The amplitude bound gives $a^2+b^2\leq d$.  Direct differentiation of the
populations gives the two exact identities

$$
x'=-b,
\qquad
\frac{d}{\sqrt2}y'=aQ-bP=aQ+Px'.
\tag{32x}
$$

Eliminating the two control quadratures therefore proves

$$
\boxed{
\left(Px'-\frac{d}{\sqrt2}y'\right)^2+Q^2x'^2\leq dQ^2,
\qquad x'^2\leq d.
}
\tag{32y}
$$

Equation (32y) is the exact projected velocity cone whenever $Q\neq0$.  At
$Q=0$, one must use the undivided form of Equation (32x), which imposes the
nontrivial compatibility condition

$$
Px'=\frac{d}{\sqrt2}y'.
\tag{32z}
$$

This is genuine extra reachability information: it forbids choosing $x'$ and
$y'$ independently while minimizing cost on each companion-overlap level.
The nonlinear gate-phase velocity is simultaneously

$$
\Phi'
=\frac{a}{1-x}
-\frac{aP+bQ}{\sqrt2d(1-y)}.
\tag{32aa}
$$

The apparent divisions at a closed endpoint are coordinate singularities,
not physical divergences.  A smooth trajectory leaving $x=y=0$ has
$y=2x+O(s^3)$, $P=\sqrt2d+O(s^3)$, and $Q=O(s^3)$; the two leading terms in
Equation (32aa) cancel.  Consequently a valid proof cannot bound those terms
separately or assign an arbitrary phase velocity at $d=0$.

Equations (32y)--(32aa) narrow the remaining problem but have not yet improved
the integrated constant $C_{\rm fib}$.  They are not a closed variational
system without the dynamics of the hidden relative phase $\arg J$.  If one
keeps only the population cone, the singular endpoint projection even admits
the spurious zero-cost history $x=y=P=Q=0$ while $\Phi$ changes.  The smallest
closed local quotient is $(x,y,\arg J,\Phi)$; globally, the nonsingular complex
invariants $C=g_2\bar g_1^2$ and $J$ are preferable.  This explains precisely
why the next lower certificate must retain the full four-dimensional HJB
reachability rather than append another pointwise scalar inequality.

## The exact analytical characterization: an exposure HJB equation

The missing joint-sector information can be retained with the
Hamilton--Jacobi--Bellman (HJB) method developed by Fromonteil, Tricarico,
Cesa, and Pichler for this exact perfect-blockade system.

Parameterize each effective TLS by

$$
\psi_{r,k}=\cos(\theta_k/2)e^{i(\phi_{g,k}-\phi_k)},
\qquad
\psi_{g,k}=\sin(\theta_k/2)e^{i\phi_{g,k}},
\tag{33}
$$

and retain the four gauge-invariant coordinates

$$
x=(\theta_1,\theta_2,\phi,\Phi),
\qquad
\phi=\phi_2-\phi_1,
\qquad
\Phi=\phi_{g,2}-2\phi_{g,1}.
\tag{34}
$$

The identity and CZ endpoints are

$$
x_0=(\pi,\pi,0,0),
\qquad
x_{\rm CZ}=(\pi,\pi,0,\pi).
\tag{35}
$$

At a pole the longitude $\phi$ is undefined, so these expressions represent
equivalence classes rather than ordinary isolated coordinate points.  A fully
rigorous proof must use compatible charts, nonsingular amplitudes, or the
corresponding quotient target set.

Use dimensionless time $s=\Omega_{\max}t$.  The running exposure cost is

$$
L(\theta_1,\theta_2)
=\frac14\left[
2\cos^2(\theta_1/2)+\cos^2(\theta_2/2)
\right].
\tag{36}
$$

For any differentiable function $V(x)$, define

$$
\begin{aligned}
\mathcal A(\nabla V)={}&
iV_{\theta_1}
+\left(\cot\theta_1-\sqrt2e^{i\phi}\cot\theta_2\right)V_\phi\\
&+\sqrt2ie^{i\phi}V_{\theta_2}
+\left[
\cot(\theta_1/2)
-\frac{e^{i\phi}}{\sqrt2}\cot(\theta_2/2)
\right]V_\Phi.
\end{aligned}
\tag{37}
$$

Let $V_*(x)$ be the minimum dimensionless exposure needed to reach the
identity target set from $x$.  Dynamic programming gives

$$
0=\min_{0\leq\rho\leq1,\,\xi}
\left\{L+\rho f_\xi(x)\cdot\nabla V_*\right\},
\tag{38}
$$

where $\rho=|\Omega|/\Omega_{\max}$ and $\xi$ is the laser phase.  Minimizing
analytically over the phase and amplitude yields the stationary exposure HJB
equation

$$
\boxed{
L(\theta_1,\theta_2)=|\mathcal A(\nabla V_*)|,
\qquad V_*|_{x_0}=0.
}
\tag{39}
$$

The dimensionful version is
$L=\Omega_{\max}|\mathcal A(\nabla T_R^*)|$.  Equation (39) differs from
Fromonteil et al.'s time-optimal equation only by replacing the running cost
$1$ with the exposure cost $L$.

In the viscosity sense, the value function is the global optimum, so formally

$$
C_*=V_*(x_{\rm CZ}).
\tag{40}
$$

This is an exact analytical characterization, not yet an evaluation of the
number on the right.

## The verification theorem needed for a tight proof

Equation (39) supplies a clean way to prove a candidate value without trusting
an optimizer.

Suppose one constructs a globally defined, locally Lipschitz function $W$ on
the physical state space such that, almost everywhere,

$$
|\mathcal A(\nabla W)|\leq L.
\tag{41}
$$

Along every admissible trajectory,

$$
\left|\frac{dW}{ds}\right|
\leq |\mathcal A(\nabla W)|
\leq L.
$$

Therefore

$$
\boxed{
\Omega_{\max}T_R=\int L\,ds
\geq|W(x_{\rm CZ})-W(x_0)|.
}
\tag{42}
$$

Such a $W$ is an HJB **subsolution** or **calibration**.  If an exact feasible
CZ trajectory also satisfies equality in Equation (41) along its entire path
and has cost equal to the endpoint difference, Equation (42) proves both the
lower bound and attainability.  This is the analytical certificate that the
unknown tight optimum currently lacks.

Because HJB value functions develop shocks, a tight certificate need not be
globally $C^1$.  A viscosity subsolution, or a collection of smooth pieces
with correctly matched interfaces, is the natural object.

## A newly available way to generate the certificate

Naceur and Balada Gaggioli's 2026 differential-moment hierarchy turns the
global HJB inequality into semidefinite programs.  Unlike GRAPE, which
searches for one feasible trajectory and therefore supplies an upper
candidate, a moment relaxation contains every admissible trajectory in a
larger convex set.  Minimizing exposure over that larger set supplies a lower
bound.  Increasing the relaxation degree adds consistency conditions and can
tighten that bound monotonically.

This framework is directly applicable because the JAN22 equations already
have an exact commutative polynomial representation.  Write

$$
g_k=a_k+ib_k,
\qquad r_k=c_k+id_k,
\qquad u=\frac{\Omega}{\Omega_{\max}}=u_x+iu_y,
\qquad \kappa_k=\frac{\sqrt{k}}2.
\tag{43}
$$

In dimensionless time $s=\Omega_{\max}t$, Equation (2) becomes the real
polynomial system

$$
\begin{aligned}
a_k'&=\kappa_k(u_xd_k+u_yc_k),
&b_k'&=\kappa_k(-u_xc_k+u_yd_k),\\
c_k'&=\kappa_k(u_xb_k-u_ya_k),
&d_k'&=-\kappa_k(u_xa_k+u_yb_k),
\end{aligned}
\tag{44}
$$

with

$$
u_x^2+u_y^2\leq1,
\qquad
a_k^2+b_k^2+c_k^2+d_k^2=1.
\tag{45}
$$

There is no Hamiltonian approximation in this rewriting.  The initial point
is

$$
(a_1,b_1,c_1,d_1,a_2,b_2,c_2,d_2)
=(1,0,0,0,1,0,0,0),
\tag{46}
$$

and the exact CZ target is the algebraic set

$$
\begin{gathered}
c_1=d_1=c_2=d_2=0,\\
a_2+a_1^2-b_1^2=0,
\qquad b_2+2a_1b_1=0.
\end{gathered}
\tag{47}
$$

The running polynomial is

$$
L=\frac{2(c_1^2+d_1^2)+c_2^2+d_2^2}{4}.
\tag{48}
$$

### What the fixed-horizon SDP would prove

For a fixed dimensionless horizon $S=T\Omega_{\max}$, introduce an
occupation-moment functional $L_y$, initial and terminal functionals
$L_{y_0},L_{y_1}$, and impose the weak dynamics

$$
L_y\!\left(\partial_\tau v+S\nabla v\cdot f\right)
=L_{y_1}(v)-L_{y_0}(v)
\tag{49}
$$

for every test polynomial allowed at relaxation degree $d$.  Moment and
localizing matrices impose Equations (45), the control disk, the fixed initial
point, and the target support in Equation (47).  Crucially, each target
equality must be imposed after multiplication by **every** legal terminal
test monomial; imposing only its mean would admit false terminal points.

The relaxed objective is

$$
C_{S,d}=\min_y S L_y(L).
\tag{50}
$$

Every real JAN22 pulse induces feasible moments with exactly the same cost.
Consequently, in exact arithmetic,

$$
\boxed{
C_{S,d}\leq C_{S,d+1}\leq C_S^*,
}
\tag{51}
$$

where $C_S^*$ is the true minimum exposure among exact CZ pulses of duration
$S$.  Thus a value such as $C_{30,d}=2.94$ would be a genuine global lower
bound at JAN22's reported horizon, not another pulse search.

The same construction can optimize over stopping times
$0\leq S\leq S_{\max}$.  Set $S=\alpha S_{\max}$ with
$0\leq\alpha\leq1$, replace the vector field by
$\alpha S_{\max}f$, and use the bulk objective

$$
S_{\max}L_y(\alpha L).
\tag{52}
$$

This certifies all durations only **up to** $S_{\max}$.  Stability of a
numerical answer as $S_{\max}$ is increased is evidence, not a proof, that no
still longer pulse has lower exposure.  This is important because JAN22
checked $S=30$, not $S\to\infty$.

### The dual is the analytical proof

The dual SDP searches for a polynomial HJB subsolution plus sums-of-squares
multipliers for the state and control constraints.  In a duration-independent
form, its central identity is a machine-checkable version of

$$
L(x)-\nabla W(x)\cdot f(x,u)\geq0
\quad\text{for every physical $x$ and every $u_x^2+u_y^2\leq1$}.
\tag{53}
$$

Together with a certified endpoint gap, integration gives Equation (42).
This is still analytical in the important sense: the final proof is an
explicit polynomial identity and positive-semidefinite Gram matrices, and it
can be checked independently of the optimizer that discovered them.

The public implementation accompanying the paper provides the needed
moment, localizing, boundary, and weak-dynamics machinery.  Its most relevant
examples are the commutative real-state chain files.  Three additions are
needed for JAN22: the eight-amplitude vector field in Equation (44), the
terminal ideal in Equation (47), and the bulk objective in Equation (50) or
(52).

There are also two reasons not to announce a tight number immediately:

1. Dense moment matrices grow combinatorially.  With eight state amplitudes,
   two controls, and normalized time, even a degree-three dense relaxation
   has hundreds of rows before localizers.  Exact symmetry reduction is
   likely necessary for the degree at which a near-tight certificate appears.
2. The paper's code records floating-point primal residuals, but does not
   reconstruct the dual polynomial or exact Gram matrices.  The paper itself
   lists rationalization as future work.  A solver printout near any proposed
   lower edge must therefore be converted over $\mathbb Q(\sqrt2)$, or
   enclosed with rigorous interval arithmetic, before it becomes a theorem.

### A compact interior state reduction

The following invariants expose the four-dimensional physical state space and
may make a higher-degree stationary certificate tractable:

$$
x=|r_1|^2,
\quad y=|r_2|^2,
\quad C=g_2\overline{g_1}^{\,2},
\quad J=\overline{g_1}r_1g_2\overline{r_2}.
\tag{54}
$$

The six real coordinates
$(x,y,\Re C,\Im C,\Re J,\Im J)$ obey the two exact polynomial relations

$$
|C|^2=(1-y)(1-x)^2,
\qquad
|J|^2=x(1-x)y(1-y).
\tag{55}
$$

They send identity and CZ to the nonsingular algebraic points

$$
(0,0,1,0,0,0)
\quad\longrightarrow\quad
(0,0,-1,0,0,0).
\tag{56}
$$

On the open stratum $0<x,y<1$, this quotient retains both the nonlinear gate
phase in $C$ and the relative Bloch azimuth in $J$, while automatically
removing two redundant phases.  Its exact HJB Hamiltonian can be written
explicitly.  Put

$$
\alpha=g_1\bar r_1,
\qquad \beta=g_2\bar r_2,
\qquad J=\bar\alpha\beta,
\tag{56a}
$$

and, for a real differentiable
$W(x,y,c,d,j,k)$ with $C=c+id$ and $J=j+ik$, define

$$
\mathcal P=W_c-iW_d,
\qquad \mathcal Q=W_j-iW_k.
\tag{56b}
$$

Direct differentiation gives

$$
\begin{aligned}
x'&=\Im(\bar u\alpha),
&y'&=\sqrt2\Im(\bar u\beta),\\
C'&=-\frac{i}{\sqrt2}u\frac{C\bar\beta}{1-y}
    +i\bar u\frac{C\alpha}{1-x},\\
J'&=\frac i2(2x-1)\bar u\beta
    +\frac i{\sqrt2}(1-2y)u\bar\alpha.
\end{aligned}
\tag{56c}
$$

All control dependence in $W'$ then collapses to

$$
W'=\Re(\bar uK),
\qquad K=A\alpha+B\beta,
\tag{56d}
$$

where

$$
\begin{aligned}
A={}&-iW_x+\frac{i\mathcal PC}{1-x}
-\frac i{\sqrt2}(1-2y)\bar{\mathcal Q},\\
B={}&-i\sqrt2W_y
+\frac i{\sqrt2}\frac{\bar{\mathcal P}\bar C}{1-y}
+\frac i2(2x-1)\mathcal Q.
\end{aligned}
\tag{56e}
$$

Consequently the exact interior subsolution inequality is

$$
\boxed{|K|\leq L=\frac{2x+y}{4},}
\tag{56f}
$$

with the invariant polynomial identity

$$
|K|^2=x(1-x)|A|^2+y(1-y)|B|^2
+2\Re(A\bar B\bar J).
\tag{56g}
$$

The verifier `verification/jan22_cz_exposure_hjb_reduction.py` compares
Equations (56c)--(56g) with the original amplitudes and both control
quadratures at 1,000 random states; the largest discrepancy is below
$2\times10^{-14}$.

The denominators in Equation (56c) are removable in the original amplitude
expressions, but the algebraic quotient is **stratified**, not one global
coordinate chart.  For example, when $y=1$ both $C$ and $J$ vanish, while the
phase of $\bar r_2g_1r_1$ can still affect the outgoing vector field.  An SOS
inequality obtained after multiplying by $(1-x)^2(1-y)^2$ is equivalent on
the dense interior only when accompanied by a continuity argument in the
original amplitudes; the cleared polynomial alone says nothing on a face
where that multiplier vanishes.

### Why $(\Re z,\Im z,x,y)$ is not the missing global chart

It is tempting to append the two populations to the complex companion overlap
and call the result four-dimensional.  That projection loses a continuous
phase on an interior surface.  Write

$$
z=e^{-i\gamma}(A_0+B_0e^{i\delta}),
\quad
A_0=(1-x)\sqrt{1-y},
\quad
B_0=\sqrt{2x(1-x)y},
\tag{56h}
$$

where $\gamma=\arg C$ is the gate phase and $\delta=\arg J$.  At

$$
z=0,
\qquad
y=\frac{1-x}{1+x},
\qquad
0<x<1,
\qquad
\delta=\pi,
\tag{56i}
$$

one has $A_0=B_0$, and **every** value of $\gamma$ maps to the same
$(\Re z,\Im z,x,y)=(0,0,x,y)$.  Those states have different gate phases and
different outgoing HJB characteristics.  A function $W(z,x,y)$ must maximize
its Hamiltonian over this hidden circle, so it satisfies an artificially
stronger inequality than a function on the true quotient.  This explains why
adding populations to the companion overlap did not solve the calibration
problem.

The smallest regular local chart remains $(x,y,\gamma,\delta)$.  A global
proof needs an atlas: the angular chart on its regular stratum and polynomial
invariants such as $C$, $\bar r_2g_1r_1$, and
$g_2r_1^2\bar r_2^{\,2}$ on cancellation and pole strata.  This is a more
specific requirement than merely “increase the SOS degree.”

### What the full HJB/SOS calibration attempts established

Several hierarchies were implemented as certificate-discovery calculations:

- a dense stationary amplitude SOS at cubic $W$ returned about $2.1301$;
- symmetry-reduced tensor SOS orders two and three returned about $1.6240$
  and $2.1119$;
- a degree-nine sampled Chebyshev calibration in
  $(\Re z,\Im z,x,y)$ reached about $2.6164$ on its finite pool;
- the next dense tensor and polynomial levels exhausted available memory.

None of these numbers is a theorem.  The first two are weaker than the
analytical exact-fiber bound.  The $2.6164$ value was checked only on sampled
states and uses the collapsed projection in Equation (56i); it has neither a
global SOS identity nor an interval enclosure.  Reporting it as a lower bound
would repeat the same logical error as reporting a GRAPE pulse as one.

These calculations do narrow the remaining design: a single low-degree smooth
polynomial is the wrong object.  A plausible tight certificate is a
shock-matched piecewise rational/viscosity calibration on the invariant atlas,
with each patch verified globally by SOS or interval arithmetic.  Constructing
and exactifying those patches remains an open research computation.

The conclusion of the web audit is therefore sharper than “use GRAPE more
carefully”: differential moments can generate the missing global certificate,
and their HJB/SOS dual can turn it into a checkable analytical proof.  No
published computation has yet carried out this JAN22 instance or established
its unrestricted-duration optimum.  The certified upper pulse above also
rules out the historical value $2.947$.

## The Petrosyan-like progress map that remains to be found

The HJB equation is invariant under translations of the gate phase $\Phi$.
This suggests looking for a corrected progress coordinate on the universal
cover,

$$
W=a\Phi+w(\theta_1,\theta_2,\phi).
\tag{57}
$$

If $w$ takes the same value at the two endpoints, then Equation (42) gives
$C_*\geq a\pi$.  If the present upper witness were optimal, a matching
calibration would require approximately

$$
a=\frac{2.935887}{\pi}\simeq0.934522
$$

and a corrector $w$ satisfying the global inequality

$$
\begin{aligned}
\Big|{}&iw_{\theta_1}
+\sqrt2ie^{i\phi}w_{\theta_2}
+(\cot\theta_1-\sqrt2e^{i\phi}\cot\theta_2)w_\phi\\
&+a\left[
\cot(\theta_1/2)
-\frac{e^{i\phi}}{\sqrt2}\cot(\theta_2/2)
\right]\Big|
\leq L.
\end{aligned}
\tag{58}
$$

The naive choice $w=0$ cannot work.  For example, take
$\theta_1=\pi-\epsilon$ and $\theta_2=\pi$.  Then

$$
L=\frac{\epsilon^2}{8}+O(\epsilon^4),
\qquad
|\mathcal A(a\,d\Phi)|
=\frac{|a|\epsilon}{2}+O(\epsilon^3).
$$

No nonzero $a$ can make a term linear in $\epsilon$ lie below a quadratic
cost in a whole neighbourhood.  The corrector is not optional.

Physical trajectories leaving the ground point have the synchronized
short-time form

$$
\pi-\theta_2=\sqrt2(\pi-\theta_1)+O(s^3),
\qquad
\phi=O(s^3).
\tag{59}
$$

On that thin reachable direction, the two linear terms in the square brackets
of Equation (58) cancel.  A successful $w$ must encode this cancellation
globally while also handling loop closure and HJB shocks.  Simple overlap,
phase-speed, or chord bounds miss the cancellation and produce
$\sqrt{p_k}$ rather than $p_k$; those bounds become useless for long, weakly
excited protocols.

Equation (58) is the closest direct analogue of Petrosyan's
cost-per-progress minimization for the JAN22 CZ problem.  Solving this
Hamilton--Jacobi corrector problem, and proving saturation on an exact CZ
trajectory, is the unresolved analytical step.

### How to generate the missing calibration

The source audit suggests a concrete research sequence:

1. Replace the time-optimal characteristic Hamiltonian by
   $F(x,p)=|\mathcal A(p)|-L(x)=0$ and derive its characteristic equations.
   Since neither $F$ nor $L$ depends on $\Phi$, the conjugate momentum
   $p_\Phi=a$ is conserved.  This gives a mathematical reason—not merely an
   ansatz—for the coefficient $a$ in Equation (57).
2. Integrate those characteristics only as a **conjecture generator** to find
   the extremal, its conserved $a$, and its shock surfaces.  This replaces a
   hundreds-of-pixels GRAPE search by a three-parameter shooting problem, but
   is not yet the proof.
3. On each region separated by shocks, integrate the characteristic one-form
   to obtain pieces $W_j=a\Phi+w_j$.  Match the pieces continuously using the
   minimum-cost selection rule.
4. Prove $|\mathcal A(\nabla W_j)|\leq L$ globally—ideally by factoring
   $L^2-|\mathcal A(\nabla W_j)|^2$ into nonnegative terms in nonsingular
   amplitude coordinates.  This step removes all reliance on the numerical
   characteristic search.
5. Supply an exact closing trajectory on which equality holds.  Its endpoint
   gap then proves the same lower and upper bound.

This route can produce a genuinely analytical theorem even if numerical
characteristics are used to discover its form: the final certificate consists
only of explicit functions, a global inequality, and an exact saturating
trajectory.

## What would complete the proof

A tight theorem for $C_*$ still requires all four of the following:

1. **Determine the optimal candidate.**  The exact upper certificate proves
   attainability below $2.935887$, not that this pulse is globally optimal.
2. **Construct the value function or calibration.**  Solve Equation (39), or
   exhibit a subsolution of Equation (41) with the desired endpoint gap.
3. **Prove the inequality globally.**  Checking Equation (41) only along the
   candidate pulse proves stationarity, not global optimality.
4. **Match both edges.**  Supply an exact pulse, or a controlled sequence of
   exact pulses, whose exposure equals or converges to the calibrated lower
   value.  The interval-certified pulse completes this step only if its cost
   matches the future calibration.

Fromonteil et al. numerically integrate HJB characteristics for the
**time-optimal** CZ problem and recover $T\Omega_{\max}=7.611$.  Their method is
the right global framework, but they do not solve the exposure-weighted
Equation (39).  JAN22's PMP equations likewise give necessary conditions for
an extremal pulse, not a global lower bound.

A rigorous computer-assisted route is possible: construct a polynomial or
piecewise-rational subsolution in nonsingular amplitude coordinates and verify
Equation (41) with interval arithmetic.  That would be stronger than GRAPE
because it would certify all admissible controls, but it would still be a
computer-assisted proof rather than the requested closed-form derivation.

The honest conclusion is therefore:

$$
\boxed{
2.48007<C_*<2.935887,
\qquad\text{the remaining gap is not yet closed.}
}
$$

The lower edge is an analytical variational theorem with an interval-certified
decimal enclosure; its defining constant is
$C_{\rm fib}=2.480079367706997\ldots$.  The upper edge is a rigorous
interval-existence theorem.  In particular, $2.947$ is not merely unproved—it
is impossible as the lower bound.  The exact HJB verification condition
identifies what a future tight lower proof must additionally satisfy.

## Sources

- S. Jandura and G. Pupillo,
  [*Time-Optimal Two- and Three-Qubit Gates for Rydberg Atoms*](https://doi.org/10.22331/q-2022-05-13-712),
  especially the ideal-blockade CZ reduction and the section “Minimizing the
  Decay of the Rydberg State.”
- G. Doultsinos, A. Delakouras, and D. Petrosyan,
  [*Fundamental error bound for entanglement generation between interacting
  Rydberg atoms*](https://arxiv.org/abs/2512.13379), especially the
  min-entropy/coarea cost-per-progress proof.
- C. Fromonteil, R. Tricarico, F. Cesa, and H. Pichler,
  [*Hamilton-Jacobi-Bellman equations for Rydberg-blockade
  processes*](https://arxiv.org/abs/2402.12956), especially their two-TLS gate
  coordinates and Eq. (16).
- F. A. Astolfi, S. Jandura, and G. Pupillo,
  [*Pontryagin Maximum Principle for Rydberg-blockaded state-to-state
  transfers: A semi-analytic approach*](https://arxiv.org/abs/2512.13549),
  for the later semianalytical characterization of time-optimal extremals.
- Y. Naceur and L. Balada Gaggioli,
  [*Reachability and optimal-time certificates for quantum
  control*](https://arxiv.org/abs/2606.24645), for controlled differential
  moment hierarchies, exact reductions, and SDP reachability certificates;
  see also their
  [public implementation](https://github.com/nininaceur/ReachabilityQuantumControl).
- J.-B. Lasserre, D. Henrion, C. Prieur, and E. Trélat,
  [*Nonlinear optimal control via occupation measures and LMI
  relaxations*](https://doi.org/10.1137/070685051), for the commutative
  occupation-measure/HJB-SOS foundation of the proposed exposure
  certificate.
- M. Burr, J. D. Hauenstein, and K. Lee,
  [*Certified Surface Approximations Using the Interval Krawczyk
  Test*](https://arxiv.org/abs/2602.07718), for the interval Krawczyk
  existence-and-uniqueness test used by the upper certificate.
- S. Jandura and G. Pupillo,
  [JAN22 public pulse archive](https://doi.org/10.6084/m9.figshare.19658427),
  whose manifest distinguishes the published time-optimal CZ pulse from the
  published minimum-exposure $C_2Z$ pulse.
