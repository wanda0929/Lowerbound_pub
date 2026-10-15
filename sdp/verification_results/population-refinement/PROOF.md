# Certified exposure lower bound: degree seven and population subdivision

## Result and scope

The supplemental certificate proves

\[
C^\star\ge B=\frac{1465612969253}{500000000000}=2.931225938506.
\]

The preceding certified bound was 2.931201368260. The exact increase is
0.000024570246. The inherited strict upper endpoint 2.935875225844105 is
unchanged; the certified bracket width is strictly less than 0.004649287338105.
The model is the all-duration ideal-blockade stationary-torus CZ problem.
No pulse parametrization, time cap, or existence of a minimizing pulse is assumed.

This is a layered computer-assisted proof, not a relabeling of the original
certificate's bound_target. Its dependencies are explicit below.

## 1. Original exact certificate and interface theorem

Let L=5861/2000 and U=2935887/1000000. The cost grid is
0,1/36,1/3,2/3,35/36,1. The unchanged original source certificate has raw SHA-256

```
1f715c99684ed7dbbf1036f168eadac54043e0a235e0f9f273451f875db4bf52
```

Its full native audit verifies 18,739 exact coefficient identities and every
Gram's positive semidefiniteness. The successful audit bytes have SHA-256

```
001885fa84d5f1819992a8a041e94066eda40f4f6a2fbaaf8b81c8b8bb0f7b53
```

This source-to-trajectory identity, explained in docs/domain-splitting.md and
verification_results/trajectory-slack/PROOF.md, reads

\[
C-L=S_{\rm occ}+S_{\rm int}+q(36C/U-35)
\]

for a trajectory terminating in the fifth cell. Every term is nonnegative.
The prior interface proof supplies

\[
S_{\rm int}\ge\kappa=1107565238703/10^{18},
\quad C\ge P_0=2.930957146313.
\]

The earlier source audit is inherited unchanged; no claim is made that the
small subdivision verifier alone rechecks that global certificate.

## 2. Degree-seven trajectory certificate

The method in verification_results/trajectory-slack/PROOF.md is now applied to
population factors of total degree up to seven. Its original matrices are not
modified. Rigorous Schur-complement inequalities give, for selected source
Gram blocks, lower bounds of the form

\[
\beta_m(\xi)(1-p_1)^{g_m}p_1^{r_m}(1-p_2)^{h_m}p_2^{s_m},
\quad p_i=|r_i|^2,\quad r_m+s_m\ge1.
\]

For each cost interval I the certificate fixes rational nonnegative allocation
weights lambda_m, whose sum for any one original Gram is at most one, and
rational b_m with beta_m(xi)>=b_m throughout I. Consequently

\[
\sigma(\xi,x,u)\ge N_I(p_1,p_2)
:=\sum_m\lambda_m b_m(1-p_1)^{g_m}p_1^{r_m}
                  (1-p_2)^{h_m}p_2^{s_m}.
\tag{1}
\]

The degree-seven base certificate and independent audit bind these claims to
the original source and native physical basis. Verification completed in run
34008303741 at commit d502415308b29884bf2a6cb215729bdbce226659. It checked 6,494
used projections from 3,171 distinct source Grams, 12,975 selected coordinates,
192,852 exact allocation-budget inequalities and 20,480 population coefficient
inequalities over 320 disjoint cost intervals. Matrix comparisons use rigorous
384-bit Arb enclosures; all polynomial and budget checks use exact rationals.

The base certificate raw SHA-256 is

```
3e2fbd42d779da00e1800ee2c5ae62e51c240f7b245c67139b12864576ba18bb
```

It proves B_base=2.931224886868. Its cost intervals cover the whole first four
cells and the guaranteed prefix of the fifth cell ending at P_0.

## 3. Subdivide the population square, not the control trajectory

The new extension leaves every projection, allocation, and b_m in (1) unchanged.
It partitions [0,1]^2 into 16 closed rectangles with disjoint interiors, using
four equal intervals in each population coordinate. On each rectangle R write

\[
N_I(p_1,p_2)=\sum_{i,j=0}^{7} n_{I,R,i,j}
 B_i^7(t_1)B_j^7(t_2),\qquad (t_1,t_2)\in[0,1]^2.
\]

For R=[a_1,b_1]x[a_2,b_2], the running cost c=p_1/2+p_2/4 has Bernstein
coefficients

\[
d_{R,i,j}=\frac{a_1+(b_1-a_1)i/7}{2}
          +\frac{a_2+(b_2-a_2)j/7}{4}.
\]

Choose delta_I as the minimum n/d over all rectangles and coefficients with
d>0; coefficients with d=0 are checked directly to have n>=0. Then every
coefficient of N_I-delta_I*c is nonnegative on every rectangle, proving

\[
\sigma(\xi,x,u)\ge N_I(p_1,p_2)\ge\delta_I c(x).
\tag{2}
\]

This covers the whole population square, including zero-cost boundary points.
It is not a sampled positivity test or a restriction on admissible states.
The producer obtains n by exact de Casteljau subdivision. The independent
checker expands the population factors in powers and restricts their elevated
Bernstein representation using explicit blossom matrices. It does not import
the producer or solve an optimization problem. All 327,680 local coefficient
inequalities are checked with exact rational arithmetic.

## 4. Integrate only a mandatory cost prefix

Cumulative exposure is absolutely continuous and nondecreasing. On a cell of
width w_j, dxi/dt=c/(U*w_j). Every trajectory has C>=P_0 by the earlier theorem,
so it traverses every integration interval of the base certificate. Therefore

\[
S_{\rm occ}\ge K_{\rm new}:=\sum_{I=[a,b]}\delta_I U w_j(b-a).
\tag{3}
\]

The new K is an exact rational, stored in the supplemental certificate; its
approximate value is 0.0002803019887001075. It REPLACES the base occupation
penalty; it is not added to it. Zero-cost stalls contribute zero to the
integral. There is no elapsed-time residual or duration assumption.

## 5. Exact endpoint exclusion

The degree-seven base certificate supplies a degree-at-most-13 polynomial

\[
P_{\rm base}(t)=\kappa+K_{\rm base}
 +q(36[L+(B_{\rm base}-L)t]/U-35)-(B_{\rm base}-L).
\]

For the new B define rho=(B-L)/(B_base-L). The exact identity

\[
P_{\rm new}(t)=P_{\rm base}(\rho t)
 +(K_{\rm new}-K_{\rm base})-(B-B_{\rm base})
\tag{4}
\]

reconstructs the new terminal exclusion without altering the terminal Gram
matrices. Fourteen strictly positive rational Bernstein coefficients certify
P_new>0 on [0,1]. The independent checker verifies (4) at fourteen distinct
rational nodes; since both sides have degree at most thirteen, this is a
complete polynomial identity proof. Positivity follows from the coefficients,
not from values at those nodes.

A hypothetical exact CZ trajectory with C<=B must also satisfy C>=P_0>L.
Equations (1)-(4) and the original identity imply

\[
B-L\ge C-L\ge\kappa+K_{\rm new}+q(36C/U-35)>B-L,
\]

which is impossible. Thus every admissible finite-duration trajectory has
C>B. Taking the infimum gives C^star>=B without an attainment assumption.

The independent exact subdivision verification passed in run 34008997701 at
commit f932a677ac3a300789ee6e5785763f02fb80795d. New certificate SHA-256:

```
3932489adf01c5f6ca596663c1624c4ed71bae396d2922d2df2f2beeca882c14
```

## 6. What is not certified by this work

The separate full-residual and cost-safe-face probes on a floating dual near
2.933253918843281 are exploratory. Their residual or discount tests do not
provide a stronger valid certificate and are not used in this proof.
The result does not establish 2.935 or equality with the constructive upper bound.
