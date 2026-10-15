# Regional allocations and a longer mandatory exposure prefix

## Result

The computer-assisted extension proves

\[
 C^\star\ge 2931286076089/10^{12}=2.931286076089.
\]

The preceding certified bound was 2.931272845583, so the exact increase is
0.000013230506. The inherited strict constructive upper endpoint is unchanged,
2.935875225844105; the bracket width is less than 0.004589149755105.
The scope is the all-duration ideal-blockade stationary-torus CZ model.
There is no pulse parametrization, elapsed-time cap, or attainment assumption.

The stages are regional allocation (2.931285651554) followed by a disjoint
mandatory-prefix extension (2.931286076089). Every bound is a rational number,
not a rounded optimizer objective. Successful certificates and reports are
retained under `certified/`; the large original source certificate remains a
separate, unchanged dependency.

## 1. Dependencies and the unchanged source identity

Use L=5861/2000 and U=2935887/1000000. The source cost knots are
0,1/36,1/3,2/3,35/36,1. For an exact CZ trajectory ending in the last cost cell,
the original audited identity gives

\[
 C-L=S_{\rm occ}+S_{\rm int}+q(36C/U-35).
\]

All slack terms are nonnegative. The preceding joint-slack certificate supplies
an interface penalty kappa and an occupation penalty K_old. It proves
B_old=2.931272845583. Its raw certificate hash is
`7d6e5c4c085331d7bf64a49fa2039910aaf4f34ac2e2c04c1e1c25bd87fdcc84`.

The original source hash is
`1f715c99684ed7dbbf1036f168eadac54043e0a235e0f9f273451f875db4bf52`.
The degree-seven projection certificate hash is
`3e2fbd42d779da00e1800ee2c5ae62e51c240f7b245c67139b12864576ba18bb`.
The preceding polynomial-profile certificate hash is
`8952644ae8aff9d692ea7cb25a462de507f29f85af02b1578e063d0eba86a7f7`.

The full original exact audit is inherited. Checking a hash is not a replacement
for that audit. The reproducer first replays the complete predecessor extension
chain; `--full-source-audit` also reruns the original native exact audit.

## 2. A valid allocation can depend on the population region

Put p1=|r1|^2 and p2=|r2|^2. State normalization gives
|g1|^2=1-p1 and |g2|^2=1-p2, and the running cost is c=p1/2+p2/4.

For an original occupation Gram block b, the previously verified Schur
projections establish, for each allowed projection m in that block,

\[
 \sigma_b(\xi,x,u)\ge \beta_m(\xi)f_m(p_1,p_2),\qquad
 f_m=(1-p_1)^{g_m}p_1^{r_m}(1-p_2)^{h_m}p_2^{s_m}.
\]

Each right-hand side is nonnegative on the source cell. The original matrices
and their polynomial projections are unchanged. Only projection IDs already
checked by the degree-seven predecessor verifier may be used.

For each accumulated-cost interval I and population rectangle R choose exact
rational weights lambda_(I,R,m)>=0, subject to

\[
 \sum_{m\text{ belonging to }b}\lambda_{I,R,m}\le1
 \quad\text{for every original block }b.
\]

It follows pointwise that

\[
 \sigma(\xi,x,u)\ge N_{I,R}(\xi,p_1,p_2)
 :=\sum_m\lambda_{I,R,m}\beta_m(\xi)f_m(p_1,p_2).
\]

The population domain is covered by the sixteen rectangles
[x/4,(x+1)/4] times [y/4,(y+1)/4], 0<=x,y<4. Different rectangles may use
different allocations. This does not double-count a matrix: at a given physical
state one uses the allocation for a rectangle containing that state. Every
allocation separately obeys every Gram budget. Rectangle interiors are disjoint
and their union, including boundaries, is the whole population square.

Nor does this introduce interface derivatives or new dynamical boundary terms.
The original dual potential and Liouville identity are not changed. Only a
pointwise lower estimate of its nonnegative slack is made region-dependent.

## 3. A single cost profile valid on all rectangles

On I=[a,b], set t=(xi-a)/(b-a). The certificate specifies

\[
 d_I(t)=\sum_{k=0}^{14}\delta_{I,k}B_k^{14}(t).
\]

For every rectangle R, the checker proves

\[
 N_{I,R}(a+(b-a)t,p_1,p_2)-d_I(t)(p_1/2+p_2/4)\ge0
\]

throughout [0,1] times R, by checking every coefficient of its exact
Bernstein representation of degree (14,7,7). This is not a sampled positivity
test. The zero-cost corner is covered without dividing by the physical cost
in the accepted inequalities. The same d_I is used for all rectangles, so the
unknown state trajectory and its arbitrary transitions between rectangles do
not affect validity.

The producer discovers weights using linear programming at averaged projection
coefficients. Those weights are floored to rationals, budgets are repaired in
exact arithmetic, and complete polynomial coefficients are constructed. The
optimizer's objective and feasibility tolerances are not acceptance criteria.

The verifier does not import the producer or an optimizer. It independently
expands signed powers, applies exact rational affine transformations, checks
all allocation budgets, and checks all tensor coefficients. It also restricts
used IDs to the exact set checked by the predecessor. There are 319 newly
improved intervals; one interval retains the stronger old certified profile.

## 4. Integrate over the already guaranteed prefix

The 320 intervals cover the first four source cells and the fifth-cell prefix
ending at P0=2.930957146313, which was proved before this extension. In a source
cell of width w_j, dxi/ds=c/(U*w_j). Therefore

\[
 S_{\rm occ}\ge K_{\rm reg}
 =\sum_{I=[a,b]} U w_j(b-a)\frac{1}{15}
                         \sum_{k=0}^{14}\delta_{I,k}.
\]

The equality uses the exact integral of a degree-fourteen Bernstein basis
polynomial, 1/15. The accumulated exposure is absolutely continuous and
nondecreasing. A primitive and the chain rule justify this integration even
when c=0 on intervals: such stalls contribute zero. No numerical quadrature
or elapsed-time residual is used.

K_reg is an exact rational; its approximate value is
0.00030298592776841285, replacing K_old approximately 0.00028960281667319914.
The source identity and unchanged interface penalty then certify
B_reg=2.931285651554 by fourteen strictly positive exact endpoint Bernstein
coefficients. The verifier checks the complete degree-at-most-thirteen
endpoint identity at fourteen distinct rational interpolation nodes. Positivity
comes from the Bernstein coefficients, not values at those nodes.

## 5. A new disjoint prefix, with no circularity

The regional theorem has now independently proved that every admissible
trajectory accumulates at least B_reg. Thus it must also traverse the additional
cost interval [P0,B_reg]. This interval was not counted in K_reg.

The last interval's regional allocations may be reused there: their budgets
are independent of xi, and the original matrix-projection polynomials are valid
on the entire source cell, not just the original integration bin. The new tail
checker nevertheless re-establishes all polynomial inequalities on the new
interval. Its local endpoints are

\[
 a_*=36P_0/U-35,\qquad b_*=36B_{\rm reg}/U-35.
\]

A new degree-fourteen profile d_* is verified on all sixteen population
rectangles. This gives the additional exact rational penalty

\[
 K_{\rm tail}=(B_{\rm reg}-P_0)\int_0^1d_*(t)dt
 \approx 0.0000004437022385740981660751589661.
\]

This is added to K_reg because their accumulated-cost intervals have disjoint
interiors. The older K_old is not added again. Most importantly, the new prefix
ends at the already proved B_reg, not at the final target B. No assumption of
the result being proved enters the integration.

## 6. Final exact endpoint exclusion

For a hypothetical final cost C<=B=2.931286076089, the predecessor theorem puts
it in the fifth cell, and the two certified prefixes imply

\[
 C-L\ge K_{\rm reg}+K_{\rm tail}+\kappa+q(36C/U-35).
\]

The final certificate has fourteen positive rational Bernstein coefficients for

\[
 P(t)=K_{\rm reg}+K_{\rm tail}+\kappa
       +q(36[L+(B-L)t]/U-35)-(B-L),\quad 0\le t\le1.
\]

The checker verifies this polynomial by direct exact interpolation against the
regional endpoint polynomial with the appropriate affine rescaling, and checks
every coefficient is strictly positive. Thus C<=B would imply

\[
 B-L\ge C-L\ge K_{\rm reg}+K_{\rm tail}+\kappa+q(36C/U-35)>B-L,
\]

a contradiction. Every finite-duration admissible trajectory therefore has
C>B; taking the infimum gives C^star>=B without an attainment assumption.

## 7. Verification scope and failed diagnostics

The new regional verification checks 4,899,840 exact tensor inequalities,
3,200,013 exact matrix-budget sums, and 6,232 already verified projection IDs.
The tail adds 15,360 exact tensor inequalities. Each stage checks fourteen exact
endpoint interpolation identities and fourteen positive endpoint coefficients.
Ten mutations of the actual regional certificate are rejected; six tail
mutations include rejection of overlapping or unproved prefix intervals.

A separate cost-compression experiment found pointwise numerical improvements,
but its conservative interval-radius test did not certify a usable improvement
on the tested intervals. It is not part of this result. The local predecessor
replay was initially interrupted by memory pressure when an exploratory process
ran concurrently; this was a resource failure, not a failed mathematical check.
The retained CI replay, when marked successful in RESULT.json, is the completed
predecessor extension replay. The original full audit remains explicitly inherited.
