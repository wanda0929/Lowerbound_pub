# Combined crossing and polynomial cost-profile lower bound

The exact endpoint and arithmetic are recorded in `RESULT.json` and
`certified/certificate.json`. This proof strengthens the preceding bound

    B0 = 1465612969253/500000000000 = 2.931225938506.

It applies to the same unrestricted finite-duration, ideal-blockade stationary-
torus CZ problem. It neither restricts the pulse parametrization nor assumes
that a minimizing pulse exists. The original global certificate is unchanged.

## 1. Pinned global identity and inherited dependencies

Let L=5861/2000 and U=2935887/1000000. The cumulative-exposure grid is

    0, 1/36, 1/3, 2/3, 35/36, 1.

The exactly audited original certificate proves, for a physical trajectory
terminating in the fifth cell,

    C-L = S_occupation + S_interface + q(36*C/U-35).       (1)

The original Gram terms are nonnegative. The final-cell terminal polynomial q
has degree at most thirteen: its possible degree-fourteen coefficient cancels
exactly. The source-to-trajectory argument is the one in
`docs/domain-splitting.md` and `verification_results/trajectory-slack/PROOF.md`.

Original source SHA-256:

    1f715c99684ed7dbbf1036f168eadac54043e0a235e0f9f273451f875db4bf52

Original successful full audit SHA-256:

    001885fa84d5f1819992a8a041e94066eda40f4f6a2fbaaf8b81c8b8bb0f7b53

The preceding interface theorem gives C>=P0=2.930957146313 and
kappa0=1107565238703/10^18. The degree-seven and population-refinement proofs
supply an occupation penalty K0 and the endpoint B0. Their raw certificate hashes
are respectively

    3e2fbd42d779da00e1800ee2c5ae62e51c240f7b245c67139b12864576ba18bb
    3932489adf01c5f6ca596663c1624c4ed71bae396d2922d2df2f2beeca882c14

These are explicit proof dependencies, not assertions established merely by
checking hashes. `reproduce.sh` replays the preceding extension verifiers before
checking the new ones. Its optional `--full-source-audit` also reruns the native
original exact audit; otherwise the original full audit is inherited unchanged.

## 2. Stronger mandatory crossings from simultaneous matrix inequalities

For each interface j and selected original Gram block Q_jb, the new certificate
specifies a nonnegative diagonal matrix D_jb. Its entries are rational products
of the recorded weights and scalar coefficients. The verifier checks

    Q_jb - D_jb >= 0                                     (2)

on the original active coordinates by rigorous 384-bit Arb LDL. Every omitted
row must be exactly zero in the original source. A successful strict LDL check
on the active submatrix, together with these exact zero rows, proves (2) for the
complete matrix.

Thus z* Q_jb z >= sum_i D_jb[i,i] |z_i|^2. Multiple selected coordinates of the
same Gram are checked together in (2); their separate scalar lower bounds are
not naively added. The scalar-budget condition sum(weights)<=1 is replaced by
the direct matrix condition. Each distinct original Gram contributes only once.

Each selected z_i is an actual state monomial in the hash-bound native basis.
Its squared magnitude is exactly

    (1-p1)^g p1^r (1-p2)^h p2^s,
    p1=|r1|^2, p2=|r2|^2, 0<=p1,p2<=1.                 (3)

This uses the two exact state-normalization identities. Reflection phases have
unit magnitude and do not affect (3). All exponents are read from the original
basis, not inferred from labels. The new proof uses population factors through
total degree seven, including the constant and higher-order factors.

Summing (2)-(3) produces a polynomial N_j(p1,p2). On each of four rectangles
covering the population square, the verifier expands N_j in powers and converts
it explicitly to bivariate degree-seven Bernstein form. Every coefficient is
at least the claimed rational kappa_j. Hence

    S_j >= kappa_j on the entire interface state space.  (4)

Every potential counterexample has C>=P0>35*U/36, so it crosses all four internal
cost interfaces. Their crossing measures have mass one, and (4) gives

    S_interface >= kappa1 = sum_j kappa_j.               (5)

This penalty replaces kappa0. The original Gram matrices and the global
certificate's bound_target field are not modified.

The producer discovers D with linear programming and eigenvector cuts. Its
floating eigensystems, objective values and feasibility tolerances have no role
in acceptance: the independent checker reconstructs and checks (2) directly
from the original source and checks all population coefficients exactly.

## 3. Keep cost dependence instead of taking a worst-case interval constant

The pinned degree-seven occupation certificate has already verified projection
polynomials beta_m(xi), population factors f_m(p1,p2), and rational allocation
weights w_m on 320 disjoint cost intervals. For each original occupation Gram,
the weights of its projections sum to at most one. Therefore its pointwise
inequality is

    sigma(xi,x,u) >= sum_m w_m beta_m(xi) f_m(p1,p2).     (6)

Here sigma is the original occupation-slack integrand, not the physical running
cost. The earlier proof replaced each beta_m by an interval minimum. The new
proof retains its complete polynomial, using the same allocations and original
matrix projections. The degree-seven base verifier previously checked every
record occurring in these allocations, including those with old scalar rate zero.

On a cost interval I=[a,b], put t=(xi-a)/(b-a). Let

    N_I(t,p1,p2) = sum_m w_m beta_m(a+(b-a)*t) f_m(p1,p2).

The new certificate specifies a degree-fourteen polynomial

    d_I(t) = sum_{k=0}^{14} delta_Ik B_k^14(t).

The independent checker proves

    N_I(t,p1,p2) - d_I(t)*(p1/2+p2/4) >= 0               (7)

throughout [0,1] times the whole population square. It does so by checking every
coefficient of the degree-(14,7,7) Bernstein representation on each of sixteen
population rectangles. The rectangles cover the entire square, including its
zero-cost corner. No division by the physical running cost is required in the
accepted inequalities.

For construction, the coefficient delta_Ik is bounded using the relevant ratios
of population coefficients. Coefficients whose cost denominator is zero are
checked separately. In verification, the checker does not use these ratios:
it expands the original projection polynomials in powers, applies exact rational
tensor affine transformations, and checks (7) coefficient by coefficient.

The producer uses de Casteljau subdivisions and degree elevation; the independent
checker uses direct power expansion and matrix transformations. Neither uses an
optimization solver or floating arithmetic in this cost-profile stage.

## 4. Exact integration over a guaranteed exposure prefix

Write c(x)=p1/2+p2/4. In cell j of width w_j,

    dxi/ds = c(x(s))/(U*w_j).

Every admissible pulse has exposure at least P0, so it traverses the same prefix
as the pinned occupation certificate: all of the first four cells and the fifth
cell prefix ending at P0. On I=[a,b], inequalities (6)-(7) give

    integral_I sigma ds
      >= U*w_j*(b-a) * integral_0^1 d_I(t) dt
      = U*w_j*(b-a) * (sum_k delta_Ik)/15.               (8)

The last equality is exact, since every Bernstein basis polynomial of degree
fourteen integrates to 1/15. Summing (8) gives the exact rational K1 stored in
the cost-profile certificate, and S_occupation>=K1. A certificate may retain an
inherited constant for an interval when that is stronger; the verifier checks
that constant against the pinned refinement. The retained successful candidate
uses a polynomial on all 320 intervals.

This is integration in accumulated exposure, not numerical quadrature in time.
The accumulated exposure is absolutely continuous and nondecreasing. Applying
the chain rule to a primitive of d_I justifies the change of variable even with
zero-cost stalls. Stalls contribute zero. All unused occupation terms and the
trajectory after the guaranteed prefix remain nonnegative and are discarded.
There is no additive error proportional to duration.

## 5. Combine disjoint terms and exclude the terminal interval

Equations (1), (5), and (8) imply

    C-L >= K1 + kappa1 + q(36*C/U-35).                   (9)

K1 and kappa1 concern disjoint measure families and may be used together. The
new proof does NOT add K0 to K1 or kappa0 to kappa1. Nor does it simply add the
two separate increases in their reported endpoints.

The preceding refinement supplies the fully verified degree-thirteen polynomial

    P0(t)=K0+kappa0+q(36*[L+(B0-L)*t]/U-35)-(B0-L).

For a proposed rational endpoint B define rho=(B-L)/(B0-L). The exact identity

    P_B(t)=P0(rho*t)+(K1-K0)+(kappa1-kappa0)-(B-B0)       (10)

expresses the new exclusion polynomial. The retained combined certificate gives
fourteen strictly positive rational Bernstein coefficients for P_B. Its checker
evaluates both sides of (10) at fourteen distinct rational nodes. Since both
sides have degree at most thirteen, those equalities prove the complete
polynomial identity. Positivity follows from the positive coefficients, not
from sampling values at those nodes.

If an admissible trajectory had C<=B, the preceding theorem would imply
C>=B0>P0>L and C<U, so it must terminate in the fifth cell. Equations (9)-(10)
would give

    B-L >= C-L >= K1+kappa1+q(36*C/U-35) > B-L,

which is impossible. Every admissible finite-duration pulse therefore has C>B;
taking the infimum proves C*>=B without assuming attainment.

## 6. Scope of numerical work and verification

All accepted quantities are exact rationals, except original-source matrix
comparisons in Q(sqrt(2)), which use rigorous interval enclosures. LP and
floating eigensystems occur only in crossing-certificate discovery; the
verifiers do not import an optimization solver. The polynomial cost-profile
stage and combined endpoint checker use exact rational arithmetic throughout.
The full source audit, native basis construction, and earlier projection proof
remain explicit dependencies. A PASS report without those dependencies is not
a standalone proof of the physical lower bound.
