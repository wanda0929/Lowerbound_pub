# Reachability-restricted exposure lower bound

This extension is accepted only with a successful independent `verify.py`
report and its predecessor proof chain. The numerical endpoint is read from
`RESULT.json`; a producer result alone is not a certificate.

## Scope and inherited identity

The model is the all-duration, drift-free, ideal-blockade stationary-torus CZ
problem. In unit active time the complex dynamics are

    g1'=-i*u*r1/2,       r1'=-i*conj(u)*g1/2,
    g2'=-i*u*r2/sqrt(2), r2'=-i*conj(u)*g2/sqrt(2),

with |u|=1 and |g_j|^2+|r_j|^2=1. Define p_j=|r_j|^2 and cumulative exposure

    C(s)=integral_0^s c(p(t)) dt,     c=p1/2+p2/4.

Both populations are zero at the initial and exact CZ terminal states. The
source equations and model qualification are also described in
`verification_results/direct-o8-endpoint-exact/README.md` and
`docs/mathematical-soundness.md`.

The unchanged global source certificate, raw SHA256

    1f715c99684ed7dbbf1036f168eadac54043e0a235e0f9f273451f875db4bf52

has L=5861/2000, U=2935887/1000000, and cost knots
0,1/36,1/3,2/3,35/36,1. For an exact trajectory ending in the fifth cell its
identity is

    C_T-L = S_occ + S_interface + q(36*C_T/U-35).

All slack terms are nonnegative. The complete predecessor chain establishes
B0=2.931286076089. It includes the global source audit, degree-seven projected
occupation inequalities, polynomial profiles, joint crossing inequalities,
regional allocations, and the noncircular mandatory-prefix extension. This new
extension does not alter the source matrices, potential, or bound_target.

The original native global audit is an inherited mathematical dependency;
checking its hash does not reprove it. `reproduce.sh --full-source-audit` can
rerun it. The default reproducer replays all predecessor extension verifiers.

## 1. A duration-free population barrier

The equations imply, almost everywhere,

    |p1'| <= sqrt(p1*(1-p1)),
    |p2'| <= sqrt(2*p2*(1-p2)).

Let n=8 and define exact rational-coefficient polynomials

    a_k = binom(2*k,k)/4^k,
    S_n(p) = sum_(k=0)^n a_k p^k,
    h_n(p) = sum_(k=0)^n [3*a_k/(2*k+3)] p^k,
    G_n(p) = p^(3/2)*h_n(p)/3.

Then G_n'(p)=sqrt(p)*S_n(p)/2. The independent verifier reconstructs the a_k
using a_(k+1)=a_k*(2*k+1)/(2*k+2), and verifies by exact polynomial arithmetic
that every coefficient of

    1-(1-p)*S_8(p)^2

is nonnegative. Thus S_8(p)*sqrt(1-p)<=1 on [0,1]. All h_8 coefficients are
positive, so G_8 is nonnegative and nondecreasing.

Set

    W(p1,p2)=G_8(p1)+G_8(p2)/(2*sqrt(2)).

The chain rule gives

    |W'| <= (p1/2)*S_8(p1)*sqrt(1-p1)
            +(p2/4)*S_8(p2)*sqrt(1-p2)
          <= c(p).

G_8 is continuously differentiable on [0,1], so this also applies through zero
population, using absolutely continuous trajectories. Since W=0 at both
endpoints,

    W(p1(s),p2(s)) <= min(C(s), C_T-C(s)).               (1)

No positive lower bound on c, phase bandwidth, time cap, or existence of a
minimizing pulse is assumed.

## 2. Exact exclusion of unreachable rectangles

Fix a rational counterexample cap H with B0<H<U. We seek a final endpoint B<=H.
Suppose, for contradiction, a physical exact-CZ trajectory has C_T<=B. It also
has C_T>=B0 by the predecessor, and therefore traverses every cost interval used
below. Its entire trajectory satisfies (1) with C_T replaced on the right by H.

For a physical cumulative-cost interval [A,D], all its relevant populations
satisfy W<=R, where

    R=min(D,H-A).

On a population rectangle [x/n,(x+1)/n] times [y/n,(y+1)/n], monotonicity implies
that the whole rectangle is impossible if its lower corner has W>R. Define

    E(p)=p^3*h_8(p)^2,
    a=8*E(x/n), b=E(y/n), T=72*R^2.

The exact test is

    a+b>T, or [a+b<=T and (T-a-b)^2<4*a*b].             (2)

This is equivalent to sqrt(a)+sqrt(b)>sqrt(T), hence to W>R at the lower corner.
All arithmetic in (2) is rational. Equality is never discarded. In particular,
the zero-cost origin is always retained. Keeping the cross term in (2) is
stronger than merely testing a+b>T.

The verifier enumerates the complete n by n grid. Every rectangle is either
excluded by (2) or retained for a rigorous polynomial inequality. There is no
sampling assertion and no unverified hole in the cover.

## 3. Reuse validated projections on the smaller physical support

The pinned regional certificate has 320 intervals and, on each regional
interval, separate rational allocations for sixteen population rectangles.
Each allocation satisfies the budget sum<=1 for each original Gram. Every
projection used belongs to the set actually checked by the pinned predecessor.
For each such region these establish

    sigma(xi,x,u) >= N_I(xi,p1,p2)
                  =sum_m w_m beta_m(xi) f_m(p1,p2),
    f_m=(1-p1)^g p1^r (1-p2)^h p2^s.

The new grid refines the inherited sixteen rectangles. Its children use exactly
their parent's allocation; no new matrix claim or change of dual potential is
made. The independent verifier nevertheless rechecks all used projection IDs,
nonnegative rational weights, and per-Gram budgets. Since only a pointwise slack
estimate changes, no extra derivative or interface term is introduced.

On a retained rectangle, and normalized cost t in [0,1], the new certificate
specifies a degree-fourteen profile

    d_I(t)=sum_(k=0)^14 delta_Ik B_k^14(t).

The verifier reconstructs signed powers of all population factors and original
projection polynomials. Direct exact affine maps produce their degree-(14,7,7)
Bernstein tensor. Every coefficient of

    N_I - d_I(t)*(p1/2+p2/4)

must be nonnegative on each retained rectangle. This proves the inequality
throughout the reachable population set, including zero-cost boundary points.
The producer uses factorwise degree elevation rather than this power-tensor
reconstruction. The new verifier does not import the new producer.

Unchanged intervals inherit their previous profiles exactly. An accepted changed
interval must have a strictly larger integral, although its new profile need not
be pointwise above the old one. Both profiles independently lower-bound the
same occupation slack on the relevant physical support.

## 4. Integrate without a duration error

Within original cell j with width w_j and local xi,

    dxi/ds = c/(U*w_j).

For xi in [a,b], let [A,D] be the corresponding physical cost interval. The chain
rule applied to a primitive of d_I gives

    integral_I sigma ds >= (D-A)*integral_0^1 d_I(t)dt
                         = (D-A)*sum_k delta_Ik/15.

This identity is valid with zero-cost stalls; there is no division by c in the
accepted inequality and no additive error proportional to elapsed time.

The new profiles replace the regional prefix integral on the same 320 disjoint
intervals. Let Delta>0 be the exact difference of new and old prefix integrals.
The already certified disjoint tail penalty, all interface terms, and terminal
polynomial are unchanged. Consequently the full slack lower bound increases
by Delta, not by old and new penalties added together.

## 5. Conditional sublevel gives an unconditional lower bound

The predecessor tail certificate supplies fourteen Bernstein coefficients for
its exact terminal-exclusion polynomial P0(t), associated with B0. Define

    rho=(B-L)/(B0-L),
    P_new(t)=P0(rho*t)+Delta-(B-B0).

The new verifier checks this identity at fourteen distinct exact rational
nodes. Both sides have degree at most thirteen, so these checks establish the
whole polynomial identity. All fourteen new Bernstein coefficients must be
strictly positive. Positivity is obtained from those coefficients, not from the
values at interpolation nodes.

For a hypothetical pulse with C_T<=B<=H, the reachability-restricted integration
is applicable and the original slack identity then implies

    B-L >= C_T-L >= [old guaranteed slack]+Delta+q(36*C_T/U-35)
                 > B-L,

a contradiction. Hence every exact finite-duration CZ pulse has C_T>B and its
infimum obeys C*>=B. The trial cap H is a cost sublevel for the contradiction,
not a restriction on the theorem or a duration cap. Pulses with C_T>H already
satisfy the conclusion. No attainment assumption is used.
