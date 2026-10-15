# Continued search for 2.935: no new accepted lower bound

The accepted bound remains **2.931287686812**, conditional on the unchanged
original global source audit and predecessor chain described in the parent
README. The new computations below are research diagnostics, not proof inputs.
They neither establish 2.935 nor establish that 2.935 is impossible.

## Accounting for a new potential

Use the original source identity, with L = 2.9305 and U = 2.935887:

```text
C - L = S_occ + S_interface + q(36 C/U - 35).
```

At H = 2.935, the unconditional original crossing bound is
0.00004081065985854328 and q(H) is approximately 0.00015963986776048678.
A potential correction spending the original occupation slack therefore needs
boundary gain **0.004299549472381141**. It must not also claim the occupation
increment used to prove 2.931287686812: that would spend the same slack twice.

The threshold at H is only a discovery objective. A proof must also establish
the terminal inequality throughout the remaining terminal-cost interval,
not just at C = H. A 17-point endpoint scan of the coherence candidate had
positive margins, with minimum 0.0002053881478174 at H. A subsequent exact
endpoint-only check converted the stored binary64 coefficients to their exact
rational values and found 14 strictly positive degree-13 Bernstein
coefficients in Q(sqrt(2)), with 17 exact interpolation checks. This proves
that component on the whole interval, but does not repair the failed
occupation inequality or certify the piece-interface matching conditions.

All occupation evaluations retain five physical variables:

```text
u = 1,
g1 = cos(t1), r1 = sin(t1) exp(i a),
g2 = cos(t2) exp(i b), r2 = sin(t2) exp(i c).
```

Only the two genuine charge gauges are fixed. In particular, g2 is not also
made real. Each counterexample retains its source-cell label, including at
interfaces where the two polynomial pieces need not agree.

## Completed diagnostics

1. **Phase reachability.** The necessary disks
   `|Z-1|² <= 8 C²/9` and `|Z+1|² <= 8 (H-C)²/9`, with
   `Z = conjugate(g2) g1² + sqrt(2) conjugate(r2) g1 r1`, did not exclude
   the 15 previously retained small-slack states. They are not enough to
   strengthen the old pointwise-slack calculation materially.
2. **Full interface Grams.** Evaluating all 134 source blocks per crossing
   gave a sampled minimum sum of 0.0000645244361053, versus the old
   unconditional projected bound 0.0000408106598585. These sampled values
   are not certified minima. Population caps were effectively inactive at
   these witnesses; their modest headroom does not close the target gap.
3. **Global phase potential.** A cost-degree-8, Z-degree-6 family with 144
   coefficients finished 60 exchange rounds with gain about 0.000780835
   and a remaining negative normalized residual about -5.9e-8. This run
   also exposed why interface counterexamples must carry their cell labels.
   It did not produce a certificate.
4. **Five continuous phase pieces.** With 720 coefficients and 64 interface
   equalities, 80 rounds ended at sampled gain 0.0012933725186545786 and
   negative residual -0.0020640512785436924. No certificate follows.
5. **Population extension.** Added cost-safe terms based on p1², p1 p2,
   and p2², including their phase products: 1,260 coefficients. The first
   sampled gain was 0.0035207449552752124; counterexample exchange reduced
   it to 0.0029307299849072044 after 18 rounds, with remaining negative
   residual -0.041331619050694574. The last LP took much longer than prior
   rounds but returned normally; the run ended after its soft time budget
   was exceeded (total 1,725.55 seconds). Final checkpoints and run status
   are retained in the experiment archive. This was not convergence.
6. **Coherence extension.** Added eight functions based on
   `W = sqrt(2) conjugate(r2) g1 r1`, such as `Re(W) p1`, `Re(W) p2`,
   and `Re(W²)`. These vanish to at least fourth order in excited
   amplitudes; their time derivatives do not introduce a linear-cost
   singularity at the ground locus. The 1,620-coefficient sampled LP is
   discussed below.

## A sampled candidate crossed the target, but failed validation

The coherence LP with 20,018 inequalities and coefficient box [-0.2, 0.2]
returned gain **0.004504937620198574** and minimum sampled residual
8.634252894688249e-9. Dual simplex reported optimality after 154 seconds;
an earlier interior-point attempt timed out. Neither outcome proves
nonnegativity away from the samples.

Unconstrained adversarial search immediately found residual -7.10562916479.
Its matrix-feature evaluation and separate potential evaluation agreed to
7.11e-15, so this was not an indexing discrepancy. Adding those cuts and
resolving hit a 180-second solver limit; this is not an infeasibility result.

The candidate also fails on the superset defined by the existing population
and phase reachability conditions. A strict-interior witness, after moving
away from the constrained optimizer's numerical boundary, is:

```text
source cell = 0 (zero-based; evaluated from the left)
C  = 0.08155241666666667
t1 = 0.5632002826091821
t2 = 0.6169826355065461
a  = -1.570949077223877
b  = 0.0000036685438048492816
c  = -1.57096168800557

source slack / running cost =   3.2968622191251122
potential derivative / cost = -8.47619431137361
sum                        =  -5.179332092248497
```

Its order-8 population-series prefix margin is 2.3358782e-5. Even the
untruncated arcsine population bound has positive margin 2.3291500e-5.
Both phase-disk margins are positive (about 0.00365715 and 3.42515703).
This is a numerical counterexample to the proposed inequality on that
necessary-condition domain, **not a claim that the state is reachable by an
actual CZ trajectory**. It rules out accepting this candidate with those
conditions alone, not accepting every possible stronger formulation.

## Verification and retained data

- Compared population/coherence time derivatives with exact constant-control
  evolution at 20 asymmetric states: PASS, maximum error 2.0748e-10.
- The new population potential's analytical coordinate gradient and its
  linear feature representation are checked in the discovery script before
  optimization. Numerical differentiation is still not a proof method.
- `endpoint_check.py` passes the exact endpoint-only check just described.
  Its output is explicitly marked as a component of a rejected candidate,
  not a new CZ lower bound.
- Re-ran `verify.py --bundle /tmp/certificate-review/extracted --self-test`:
  PASS at **2.931287686812**, checking 983,040 allocation coefficients,
  615,296 crossing coefficients, 638,611 Gram budgets, and rejecting all
  ten certificate mutations. The original global source audit was inherited,
  not rerun by this continuation.

The companion `2935-continuation-experiments.zip` stores scratch research
scripts, solver reports, candidate coefficients, labeled samples, and
counterexamples. Its `/tmp/cz-*` layout is intentional: these are retained
experiment snapshots, not a new portable proof package. They use the
original extracted attachment at `/tmp/certificate-review/extracted`, the
repository's `full-phase-polynomials.npz`, and NumPy/SciPy/python-flint.
The initial unconstrained experiments have known rejected assumptions noted
above; do not treat their standalone optimistic summaries as accepted bounds.

The existing proof ZIP remains the only accepted extension produced by this
campaign. No paid compute was provisioned, no remote repository was changed,
and no calculation from this continuation remains running.
