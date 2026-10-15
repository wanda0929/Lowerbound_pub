# Reachability at mandatory cost crossings and final composition

Read `PROOF.md` for the population barrier and occupation refinement. This note
completes the proof of the final endpoint

    C* >= 1465643801663/500000000000 = 2.931287603326.

The predecessor present in the repository before this computation was
2.931286076089. Thus the improvement made in this round is exactly
0.000001527237. The occupation-only reachability result is 2.931287271171.
The strict upper witness 2.935875225844105 is unchanged, leaving a gap below
0.004587622518105. These are small improvements; 2.932 and 2.935 are not proved.

## Pinned interface inequality

The earlier, independently checked crossing certificate has raw SHA256

    98560cc0bd55714dfb74814e377caac64cb4c736652e33868925da7b25703fd7.

It directly proves Q-D>=0 for each selected original Gram and reconstructs the
native state monomials. Consequently at crossing j its slack satisfies

    S_j >= N_j(p1,p2),
    N_j = sum_(r in allocations_j) weight_r * gamma_r
          * (1-p1)^g p1^r (1-p2)^h p2^s.

The new work changes neither the matrices D nor these allocations. This pinned
inequality is a dependency, replayed in the predecessor verification workflow.

## Smaller physical domain at the crossings

The four crossing costs are C_j=U*knots[j+1], with j=0,1,2,3. Every candidate
with total cost below the new bound crosses all four because the previous
lower bound exceeds C_3. Under the contradiction hypothesis C_T<=B<=H=2.932,
the barrier proved in `PROOF.md` gives

    W(p1,p2) <= min(C_j,H-C_j).

For each j the full population square is partitioned into 16 by 16 rectangles.
Rectangles are discarded only by the strict, exact rational lower-corner test
in `PROOF.md`. On every retained rectangle the independent checker expands N_j
in signed powers and transforms it to bivariate degree-seven Bernstein form.
Every coefficient must be at least the proposed kappa_j. This establishes
S_j>=kappa_j throughout the physical crossing support. Equality cases of the
barrier remain in the checked cover.

The producer uses separately implemented factorwise Bernstein conversions.
The checker does not trust point samples, floating feasibility tolerances, or
unchecked subtraction of diagonal contributions from source matrices.

The four improved crossing lower bounds sum to the previous interface penalty
plus the exact positive increment

    11415691460675126277210319157097193357716454771
    / 32883343360000000000000000000000000000000000000000000.

Its decimal display is approximately 3.47157262438265836e-7. The check covers
39,360 exact coefficients on retained rectangles, and excludes 409 rectangles.
At the two middle crossings no rectangle is excluded; their modest improvement
comes solely from finer Bernstein subdivision. The reachability and refinement
effects should not be conflated.

## Combine disjoint improvements, not repeated penalties

Let B_occ=2.931287271171, and let P_occ be its degree-at-most-thirteen endpoint
polynomial, independently checked against the prior tail certificate. If
Delta_int denotes the increment above, define

    rho=(B-L)/(B_occ-L),
    P_final(t)=P_occ(rho*t)+Delta_int-(B-B_occ).

The occupation increment and interface increment concern disjoint measure
families. No old occupation or interface penalty is added again. Both refinements
use the same counterexample cap H, and the final B is checked to satisfy B<=H.

`crossings.py` acceptance checks this identity at fourteen distinct rational
nodes and separately checks strict positivity of all fourteen final Bernstein
coefficients. Hence P_final>0 on [0,1]. The original global slack identity then
contradicts the existence of an exact-CZ pulse with C_T<=B. Taking the infimum
establishes C*>=B without assuming that the infimum is attained.

The final certificate hash is

    5f5edbf79a66e4ee060ae0d069eeaabe772e30f2a6df64f29d626d2c956c0784.

The occupation reachability certificate hash is

    cce6d0af84023f0d8619686d0b94f4f51f515c0b99c68560acfbea6489c144bd.

## Completed computations

- Run 34024199691: occupation producer, independent checker, and 13
  acceptance/self-test cases passed. There are 6,157,440 new exact tensor
  inequalities, 1,137,333 rational Gram-budget checks, and 8,306 excluded boxes
  across the 230 improved occupation intervals.
- Run 34024435352: occupation replay was byte-identical; crossing production,
  separate signed-power acceptance replay, and six test cases passed.
- Run 34024241552: every predecessor extension replayed successfully. The
  original global native audit itself was inherited, not rerun. The default
  reproducer replays the extension chain; --full-source-audit also reruns it.

No source Gram, original potential, bound_target, or pulse model is changed.
There is no duration cap. The cost cap is used only in a contradiction argument;
pulses above it already satisfy the new lower bound.
