# 2.935 target: small accepted improvement, target not reached

The retained exact extension proves, subject to the unchanged original global
source audit and pinned predecessor chain,

```text
732821921703/250000000000 = 2.931287686812 <= C* < 2.935875225844105.
```

The user's attachment proved 2.931287603326. This round improves it by
**0.000000083486**, not by an amount close to the requested 2.935 target.
The remaining distance to 2.935 is 0.003712313188. The scope remains
all-duration, drift-free, ideal-blockade stationary-torus CZ; neither a time
cap nor a pulse parameterization has been imposed.

## Acceptance and dependencies

`verify.py` independently reconstructs signed-power tensors from the pinned
old projections, checks complete population covers and exact Gram budgets,
and checks endpoint identities using rational arithmetic. It does not import
an optimizer or the new producer. The new stages cover:

- 16 replacement cost intervals (176–191), each with 64 population regions;
- 983,040 occupation coefficient inequalities and 638,611 Gram-budget checks;
- order-64 population barrier and a 64×64 grid at all four mandatory crossings;
- 615,296 crossing coefficients and 6,770 strictly excluded boxes;
- 14 exact polynomial identities and 14 positive Bernstein coefficients at
  each of the allocation, crossing, and combined endpoints;
- actual-certificate corruption tests for inflated gains/targets/profiles,
  over-budget weights, missing regions/crossings, and a wrong barrier order.

The entire original attachment's default extension replay completed in this
orb; `predecessor-replay.log` ends with its accepted 2.931287603326 endpoint.
That replay verifies the predecessor projections against the repository's
original source matrices. The original **global native source audit itself
was inherited, not rerun**. A hash or this round's PASS does not replace it.
No historical floating result has been promoted to a theorem.

## Reproduce with the original attachment

Extract the user's original ZIP to `BUNDLE`. It supplies the unchanged
`verification_results/{population-refinement,adaptive-slack,...}` modules and
certificates. The repository supplies the original source certificate chunks.

```bash
python3 -m venv /tmp/slack-check-env
/tmp/slack-check-env/bin/pip install python-flint==0.8.0
export PYTHON=/tmp/slack-check-env/bin/python
export BUNDLE=/absolute/path/to/extracted-original-attachment

# Replay the original extension chain first.
bash "$BUNDLE/reproduce.sh" "$PWD"

# Check the supplied new certificate without rerunning discovery.
"$PYTHON" verification_results/slack-campaign-2935/verify.py \
  --bundle "$BUNDLE" --self-test

# Optional: reconstruct the combined endpoint, then check again.
"$PYTHON" verification_results/slack-campaign-2935/compose.py --bundle "$BUNDLE"
"$PYTHON" verification_results/slack-campaign-2935/verify.py \
  --bundle "$BUNDLE" --self-test
```

Only `python-flint==0.8.0` is needed for acceptance. The original attachment is
an explicit external input, not silently downloaded by the checker. The
checker trusts the original checker implementation as code; it pins input
certificate bytes and reconstructs each new mathematical inequality.

## Why the two increments can be combined

Write the inherited identity as

```text
C - L = S_occ + S_interface + q(36 C/U - 35),
L = 2.9305, U = 2.935887.
```

For the 16 selected intervals, new nonnegative rational allocations obey
`sum_{m in original block b} lambda_m <= 1` separately in every region.
The checker establishes `N - d(t)c >= 0` on each full population rectangle
by checking its degree-(14,7,7) Bernstein tensor. Unlike the inherited
reachability profiles, these new replacements are valid on the entire
population square. Their cost intervals are inside the already guaranteed
prefix. Their integrated occupation increment `Delta_occ` is the new profile
integral **minus the inherited reachability profile integral** on those same
intervals; it is approximately 8.237376161887501e-8.

For crossing support, replace the old order-8 positive series by order 64:

```text
a_0 = 1, a_(k+1) = a_k (2k+1)/(2k+2),
S_n(p) = sum a_k p^k,
G_n(p) = p^(3/2) sum [a_k/(2k+3)] p^k.
```

The checker verifies all coefficients of `1-(1-p)S_n(p)^2` are nonnegative.
Since `G_n'=sqrt(p)S_n/2`, the sector population speed bounds imply

```text
W_n = G_n(p1) + G_n(p2)/(2 sqrt(2)),
|dW_n/ds| <= c,
W_n <= min(C(s), C_T-C(s)).
```

Under the contradiction hypothesis `C_T <= B <= H = 2.932`, a crossing at
cost `C_j` has `W_n <= min(C_j,H-C_j)`. Each grid rectangle is either strictly
excluded by an exact rational comparison at its lower corner, or all its
crossing-polynomial Bernstein coefficients are checked. Equality is retained.
All old crossing allocations and matrix inequalities are unchanged.

Let `Delta_int` be the new total crossing gain **minus the gain already present
in the attachment**, not the full new crossing penalty. The occupation and
interface increments concern disjoint terms in the source identity. Thus
`Delta = Delta_occ + Delta_int` is valid without double counting. Against the
attachment's endpoint polynomial `P_old` and bound `B_old`, the new polynomial is

```text
P_B(t) = P_old((B-L)/(B_old-L) * t) + Delta - (B-B_old).
```

Exact identities at 14 distinct rational nodes prove the degree-at-most-13
polynomial identity. Strict positivity comes from its Bernstein coefficients,
not sampled values. This excludes every trajectory with `C_T <= B`; taking the
infimum proves `C* >= B` without requiring an attained minimum. Stalls at zero
cost introduce no time-dependent residual, since the argument integrates
`d(t)c` by a primitive in cumulative exposure.

## What was computed toward 2.935

1. **Crossing grid and barrier.** Orders 16/64 on the original 16×16 grid gave
   no gain over order 8. Order 64 with a 64×64 grid gave 2.931287607999, versus
   2.931287607172 at grid 32. This is diminishing numerical evidence, not a
   proved ceiling.
2. **Reoptimized occupation weights.** Sixteen n=8 HiGHS discovery processes
   reoptimized intervals 176–191 and rationalized/repair-budgeted the weights.
   All sixteen improved. Exact acceptance gave 2.931287682139 before combining
   the independent crossing increment. Discovery took about 3m16s with 16
   workers; no solver tolerance participates in acceptance.
3. **Optimistic projection envelope.** At 80 sampled cost locations and a
   21×21 population grid, allowing each block its individually best projection
   gave a sampled occupation integral about 0.000317855, compared with the
   regional 0.000302986. This is neither a certified ceiling nor a bound:
   minimization and cost integration are sampled. The actual current crossing
   penalty is about 0.0000411578. At C=2.935 the terminal polynomial requires
   total nonterminal slack about 0.00434036; this diagnostic falls short by
   about 0.00398135. `exploratory/projection-headroom.json` retains the data.
4. **Full phase-dependent Gram slack.** All 736 occupation blocks per cell
   were expanded, not just the diagonal projections. An initial exploration
   incorrectly fixed three phases despite having only two charge symmetries;
   it was rejected. Corrected runs keep five real physical coordinates:
   `u=1, g1=cos(t1), r1=sin(t1)e^(ia), g2=cos(t2)e^(ib), r2=sin(t2)e^(ic)`.
   The relative phase `b` must not be removed. At xi=0.2,0.5,0.8 the interior
   cell ratios `sigma/c` can be as small as roughly 0.000100–0.000225. Direct
   blockwise evaluation agrees with the expanded polynomial at all 15 retained
   states to within 5.68e-14 in sigma. These are feasible sampled state values,
   not globally certified minima; some optimizations did not converge.
5. **Proposed shared-control equality.** The cross-sector coherence identity
   is already in the source quotient; adding it again would not strengthen
   this model. See `docs/stationary-torus-strengthening.md`. Adding an
   unweighted constant occupation coordinate also encounters the known
   all-duration zero-cost-face issue. No new SDP was launched for a duplicate
   identity or for an unjustified duration cap.

The retained polynomial data are a compact floating research artifact, not a
proof input. To repeat a corrected full-phase search (zero-based cell):

```bash
"$PYTHON" -m pip install numpy==2.4.6 scipy==1.17.1
OPENBLAS_NUM_THREADS=1 "$PYTHON" \
  verification_results/slack-campaign-2935/exploratory/full_phase.py \
  --cell 2 --xi 0.5 --starts 16 --output /tmp/phase-search.json
```

The archive stores numeric arrays only and is loaded with `allow_pickle=False`.
Columns in `k0`–`k4` are cost power, five antiholomorphic powers, then five
holomorphic powers; `c0`–`c4` are binary64 complex coefficients. The search
also starts at its retained witness, so exact reproduction of the full random
discovery sequence is not claimed. This script is not an acceptance checker.

## Remaining obstacle

These computations do **not** prove that 2.935 is impossible. They do show why
local profile refinements are not currently closing the gap. A substantially
stronger result needs a new globally valid constraint connecting the states
across cumulative-cost slices, or a genuinely stronger/exactifiable dual
potential. Reintroducing a phase already present in the quotient is not such
a constraint. No cloud instance was provisioned, no remote service changed,
and no calculation is left running by this campaign.
