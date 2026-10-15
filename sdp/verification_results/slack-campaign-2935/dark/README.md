# Exact dark-population extension toward 2.935

Accepted extension endpoint: **146564386761/50000000000 = 2.931287735220**.
Independent exact acceptance passed 3,751,680 coefficient inequalities,
243,421 Gram-budget checks, 4,284 excluded boxes, and three corruption tests.
The unchanged original global source audit and complete original predecessor
chain remain prerequisites; the global source audit was not rerun in this round.

This increases the parent endpoint 2.931287686812 by 0.000000048408 and
the attachment endpoint 2.931287603326 by 0.000000131894. It does **not** reach
2.935: the remaining distance is 0.003712264780. The scope remains all-duration,
drift-free, ideal-blockade CZ, with no duration cap or pulse ansatz.

## New reachability inequality

Write p=|r1|², q=|r2|², c=p/2+q/4 and let C be cumulative exposure.
For the original dynamics and |u|≤1, define

```text
D = g1 r2 - sqrt(2) g2 r1,
D' = i u r1 r2 / 2,
c² - 2|D'|² = (2p-q)²/16 + (1-|u|²)pq/2 >= 0.
```

Both CZ endpoints have r1=r2=0, hence D=0. Integrating the norm speed from
either endpoint gives |D|≤min(C,C_T-C)/sqrt(2). Under the contradiction
hypothesis C_T≤B≤H=733/250, this implies

```text
2 |D|² <= min(C,H-C)².
```

Here H is a cap on a hypothetical counterexample's **exposure**, not duration.
The new inequality retains the physical relative phases; the reverse triangle
inequality only supplies a necessary population condition:

```text
|D| >= |sqrt((1-p)q) - sqrt(2(1-q)p)|.
```

The expression inside the absolute value decreases with p and increases with q.
On each closed box [a,b]×[c,d], its positive minimum is at (b,c), or its negative
maximum is at (a,d); if the range includes zero the box cannot be excluded.
For the appropriate signed corner put A=(1-p)q, B=2(1-q)p and
G=A+B-R²/2. Exclusion requires the appropriate strict sign of A-B, G>0,
and G²>4AB. These are exact rational comparisons. Equality is retained.
For a whole cost interval [C_left,C_right], use
R=min(C_right,H-C_left), an upper bound on min(C,H-C) throughout it.

## Why this gain can be added

The 32 profile replacements do not intersect parent-owned intervals 176–191.
On every retained population box, the checker reconstructs the old regional
Gram projection polynomial N and verifies every Bernstein coefficient of
N-d(C)c is nonnegative. It checks the original projection IDs and Gram budgets;
it does not reoptimize or change these weights. Discarded boxes are handled by
the exact reachability argument above. Only the difference from the inherited
profile integral is credited, namely

```text
Delta = sum_intervals (C_right-C_left) sum_k(d_new[k]-d_old[k])/15.
```

Delta is approximately 5.059399806848049e-8. Every selected cost interval lies
inside the already proved mandatory prefix. The interface contribution is not
changed or counted again. For the parent's endpoint polynomial P and endpoint
B_old, the new degree-13 endpoint polynomial is

```text
P_new(t) = P((B-L)/(B_old-L) t) + Delta - (B-B_old),  L=2.9305.
```

The checker verifies the identity at 14 distinct rational nodes and strict
positivity of all 14 Bernstein coefficients, covering the whole terminal-cost
interval, not just its right endpoint.

## Reproduction

Requires Python and `python-flint==0.8.0`. BUNDLE is the extracted original user
attachment, already verified according to its `reproduce.sh` instructions.
The parent certificate and scripts must remain one directory above this one.

```bash
python verification_results/slack-campaign-2935/dark/verify.py \
  --bundle "$BUNDLE" --self-test
```

This first runs the parent's exact acceptance and ten corruption tests, then
independently checks the dark extension, including overlapping intervals,
inflated profiles, and incorrect cost-prefix data. Exact boundary tests use a
box with limiting radius 2/7 and radii on both sides separated by 1e-30.
Successful output is written to `independent.json`.

Optional endpoint reconstruction (not acceptance):

```bash
python verification_results/slack-campaign-2935/dark/compose.py --bundle "$BUNDLE"
```

The discovery producer used separated univariate population transforms. This
checker instead constructs the signed multivariate power tensor from the pinned
projection records and directly checks coefficient inequalities; it imports no
new producer or optimizer. Discovery metadata in `profiles.json` is not trusted
as evidence: all credited integrals and geometric exclusions are reconstructed.
