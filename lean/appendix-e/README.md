# Appendix E formalization (Lean 4.28)

This standalone project contains the concrete control model, SOS hierarchies,
weak-duality proofs, and exposure-coordinate construction for Appendix E.
The modules use the namespace `CZExposure` and retain the `RequestProject`
module prefix from the downloaded formalization. Lean and mathlib are pinned
to 4.28.0; `lake-manifest.json` fixes mathlib at
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

The parent library now also pins Lean 4.28 and imports this project as a local
dependency. Its historical differentiable model is not automatically
interchangeable with this integral model. The new parent certificate contracts
use this model explicitly; see [the integration contract](../CertificateContracts.md).

## Current status: conditional completeness

Conditional completeness means that convergence is proved **assuming
`EuclideanDirectedArcSuperposition`**, not that this last input has been
proved in Lean. Within this scope, the local proof chain is complete.

The tier-two acceptance entry point is now
`RequestProject.AppendixE.ConditionalAcceptance`: it takes the source-shaped
`EuclideanCurrentSuperposition` explicitly and derives directedness rather
than assuming it. See [the acceptance record](ConditionalAcceptance.md) for
the complete external contract, literature correspondence, tier-two versus
tier-three scope, work estimates, and reproducible checks. Run
`lake env lean ConditionalAcceptanceAudit.lean` after `lake build RequestProject`.
The audit rejects every transitive axiom outside Lean's standard allowlist;
it does not assert that the explicit superposition assumption is proved.

The [external mathematical justification](ExternalSuperpositionJustification.md)
derives that interface from AK Theorem 11.1 and PS Proposition 3.8,
Theorem 5.1 and Lemma 4.17, including the measurable parametrization and
bounded-Borel-test conversions. This is a written mathematical argument,
not a Lean proof of the external input. The earlier acceptance record's
literature mapping alone did not establish those conversions.

Local controllability is now proved for this system, rather than supplied:
`LocalSteeringConstruction.physicalLocalSteering` uses actual finite pulse
words, signed-root C¹ curves, and the six-dimensional inverse function theorem.
Its positive radius and fourth-root duration constant are uniform over all
normalized states. They are existential, not numerically evaluated.
Simultaneous C¹ polynomial approximation is now proved by tensor Bernstein
polynomials, mixed-degree derivative convergence, a common approximation
order, and affine transport to the closed box. `BoxC1PolynomialApproximation`
is retained as a proposition describing the unchanged contract, with the
proved inhabitant `PolynomialGeometry.boxC1PolynomialApproximation`.
No main convergence API takes `hApprox` anymore. The matrix Positivstellensatz
is also proved by M1--M5 in `MatrixSOSTheorem.lean`; no main certificate or
convergence API takes `hSOS` anymore.
Earlier module-by-module progress notes below that mention three or four inputs,
conditional approximation, or conditional local steering describe older routes; the current
status and main API sections supersede those historical descriptions.

### Completed implications

- Endpoint repair and exact CZ closure use constructed local steering.
  Equality of the relaxed and physical optimal values requires only the
  superposition input. Successful-pulse existence and finiteness of
  `Cstar` are unconditional (`nonempty_physical_pulse`, `Cstar_finite_physical`).
- Polynomial approximation, symmetry averaging, residual matrix correction,
  and sum-of-squares representation yield finite-degree certificates under
  the superposition input alone. A sum-of-squares certificate represents a polynomial as
  a finite sum of squared polynomials modulo the normalization constraints.
- The concrete real-matrix programs have proved soundness, degree
  monotonicity, stationary embedding without a degree increase, convergence,
  and finite-real epsilon bounds. The shared shift `W_j = -n - V_j`
  preserves the manuscript objective exactly. The redundant scalar interval
  family is absorbed into the interval matrix blocks.
- Tangent alignment with the parent current is proved from the supplied
  decomposition and vector-current identity in `PolarAlignment.lean`.
  Mean-length integrability and pairing integrability are also derived;
  pairing measurability follows from the supplied measurable arc realization.

### Accepted external inputs, not proved here

| Input | What remains assumed |
| --- | --- |
| `EuclideanDirectedArcSuperposition` | Current identification, cycle removal, and existence of measurable directed arcs with the stated mass and endpoint laws. |

This input packages consequences of cited results, not verbatim source
theorems formalized here. `EuclideanCurrentSuperposition` is an alternative
input supplying decomposition and vector-current identities; its implication
to `EuclideanDirectedArcSuperposition` is proved. Constructing the actual
measurable curve-space realization from the cited decomposition remains
external and is not part of the completed local work.

The final conditional APIs do not depend on the legacy axiom
`External.euclideanDirectedArcSuperposition`. Older convenience wrappers
in `ExposureSuperposition.lean` do; their dependency audits expose it.

### Scope and correspondence boundaries

- Fixed-partition upper bounds, convergence, finiteness, and epsilon bounds
  require `∃ γ : Pulse, γ.exposure < U`: a successful pulse strictly below
  the chosen ceiling. Existence of some pulse does not discharge this bound.
- `SplitFeasible` is an abstract polynomial program;
  `ConcretePartitioned.Feasible` specifies the concrete real-matrix cones.
  Equality of their feasible sets is not asserted or needed: the concrete
  program has its own soundness and convergence theorems.
- The manuscript correspondence uses positive orders. At order zero,
  Lean's natural-number subtraction truncates `d - 1` to zero; this is an
  additional convention, not a negative-degree polynomial space.
- Serialized certificate files, basis ordering, exact-number archive
  arithmetic, and numerical objective checks are outside this real-coefficient
  result. Convergence does not assert attainment of the physical infimum.

The sections below describe each module's role and hypotheses. A result
outside one module may be supplied by a later module; the current scope is
the one stated above, not an unfinished-work list for each intermediate step.

## Verified B-field regularity

`RequestProject/AppendixE/BFieldRegularity.lean` proves:

- `Bfield_norm_le_sqrt_cost`: for every normalized state and every control
  with norm at most one, `norm (Bfield (Jmap x) u) ≤ K * sqrt (cost x)`.
  The proof supplies `K = 32`, including at zero cost.
- `continuousOn_Bfield`: joint continuity on
  `Yset × Metric.closedBall (0 : ℂ) 1`, including the collapsed zero-cost face.
- `Bfield_bounded`: a uniform bound on this domain, also with `K = 32`.

The finite-function-space norms are the existing sup norms. Supporting
lemmas prove the directional derivatives of `cost` and `zObs`, their bounds,
and `norm B ≤ 32 * sqrt (sqrt (y 2))` on the image domain.

All three targets were compiled and audited locally. Each has precisely
`[propext, Classical.choice, Quot.sound]` as its axiom dependencies, with no
`sorryAx` or added project axiom. The audit imports the regularity module
without importing the conditional completeness module.

## Compactness of exposure records

`RequestProject/AppendixE/ExposureCompactness.lean` proves that, for every
nonnegative mass budget, the set of finite measures satisfying the original
`IsExposureRecord` balance constraints within that budget is compact in the
weak topology. The proof uses continuity of the balance integrals on the
compact state-control domain and preserves the original constraints through
an explicit subtype pushforward/pullback equivalence.

This compactness input supports the separation argument below.

## Smooth subsolutions below the relaxed value

`ExposureSeparation.lean` reduces infeasibility at a budget below `pRelaxed`
to finitely many smooth balance tests and applies finite-dimensional
Hahn–Banach separation. `RelaxedSubsolution.lean` normalizes the resulting
smooth function using the symmetry under control negation.

The resulting `smooth_subsolution_relaxed` has the same derivative and
endpoint conclusions as Lemma 3, for every real threshold `a < pRelaxed`.
It includes the zero-cost face and depends on none of the existing
generic completeness inputs. The physical-threshold smooth-subsolution theorem in
`Completeness.lean` now follows from checked realization under the
explicit generic ball-box and superposition inputs.

## Control averaging and disintegration

`ControlAveraging.lean` proves that `u ↦ vf x u` and hence `u ↦ B(y, u)`
are `ℝ`-linear in the control on the whole ambient space, including the
zero-cost face where `B = 0`. It packages them as continuous linear maps
`vfControlCLM`/`BfieldControlCLM` and derives the exchange of Bochner
integration and the B-field (`integral_Bfield`, `integral_balance_Bfield`),
plus mean/disk facts for control marginals.

`ExposureDisintegration.lean` disintegrates an exposure record `ν` over its
`Y`-marginal. The conditional kernels `ν.condKernel y` are probability
measures supported on the closed unit disk for `ν.fst`-a.e. `y`
(`exposure_condKernel_disk_support`). Their means are disk-admissible a.e.;
`exposureAdmissibleControl ν` sets the mean to `0` when it lies outside
the disk, giving a single measurable control `ubar : (Fin 11 → ℝ) → ℂ`
with `‖ubar y‖ ≤ 1` everywhere that agrees with the mean `ν.fst`-a.e.

`exists_averaged_exposure_flow` proves that this `ubar` is measurable,
globally disk-valued, has marginal `ν.fst` supported on `Y`, makes the
averaged velocity `y ↦ B(y, ubar y)` integrable, and satisfies the original
balance identity `∫ Dψ(y)(B(y, ubar y)) dν.fst = ψ(yPi) - ψ(y0)` together
with exact mass preservation `ν.fst univ = ν univ`. Extracting an actual
pulse from the averaged flow (path reconstruction) is not part of this
step; the later physical-completeness modules prove it under the explicit
controllability and superposition inputs.

All listed declarations are audited locally to depend only on
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx` and no project
axiom; see `ExposureAveragingAudit.lean`.

## Euclidean flow and vector measure

`VectorMeasureBounds.lean` proves two generic domination lemmas: a vector
measure dominated in `enorm` by a scalar measure `m` on every measurable
set has `variation ≤ m`, and a density-defined vector measure
`μ.withDensityᵥ v` has `variation ≤ μ.withDensity (‖v ·‖ₑ)`. These lemmas
provide upper bounds; `VectorMeasureDensity.lean` later proves equality
for finite measures and integrable Banach-valued densities.

`ExposureCurrent.lean` transports the averaged flow to
`EuclideanSpace ℝ (Fin 11)` along the fixed continuous linear equivalence
`exposureEuclideanEquiv` — the Euclidean geometry is used rather than the
sup norm of `Fin 11 → ℝ`. `EuclideanExposureFlow` bundles a finite state
measure, a measurable disk-valued control, support on the compact image
`euclideanExposureDomain`, velocity integrability, and the balance
identity `∫ Dψ(z)(eB(z, u(z))) = ψ(z_pi) - ψ(z_0)`.
`exists_euclidean_exposure_flow` constructs one from any exposure record,
with the scalar measure equal to `Measure.map exposureEuclideanEquiv ν.fst`
and `stateMeasure univ = ν univ`: the scalar exposure mass is unchanged.

Inside `EuclideanExposureFlow`, `vectorMeasure` is
`stateMeasure.withDensityᵥ velocity`, `massBound` is
`stateMeasure.withDensity (‖velocity ·‖ₑ)`, and `action` evaluates a
one-form by integration. This module proves `variation ≤ massBound`;
`ExposurePolarCurrent.lean` later proves equality. It also proves
`variation univ < ⊤`, `variation` vanishes off the
compact domain, and `boundary ψ = ψ(z_pi) - ψ(z_0)` for compactly supported
smooth `ψ` — a weak source–sink boundary. The action is additive on
integrable one-forms, scalar-homogeneous, and operator-norm bounded.
Total vector variation equals `∫‖v‖`; it remains a separate quantity
from the original scalar exposure mass and is not asserted equal to the
exposure budget.

`exposureTimeWeight z = (‖v z‖ₑ)⁻¹` is the inverse Euclidean speed used by
the later exposure-time reparameterization: it is `∞` at zero speed
(`exposureTimeWeight_eq_top_of_velocity_eq_zero`), which is safe because
the velocity density vanishes there. The weighted inequality
`∫⁻ ‖v‖ₑ⁻¹ d(variation) ≤ stateMeasure univ` (`weighted_variation_le`)
follows from the density domination `variation ≤ massBound` and
`ENNReal.mul_inv_le_one`; it also holds for any measure `m` dominated by
the variation (`weighted_submeasure_le`, `weighted_submeasure_lt_top`),
the situation produced by any mass-decreasing cycle removal.
`exists_component_le_exposure_mass` is conditional on a supplied
probability decomposition, the weighted-mass identity between component
times and the weighted submeasure, and an a.e. good-component property:
it selects a finite, budget-bounded good component. It does not construct
a decomposition or prove that components obey the ODE.

`exists_exposure_current` packages these facts. This constructs the vector
measure and its density-defined action. A formal identification with the
current framework used by Paolini–Stepanov, cycle removal, and path
extraction are still outstanding.

## Measure decompositions of the current mass

`ExposureDecomposition.lean` proves the measure-theoretic consequences of the
raw identities a geometric arc decomposition would supply. In the published
argument (Paolini–Stepanov, <https://arxiv.org/abs/1303.5664>), Prop. 3.8
gives the acyclic part (the existence of the cycle removal itself remains
external here), Def. 4.4 eq. (4.4) gives the endpoint pushforwards, Lemma
4.17 eq. (4.14) gives the localized equality of the mass measure on Borel
sets, and Thm. 5.1 assembles the decomposition. None of those results is
formalized; `LocalizedMeasureDecomposition` is only the localization identity
`m s = ∫⁻ component a s dη`, and `ExposureMeasureDecomposition` is the
measure data expected after such a decomposition and endpoint
identification — not a claim that the components are curves or solve ODEs.

From these raw identities the file derives: the ensemble is a probability
measure (`isProbabilityMeasure_ensemble`), a.e. component has the declared
source and sink (`ae_endpoints`), the unbounded inverse-speed weight satisfies
the exact average identity `∫⁻ componentTime dη = ∫⁻ ‖v‖ₑ⁻¹ d(mass)`
(`average_componentTime`) and hence the exposure-mass bound
(`average_componentTime_le`), a.e. component measure is supported on the
exposure domain and sees nonzero velocity (`ae_component_domain`,
`ae_component_velocity_ne_zero`), and `exists_component_le_exposure_mass`
selects a good component with the correct endpoints, a.e. domain/velocity
properties, and finite budget-bounded time. The domain and velocity
properties hold almost everywhere for the component MEASURES; full-path
support and dynamics are supplied by the arc and clock modules below.
Existence of the geometric decomposition remains external; tangent alignment
from its vector-current identity is proved in `PolarAlignment.lean`.

## Parameterized arcs and the exposure clock

`ExposureArc.lean` defines `EuclideanArc`: a positive finite-length, injective
(unit-speed Lipschitz) parameterization `path : ℝ → ExposureEuclidean` on
`[0, length]` — a genuine curve function with `LipschitzWith 1`, `Set.InjOn`,
and derivative of norm `1` a.e., not independent endpoint labels. Its
`lengthMeasure` is `map path (ds restricted to [0, length])`, and
`lengthMeasure_eq_map_speed` verifies the pushforward agrees with the
parameterized speed-density formula `‖deriv path‖ₑ ds` (no independent
Hausdorff-measure equality is claimed). `mapsTo_of_ae_mem_closed` upgrades
a.e. membership in a closed set to full `[0, length]` path support, endpoints
included.

`ExposureArcRealization` is conditional data tying a decomposition `D` to arc
functions: for a.e. index the component measure equals `arc a`'s length
measure and `initial`/`terminal` equal `path 0`/`path length`.
`exists_arc_le_exposure_mass` then selects a genuine `EuclideanArc` with the
declared source/sink endpoints, full-domain path support, a.e. nonzero
velocity along the parameter interval, and `exposureTime ≤ stateMeasure univ`
with `exposureTime < ⊤`. The `exposureClock` is the real interval integral of
the real inverse speed (which is `0` at zero speed by convention, safe only
under finite `exposureTime`); it is absolutely continuous on `[0, length]`
with `clock 0 = 0` and `clock length = exposureTime.toReal`. `IsDirectedBy`
is the tangent-alignment interface, discharged from a supplied current
identity by `PolarAlignment.lean`. Decomposition existence remains external;
finite-duration reconstruction is proved conditionally below. The inverse-clock
reparameterization is constructed in the next module.

## The exposure clock and its inverse

`ExposureClock.lean` first bounds the transported field: `euclideanBfield_bounded`
gives `‖euclideanBfield z u‖ ≤ K` on the compact domain for
`K = ‖exposureEuclideanEquiv‖₊ * C + 1` (the coordinate equivalence is used
through its operator norm, not asserted isometric), and
`EuclideanExposureFlow.velocity_bounded` specialises it to the controlled
velocity. For an arc contained in the domain with finite `exposureTime`, the a.e. lower bound
`K⁻¹ ≤ inverseSpeed` on the parameter interval yields the quantitative
increment inequality `(b - a)/K ≤ clock b - clock a`
(`exposureClock_increment_lower_bound`), hence `StrictMonoOn` of the clock and
`dist a b ≤ K * dist (clock a) (clock b)`. In particular
`0 < exposureTime.toReal` (`exposureTime_toReal_pos`): a finite-cost arc has
positive exposure duration. The clock's image is exactly
`Icc 0 exposureTime.toReal`, so `clockOrderIso` is an actual order
isomorphism `Icc 0 length ≃o Icc 0 exposureTime.toReal`, `clockInverse` its
inverse on that real interval (not a global inverse), Lipschitz with constant
`K` (`lipschitz_clockInverse`, `exists_lipschitz_clockInverse`). Composing the
path gives `reparameterizedPath : Icc 0 exposureTime.toReal → ExposureEuclidean`,
again `K`-Lipschitz, staying in `euclideanExposureDomain` with
`reparameterizedPath 0 = path 0` and `reparameterizedPath T = path length`.
The exceptional zero-velocity set is absorbed by `exposureTime < ⊤` (it is
null for the parameter measure).

## Clock transport and the conditional a.e. ODE

`ExposureClockTransport.lean` proves the exact pushforward identity
`map clockInverseReal (dt on [0,T]) = (ds on [0,L]).withDensity (weight ∘ path)`
(`clockInverseReal_map_exposureMeasure`) by `Measure.ext_of_Iic` — no
Luzin-type theorem is assumed. This yields the correct-direction a.e.
transfer `clockInverseReal_ae_transfer`, partial-integral finiteness
(`lintegral_exposureTimeWeight_Icc_lt_top`), the local clock value
`exposureClock_eq_toReal_lintegral`, and the `Iic` mass
`weightedParameterMeasure_Iic`. `clockInverseReal` is a clamped (`Set.projIcc`)
extension valid outside `[0,T]` only for measure-theoretic convenience; all
a.e. claims live on the exposure interval. Lebesgue differentiation gives
`HasDerivAt clock inverseSpeed` a.e. (`ae_hasDerivAt_exposureClock`).

`ExposureReparamODE.lean` then proves, by `HasDerivAt.of_local_left_inverse`,
`HasDerivAt clockInverseReal ‖v‖` a.e. on `(0,T)`
(`ae_hasDerivAt_clockInverseReal`), and conditionally on `γ.IsDirectedBy F`
(the tangent identity, still an external input) the a.e. ODE
`d/dt exposurePathReal = euclideanBfield (exposurePathReal t) (exposureControl t)`
on `[0,T]` via the vector chain rule `HasDerivAt.scomp`
(`ae_hasDerivAt_exposurePathReal`). The exceptional-set transfer through the
AC clock and the inverse/chain-rule argument are now proved for the
reparameterized curve. `exists_exposure_time_trajectory` packages this:
given a decomposition, an arc realization, and a.e. tangency, it returns
`T = exposureTime.toReal > 0`, `ENNReal.ofReal T ≤ stateMeasure univ`, and a
Lipschitz `y : ℝ → ExposureEuclidean` with measurable disk-valued `u`,
correct endpoints, full `Icc 0 T` domain support, and the a.e. field
equation. Arc-decomposition existence, normal-current correspondence, and
construction of the measurable arc realization remain external. The later
`PolarAlignment` module derives `IsDirectedBy` from the supplied identities.
`exposureTime` is a weighted cost — not finite physical duration — and the
trajectory is not a `Pulse` and does not establish `Cstar ≤ pRelaxed`.

## Vector-measure subcurrents (PS Def. 3.1)

`VectorSubcurrent.lean` formalizes the vector-measure analogue of
Paolini–Stepanov's subcurrent relation (arXiv:1303.5664): `S ≤ T` means
`M(T - S) + M(S) ≤ M(T)` — "no cancellation" between a subcurrent and its
complement. It proves `‖T s‖ₑ ≤ |T| s` on measurable sets (single-part
partition), the variation triangle inequality `(S+T).variation ≤ |S| + |T|`,
`|0| = 0`, and `T.variation = 0 ↔ T = 0`. The relation `IsVectorSubcurrent`
is reflexive, transitive, and closed under complement (`T - S`), and under
finite total variation `|T| univ < ∞` it yields the localized identity
`|T - S| + |S| = |T|` (Remark 3.5 analogue — finite mass is essential),
domination `|S| ≤ |T|`, support/null inheritance, and antisymmetry. Checked
source facts: Def. 3.1 (exact total-mass condition), Remark 3.2 (equality by
triangle), Remark 3.3 (transitivity), Remark 3.5 (localization); Prop. 3.8
cycle existence is NOT formalized.

`ExposureSubcurrent.lean` applies this to `F.vectorMeasure`: a subcurrent's
variation is dominated by `F`'s variation, inherits compact-domain support,
and satisfies the same inverse-speed budget bounds
(`weighted_subcurrent_le`/`_lt_top`). `ExposureMeasureDecomposition.ofSubcurrent`
supplies decomposition data with `mass_le` PROVED rather than assumed — the
missing mass-domination consequence used after cycle removal. Still open:
constructing a cycle with zero boundary and an acyclic remainder, identifying
vector measures with normal currents, and obtaining an arc decomposition
with the required tangent alignment. No new axioms.

## Exact variation and polar representation

`VectorMeasureDensity.lean` proves
`(μ.withDensityᵥ v).variation = μ.withDensity (fun x => ‖v x‖ₑ)`
for a finite measure and an integrable density in a real Banach space.
The proof first treats simple functions by summing over disjoint fibres,
then passes to the density using L¹ approximation and the variation
triangle inequality.

`ExposurePolarCurrent.lean` applies this identity as
`variation_eq_massBound`. The measurable `polarDirection = ‖v‖⁻¹ • v`
is unit norm almost everywhere for current variation, integrable for
that measure, and reconstructs the original vector measure
(`vectorMeasure_eq_withDensity_polar`). `action_eq_integral_polar`
proves that integrating one-forms against this representation preserves
the original action. The source–sink boundary is preserved as well.

`EuclideanNormalCurrentData` packages the finite vector measure, its
unit polar density, and a finite positive-measure representation of its
distributional boundary. `toNormalCurrentData` constructs these data
from the exposure flow with boundary `δ_target - δ_initial`.
The positive boundary measures are not asserted to be Jordan parts.
Identification with the metric-current framework, cycle removal, arc
decomposition, and its measurable realization remain external. Tangent
alignment from supplied current identities is proved in `PolarAlignment.lean`.
No new axioms are
introduced by the mass identity or this representation.

## Directed-arc superposition and conditional trajectory

`CurrentArcDecomposition.lean` defines the mass and arc data consumed from
geometry: a retained vector subcurrent, its localized measure decomposition,
unit-speed arcs, and measurable endpoint maps with Dirac laws.
`IsDirected` separately states that the arc tangents equal the parent
current's polar direction. The localized domination of the retained mass
is proved from the subcurrent condition using `variation_le`.

`EuclideanDirectedArcSuperposition` quantifies over arbitrary Euclidean
current data with finite mass and boundary, distinct source and sink,
Dirac boundary measures, and compactly supported variation. It supplies
the above data and directedness. Its conclusion contains no exposure
cost, control, physical pulse, or CZ-specific endpoint.

`ExposureSuperposition.lean` opts into one external geometric axiom:
`External.euclideanDirectedArcSuperposition`. This assumes a combined
Euclidean corollary: current representation, cycle removal, curve
decomposition and endpoint laws, measurable arc-length representatives,
and polar/tangent compatibility. It is broader than the literal statement
of Paolini–Stepanov Theorem 5.1. This legacy wrapper assumes the whole package.
The final conditional APIs instead take an explicit hypothesis; the later
`EuclideanCurrentSuperposition.directed` theorem derives tangent alignment
from supplied current identities without using this axiom. Current-theory
identification and decomposition existence remain external in either route.

The source correspondence is Paolini–Stepanov,
<https://arxiv.org/abs/1303.5664>: Proposition 3.8 supplies cycle removal;
Definition 4.4, equations (4.3)/(4.4), gives mass and endpoint identities;
Lemma 4.17, equations (4.14)/(4.15), localizes mass and current identities;
and Theorem 5.1 gives the acyclic arc decomposition. Remark 4.5 identifies
the classical Euclidean counterpart with Smirnov's Theorem C. Remark 5.2
covers Polish spaces without an extra set-theoretic assumption.
No cancellation and strict convexity of the Euclidean norm underlie the
polar-alignment consequence. The original directed-superposition input
includes that consequence; `PolarAlignment` now proves it from the
alternative current-identity input. The measurable parametrization's
existence remains external in both formulations.

`exists_exposure_time_trajectory_of_record_of_superposition` proves the
full record-to-trajectory implication with the geometry schema as an
explicit parameter. Its standard-only axiom list does not discharge that
parameter. The final `exists_exposure_time_trajectory_of_record` uses the
named axiom, which appears in its dependency audit. Given any
`IsExposureRecord ν`, it yields positive finite exposure time
`ofReal T ≤ ν univ`, a Lipschitz path in the state domain with the required
endpoints, measurable disk-valued control, and the field equation almost
everywhere. The exposure bound, selection, and time change are proved
consequences. The later modules prove finite-duration physical-pulse
reconstruction, `Cstar ≤ pRelaxed`, and SOS completeness under the explicit
inputs described in the current-status section.

## Positive-cost lift and the physical clock

`ExposureStateLift.lean` inverts the coordinate lift on the positive-cost
region only: `exposureStateLift y i = y_{i+3} / y 2` with running cost
`euclideanExposureCost z = √(y 2)` (the cost itself, not its square).
Differentiating the local identity `lift ∘ J = id` gives
`D lift (J x) ∘ DJ x = id`, so lifting `y' = B(y,u)` yields
`x' = f_u(x)/c(x)`; inverse claims hold only where `y 2 > 0`.

`PhysicalClock.lean` defines `PositiveExposureSegment`: a retained interval
`[a,b]` storing the path's Lipschitz constant, a disk-valued measurable
control, and a uniform cost cutoff `δ`. The lifted state is proved
Lipschitz on `[a,b]` (local C¹ inverse plus compactness — a.e. ODE alone
would not suffice), obeys `x' = f_u(x)/c(x)` a.e., and the physical clock
`σ(t) = ∫_a^t 1/c` is absolutely continuous and strictly monotone with
`t-s ≤ σ(t)-σ(s) ≤ (t-s)/δ`, so `0 < σ(b) ≤ (b-a)/δ`. The identity
`∫ c·σ' = b-a` is an exposure-parameter accounting step only;
`ofTrajectory` consumes a supplied cutoff interval. The next section
inverts the clock and realizes physical-time dynamics; the
excursion-selection section below constructs the retained intervals.
Endpoint matching and Pulse reconstruction are supplied by the later
conditional repair and assembly modules.
No new axioms; this module does not import `ExposureSuperposition`.

## Physical-time realization of a segment

`PhysicalClockInverse.lean` identifies the physical clock with an order
isomorphism from `[a,b]` to `[0,D]`. Its real inverse `ψ`, extended
constantly outside `[0,D]`, is globally 1-Lipschitz. The forward clock is
differentiable at every point of `[a,b]`; mathlib's null-image theorem
therefore carries the exceptional sets through the time change. The
a.e.-transfer lemma requires no measurability hypothesis on the predicate.

`PhysicalReparam.lean` defines the physical path and control by
`x(s) = liftedState(ψ(s))` and `v(s) = u(ψ(s))`. The inverse-function theorem
gives `ψ' = c(x)` on `(0,D)`, which turns the lifted dynamics into
`x' = vf(x,v)` almost everywhere. Absolute continuity of each Lipschitz
coordinate then gives the integral equation at every time in `[0,D]`,
including the endpoints, and proves velocity-coordinate integrability.
Applying the same fundamental theorem of calculus to `ψ` gives the exact
physical exposure `∫₀^D c(x(s)) ds = ψ(D) − a = b − a`.

`exists_physical_realization` packages finite duration
`0 < D ≤ (b−a)/δ`, a globally Lipschitz path in `Xset` with the retained
segment's endpoints, measurable disk-valued control, integral-form
dynamics, and exact physical exposure. The positive-cutoff interval is
supplied as input; the excursion-selection section below constructs the
retained intervals. The later repair and completeness modules supply steering,
phase repair, the complete `Pulse`, and `Cstar ≤ pRelaxed` under the explicit
controllability and superposition inputs. These local analytic
results use only standard Lean axioms.


## Sharp cost growth and excursion accounting

`CostGrowth.lean` proves the sharp physical cost-derivative bound
`|Dcost_x(vf(x,u))| ≤ √c(x)` on `Xset` for `‖u‖ ≤ 1`. The previous
bound `6√c` in `abs_fderiv_cost_vf_le` remains unchanged; the sharp result
is `abs_fderiv_cost_vf_le_sqrt`.

In exposure time, the squared-cost coordinate `q = c²` satisfies
`|q'| ≤ 2√√q`. At positive cost, its B-field component is
`2·Dcost_x(vf(x,u))`: the factor `c` in `D(c²)` cancels the division by
`c` in the B-field. That component vanishes at zero cost. To control
`H(c) = c·√c`, the proof regularizes its expression in the coordinate
`q`: `g_ε(q) = √(q+ε)·√√(q+ε)`. For `ε > 0` this is `C¹` near each
`q ≥ 0`, with derivative `3/(4√√(q+ε))`. Absolute continuity and the
fundamental theorem of calculus give a uniform `3/2`-Lipschitz bound
for the regularized compositions. Passing `ε ↓ 0` proves
`lipschitzOn_costThreeHalves_exposure`: `H(c(t))` is `3/2`-Lipschitz on
the entire exposure interval `[0,T]`, including zero-cost times.

`ExposureExcursions.lean` bounds the duration of a supplied interval
whose endpoint costs equal `α` and which reaches cost at least `β`,
where `0 ≤ α < β`. Its duration is at least `(4/3)(H(β) − H(α))`.
For pairwise disjoint open intervals inside `[0,T]`, this gives
`N·(4/3)(H(β) − H(α)) ≤ T`. The index type of any such family is finite,
even if finiteness was not assumed. When `α ≤ β/2`, the bound simplifies
to `N·(2/3)·β√β ≤ T`. Separately, `sum_retained_physicalExposure_le`
shows that the exact physical exposures of disjoint retained
`PositiveExposureSegment`s sum to at most `T`.

The interval, peak, and disjointness data are supplied as hypotheses;
the following section constructs these intervals and proves coverage.
The later conditional repair, assembly, and completeness modules supply
steering, phase repair, the complete `Pulse`, and `Cstar ≤ pRelaxed`.
These results add no axioms.

## Constructed finite excursion selection

`CutoffExcursions.lean` constructs cutoff intervals from a continuous
cost function whose endpoint values are at most `α`. For a time above
`α`, the interval endpoints are the last sublevel point before it and
the first sublevel point after it. Compactness supplies these extrema;
the intermediate value theorem gives endpoint cost exactly `α`, and
the interior stays strictly above `α`. Overlapping cutoff intervals
coincide, so distinct intervals have disjoint interiors.

`ExcursionSelection.lean` retains precisely the endpoint pairs whose
intervals reach `β > α`. The count bound proves this set finite. Every
time with cost at least `β` lies in a retained interval; outside their
union the cost is strictly below `β`. For `α > 0`, the construction
produces a `FiniteExcursionSelection` of actual
`PositiveExposureSegment`s sharing the original trajectory and control.
Their physical endpoints have cost `α`, their total physical exposure
is at most `T`, and their total physical duration is at most `T/α`.
The finite enumeration need not be chronological; intervals ordered by
start time are separated. An empty selection is allowed when no interval
reaches `β`.

`ExposureRecordSelection.lean` combines this construction with the
record-to-trajectory theorem. One exposure trajectory works for every
choice `0 < α < β`; the retained pieces stay within the record's mass
budget. The conditional theorem takes the superposition schema
explicitly and uses only standard Lean axioms. Its wrapper invokes
`External.euclideanDirectedArcSuperposition`, with that existing
assumption visible in the axiom audit. No new axiom is introduced.

The discarded low-cost portions are handled by the subsequent progress,
repair, and assembly modules. Physical completeness uses the explicit
controllability and superposition inputs.

## Discarded-gap progress bounds

`ExposureProgress.lean` reads the complex progress observable from the
first two exposure coordinates. Its exposure-time velocity satisfies
`|z'| ≤ 4√c`, including at zero cost, using the existing physical-time
bound `|Dz(vf)| ≤ 4c√c`. Lipschitz regularity and the scalar fundamental
theorem of calculus on the real and imaginary coordinates establish the
complex integral equation.

`DiscardedProgress.lean` proves that any low-cost interval `[a,b]` with
`c ≤ β` changes the progress observable by at most `4√β(b−a)`.
For disjoint such intervals inside `[0,T]`, the sum of the endpoint
changes is at most `4T√β`, independent of their number. For an actual
`FiniteExcursionSelection`, the discarded-time set is compact and lies
where `c < β`; the integral of progress speed over that set has the
same bound. Integrability and the almost-everywhere derivative identity
on the discarded set are proved explicitly.

The estimate `|z| ≥ 1−6c` also ensures `|z| ≥ 1/2` when
`c ≤ β ≤ 1/12`. Consequently, the angular-rate integrand
`Im(z'/z)` has magnitude at most `8√β` there, and its signed integral
over discarded times has magnitude at most `8T√β`. This is a proved
bound on the angular-rate integral. The phase-transport section below
identifies this integral with actual phase increments on supplied
low-cost gaps. The chronological cover is constructed below; repaired
physical blocks are supplied by the later conditional repair modules.
These analytic results use only standard
Lean axioms and introduce no new assumptions.

## Phase transport across low-cost gaps

`PhaseTransport.lean` proves, for a nonvanishing Lipschitz complex path
with its almost-everywhere velocity, that its unit phase satisfies
`z(t)/|z(t)| = exp(i∫ Im(z'/z)) · z(a)/|z(a)|`.
The proof removes the accumulated rotation and uses absolute continuity
to show that the resulting unit phase is constant. It also constructs
an absolutely continuous real phase lift initialized at `arg(z(a))`.
Only this initial value uses the principal argument; the lift remains
valid across branch cuts and multiple turns.

`LowCostPhase.lean` applies the identity where `c ≤ β ≤ 1/12`.
The real phase increment on `[a,b]` is exactly the angular-rate integral,
with magnitude at most `8√β(b−a)`. For a supplied disjoint finite gap
family inside `[0,T]`, the sum of absolute increments is at most
`8T√β`, and the product of endpoint unit-phase ratios is the exponential
of their signed sum. That sum equals the angular-rate integral over
the union of the gaps. The final corollary identifies it with
`discardedAngularIntegral` when the gaps cover the selected discarded
set up to a null set.

The supplied-cover corollary is discharged by the chronological
construction below. These identities concern the observable `z`, whose
phase has the opposite sign to the conditional gate phase.
Phase-preserving endpoint steering, construction of physical face
blocks, terminal phase repair,
the complete `Pulse`, and `Cstar ≤ pRelaxed` are proved in the later
conditional reconstruction modules.
No new axioms are introduced.

## Chronological discarded gaps

`ExcursionGaps.lean` sorts the retained segments by their start times
and constructs the `N+1` gaps before, between, and after them. Their
closed intervals cover `discardedTimes` exactly; their open interiors
are pairwise disjoint and cover it up to a null set. The construction
includes an empty retained selection and zero-length gaps between
touching intervals.

`chronological_gap_phase_accounting` applies the phase-transport theorem
to this constructed family. It proves the signed-sum and
endpoint-product identities for `discardedAngularIntegral`, together
with the `8T√β` absolute-sum and product-error bounds, without a
supplied gap-cover hypothesis. All results use only standard Lean
axioms. The later conditional steering and assembly modules turn these
identities into a physical pulse.

## Endpoint projection and phase alignment

`FaceProjection.lean` constructs the paper's projection
`P(x) = (phase(g₁), 0, phase(g₁)² conj(phase(z)), 0)`, where
`phase(w) = w/|w|`. For `x ∈ X` with `c(x) ≤ 1/12`, it proves
`P(x) ∈ F`, `z(P(x)) = phase(z(x))`, and
`‖P(x) − x‖ ≤ 32√c(x)`. The norm here is the ambient sup norm on
`State`, not the Riemannian distance used in the manuscript's
ball-box argument. The projection fixes `F`, and the results are
applied to both physical endpoints of every retained segment.

For `x ∈ F`, `faceCZTarget` constructs a point of the exact CZ orbit
at ambient distance at most `|z(x)+1|`. If
`z(x) = −exp(iθ)`, this distance is at most `|θ|`.

`SectorPhase.lean` proves that independent constant unit phases in
the two sectors preserve the state manifold, running cost, and
physical dynamics, including their integral form. It constructs
phase factors mapping any supplied face state to any other face
state and proves preservation of each block's endpoint progress
ratio. The normalized-phase ratio is preserved as well.

These results establish endpoint geometry and symmetry only.
The later modules construct steering trajectories, repaired blocks, final
phase repair, the complete `Pulse`, and `Cstar ≤ pRelaxed` using the
explicit geometric inputs. The generic ball-box specialization remains
external, not a consequence of endpoint geometry alone. No new
axioms are introduced.

## Physical segments and cubic steering exposure

`PhysicalSegment.lean` packages a finite-duration physical path with a
measurable disk-valued control, domain membership, velocity integrability,
and the integral equation at every time. The integral equation implies
that its path is Lipschitz on its interval. Existing retained physical
realizations instantiate this structure with exposure exactly `b−a`.

Time reversal uses `x(D−s)` and `−u(D−s)`, swaps the endpoints, and
preserves exposure exactly. Constant unit sector phases also give valid
segments with the same control and exposure. A segment becomes a `Pulse`
when unit-modulus control, the initial state, and exact-CZ closure are
supplied explicitly; this conversion does not prove those hypotheses.

`SteeringExposure.lean` proves that any such segment starting on `F`
satisfies `|r₁(s)| ≤ s/2`, `|r₂(s)| ≤ √2 s/2`, and `c(x(s)) ≤ s²/4`.
Its cumulative exposure is at most `s³/12`, and its total exposure is at
most `D³/12`. Reversal gives the same total bound for a segment ending
on `F`, with running cost at most `(D−s)²/4`.

These are bounds for supplied physical segments. The existence of short
connections is derived in `BallBoxSteering` from the explicit generic
controllability input. The later repair and completeness modules use those
connections; the generic theorem itself remains external.
No new axioms are introduced.

## The step-four Lie-bracket rank condition

`ControlLieAlgebra.lean` uses the actual real vector fields
`X = vf(·,1)` and `Y = vf(·,i)` and mathlib's derivative definition of
the Lie bracket. It computes `Z=[X,Y]`, `X₃=[Y,Z]`, `Y₃=[Z,X]`, and
`Z₄=[X,Y₃]` as linear fields, proves all six fields smooth, and proves
that their values span the kernel of the differential of the two
normalization constraints at every state in `Xset`.

The constraint differential is surjective. Its kernel has dimension
six, and the six displayed bracket fields are linearly independent.
Their prefixes of sizes two, three, five, and six have those
respective ranks. The proof includes states with vanishing ground or
excitation amplitudes; it uses an explicit six-coordinate
parametrization of the kernel rather than division by an amplitude.

This verifies the algebraic step-four bracket-generating prerequisite.
It does not construct a manifold tangent bundle, compare ambient and
Riemannian distances, or prove the generic ball-box theorem. That geometric
specialization is packaged in `CompactRegularLevelBallBox`;
`BallBoxSteering` proves its physical application, and the later modules
complete repair and reconstruction conditionally. No new axioms are introduced.

## Local geometric paths and length comparison

`StateGeometry.lean` identifies `Xset` homeomorphically with the
product of two unit spheres in Euclidean four-space. It keeps the
existing sup norm on `State` and proves the coordinate norm
comparisons used below explicitly.

For `x,y ∈ Xset` with `‖y−x‖∞ ≤ 1/4`, normalizing the straight
chord in each sector constructs a smooth path within `Xset` with
the exact endpoints and Euclidean arc length at most `16 ‖y−x‖∞`.
Each chord has norm at least `1/2`, including when a ground
amplitude vanishes. The length is defined as Euclidean total
variation, with extended nonnegative values. Its infimum over
smooth paths lies between the ambient chord distance and the
stated local upper bound.

For `c(x) ≤ 1/16384`, this gives a geometric path from `x` to its
face projection with length at most `512 √c(x)`. For `x ∈ F`,
`z(x) = −exp(iθ)`, and `|θ| ≤ 1/4`, it gives a path to the exact
CZ target with length at most `16 |θ|`.

These paths establish a local geometric length comparison. They
do not come with physical controls, and the length infimum is not
yet identified with mathlib's manifold Riemannian distance.
`BallBoxSteering` uses these paths with the accepted generic input to
produce short physical connections. Repair and physical completeness then
follow conditionally; no Riemannian-distance identification is claimed here.
No new axioms are introduced.

## Physical concatenation and finite face-block assembly

`PhysicalConcatenation.lean` concatenates supplied physical segments
with matching endpoints. The resulting segment satisfies the integral
equation at every time, has duration and exposure equal to the sums,
and preserves unit-modulus control when both inputs have it. Controls
may jump at the join. Zero durations are allowed; the first segment's
control is used at the join.

`FaceBlockAssembly.lean` packages supplied segments whose two endpoints
lie on `F`. It uses constant sector phases to align a finite list of
these blocks to a prescribed initial face state, preserving each
block's control, duration, exposure, and conditional-phase ratio.
The assembled duration and exposure are exactly the respective sums,
and its endpoint phase ratio is exactly the product of the input
ratios. The empty list uses a zero-duration segment with control `1`.

If all supplied blocks have unit-modulus controls and their phase
ratios multiply to `−1`, assembly from `x0` constructs a `Pulse` with
exact CZ closure and exposure equal to the sum. These hypotheses
remain explicit. This does not produce the face-to-face blocks from
the retained excursions by itself: the later endpoint-repair and excursion-
assembly modules construct them under controllability and prove the
conditional physical-completeness result. No new axioms are introduced.

The unit-modulus requirement is discharged by the complete conversion
of the following section: assembled disk-control segments are
normalized once by `toUnit`/`assembleDiskPulse`.

## Active-time factorization and exposure reduction

`ActiveClock.lean` defines the active clock `A(t)=∫₀ᵗ |u(q)| dq`
for every supplied `PhysicalSegment`, with no positive lower bound on
the control amplitude. It proves `0 ≤ S=A(D) ≤ D` and
`‖x(t)−x(s)‖ ≤ |A(t)−A(s)|`, so the state is constant on clock
fibers. A chosen clock section is monotone and measurable; its clamped
extension may jump. Nevertheless, composing the physical state with
this selector gives a globally `1`-Lipschitz active-time path in `X`
with the same endpoints and the same state-space image. Zero duration,
zero active duration, and clock plateaux are included.

Normalizing the selected control, with value `1` at zero, supplies a
globally measurable unit-modulus control. The following dynamics and
realization modules prove that it drives this path and package it
as a `PhysicalSegment`.

`ActiveExposure.lean` proves the exact cost identity
`∫₀ˢ c(Y(s)) ds = ∫₀ᴰ c(x(t)) |u(t)| dt ≤ P.exposure`.
The proof composes a continuously differentiable cost primitive with
the original clock and applies the absolutely-continuous FTC. It does not assume a
continuous inverse or change-of-variables theorem for the selector.
The following section establishes the dynamics under this possibly
discontinuous selector.
Endpoint steering, phase repair, and `Cstar ≤ pRelaxed` are supplied by
the later conditional reconstruction modules.
No new axioms are introduced.

## Complete disk-to-unit control conversion

`ActiveDynamics.lean` proves that the normalized control drives the
active-time path. The Lipschitz clock maps original null sets to null
sets. The image of its zero-control set is also null: outside a null
exceptional set, `A' = |u|`. At zero-control points satisfying this
identity, mathlib's one-dimensional Sard result applies. The Lipschitz
null-image bound handles the exceptional set.

Rademacher's theorem gives differentiability of the active-time path
almost everywhere. The chain rule for `x = Y ∘ A`, followed by
cancellation of the nonzero selected amplitude, identifies its
physical velocity. The scalar absolutely-continuous FTC then proves
the vector integral equation at every time. The selector is never
assumed continuous or differentiable.

`UnitControlRealization.lean` constructs `P.toUnit` for every supplied
`PhysicalSegment`: unit-modulus control, the same endpoints and
state-space image, active duration at most `P.duration`, and exposure
at most `P.exposure`. This includes zero duration, clock plateaux,
and zero active duration. No extra mathematical assumptions or
external axioms are used.

`FaceBlock.assembleDiskPulse` now constructs an exact-CZ `Pulse` from
a finite list of supplied face-to-face disk-control blocks whose
phase ratios multiply to `−1`. Its exposure and duration are bounded
by the respective sums. No unit-control hypothesis is needed.
Unconditional quantitative steering remains open; the following
sections prove the remaining reconstruction steps under
`LocalSteering`.

## Endpoint and phase repair under explicit local steering

`QuantitativeSteering.lean` defines `LocalSteering`, an explicit
hypothesis carrying positive constants `radius` and `K`. It requires
that nearby states in `X` admit a physical segment of duration at
most `K * ‖y−x‖^(1/4)`, using the ambient sup norm.
`BallBoxSteering.localSteeringOfBallBox` constructs this structure from
`CompactRegularLevelBallBox`, using the checked Lie-bracket and geometric
results. The generic input is still required; no unconditional inhabitant
or new axiom is asserted.

Given this hypothesis, connections starting or ending on `F` have
exposure at most `K³ d^(3/4)/12` when displacement is bounded by
`d ≤ radius`.
`EndpointRepair.lean` repairs a supplied segment whose two endpoint
costs are at most `α ≤ 1/12`, provided `32√α ≤ radius`. The resulting
face-to-face block has the phase-preserving projected endpoints and
exactly the original normalized endpoint phase ratio. The duration
overhead is at most `2 K (32√α)^(1/4)` and exposure overhead at most
`K³ 32^(3/4) α^(3/8)/6`.

For a face state with `z = −exp(iθ)` and `|θ| ≤ radius`, the same
hypothesis gives a physical correction to the exact-CZ target, with
duration at most `K |θ|^(1/4)`, exposure at most
`K³ |θ|^(3/4)/12`, and phase ratio `exp(−iθ)`. Appending this correction
to a supplied trajectory from `x0` and applying `toUnitPulse` gives
a `Pulse` with these additive bounds.

All these repair results remain conditional on `LocalSteering`.
Its derivation from the accepted quantitative-controllability input is
proved in `BallBoxSteering`. The
following assembly and cutoff sections complete the conditional
reconstruction under this hypothesis. No new axioms are introduced.

## Finite excursion assembly and pulse budget

`ExcursionPhaseAccounting.lean` proves the exact telescope between
retained intervals and their chronological gaps. Writing `E` for
`discardedAngularIntegral`, the retained normalized phase ratios
multiply to `−exp(−iE)`, with `|E| ≤ 8T√β`. The proof includes empty
selections and zero-length gaps; it does not choose principal phases.

`ExcursionAssembly.lean` applies the conditional endpoint repair to
each actual retained physical segment and phase-aligns the resulting
finite family from `x0`. Endpoint repair preserves every normalized
phase ratio exactly. The assembly therefore has phase deficit `−E`,
which the terminal repair closes before conversion to unit controls.

Given `H : LocalSteering`, an admissible exposure trajectory from
`y0` to `yPi`, and cutoffs `0 < α ≤ β/2`, `0 < β ≤ 1/12`, with
`32√α ≤ H.radius` and `8T√β ≤ H.radius`, Lean now constructs an
exact-CZ `Pulse`. Put `τ(d)=H.K d^(1/4)` and
`η(d)=H.K³ d^(3/4)/12`. Its bounds are
`duration ≤ T/α + [3T/(β√β)] τ(32√α) + τ(8T√β)` and
`exposure ≤ T + [3T/(β√β)] η(32√α) + η(8T√β)`.
The `β√β` denominator comes from the proved excursion-count bound.
No repaired blocks or phase-product identity are supplied as extra
hypotheses of the trajectory-to-pulse theorem.

The local-steering hypothesis is instantiated from the generic ball-box
input in `BallBoxSteering`. The following cutoff section discharges the
cutoff choice and derives
`Cstar ≤ pRelaxed` under `H` and the superposition hypothesis.
No new axioms are introduced.

## Cutoff limit and conditional physical completeness

`CutoffLimit.lean` chooses `α = β⁵`. For `T ≥ 0` and `β > 0`, the
exposure overhead is exactly `c_H(T) β^(3/8)`, where
`c_H(T) = H.K³ [3T·32^(3/4) + (8T)^(3/4)]/12`.
It proves that positive cutoffs can simultaneously satisfy the
excursion and steering-radius conditions and make the overhead
smaller than any `ε > 0`. Every admissible exposure trajectory of
length `T` therefore yields a finite-duration exact-CZ `Pulse` with
exposure at most `T + ε`, conditional on `H : LocalSteering`.
No uniform duration bound as `ε → 0` is claimed.

`PhysicalCompleteness.lean` combines this with directed-arc
superposition. For every feasible record `ν` and `ε > 0`, it produces
a `Pulse` with exposure at most `ν(univ).toReal + ε`; record finiteness
justifies this real-valued mass. Taking `ε → 0` and the infimum over
records proves `Cstar ≤ pRelaxed`, hence `pRelaxed = Cstar`.

These results are in the `LocalSteering` namespace and retain `H`
as an explicit parameter. Versions ending in `_of_superposition`
also take the superposition statement explicitly and use only
standard Lean axioms. The default wrappers additionally depend on
the existing `External.euclideanDirectedArcSuperposition` axiom.
No new axiom supplies `LocalSteering`; its physical application is
checked in `BallBoxSteering` conditional on the generic ball-box
input, which itself remains unproved. The main `Completeness.lean`
API now exposes both generic geometric inputs and uses the checked
physical proof. Polynomial certificates additionally require the two
algebraic inputs described below.

## Generic ball-box input and its physical application

`BallBoxInput.lean` specifies `CompactRegularLevelBallBox`, an
explicit, unproved corollary for compact regular level sets in
finite-dimensional real space. It requires smooth constraint and
control fields, a surjective constraint differential, tangent control
fields, and six independent actual brackets of lengths up to four
spanning the differential kernel. Its conclusion gives bounded,
measurable real quadratures with integral-form dynamics and duration
at most `C L^(1/4)` when a smooth connecting path has ambient length
at most `L ≤ R`. It does not mention Rydberg exposure, conditional
phase, or CZ endpoints. No axiom asserts this proposition.

This is a derived regular-level-set form, not the verbatim statement
in Jean's book. The cited full text gives the control-time
interpretation in Eq. (1.5), the local Holder estimate in Theorem 1.2,
and locally uniform estimates at regular points in Theorem 2.3.
The generic input still includes the regular-level-set manifold
interpretation, uniform compactness argument, norm-length comparison,
and integral-control realization. Those general results are not
formalized by introducing this input.
Source: https://hal.science/hal-01137580v1
(DOI `10.1007/978-3-319-08690-3`, printed pp. 6, 11, 32–33).

`BallBoxSteering.lean` proves the system-specific application. Its
`physicalSystem` verifies every input hypothesis using the physical
normalization map and the previously computed Lie brackets. It
converts real quadratures `(a,b)` to the complex control `u=a+ib`,
proving both the exact vector-field identity and the disk constraint.
The resulting physical segment preserves the duration, path, and
integral dynamics.

The proved short geometric path has Euclidean length at most
`16 ‖y-x‖∞`; its ambient sup-norm variation is no larger. Thus a
supplied generic bound `(R,C)` yields `LocalSteering` with
`radius = min(1/4,R/16)` and `K = C·16^(1/4)`.
`localSteeringOfBallBox` constructs this package from the explicit
generic theorem input. The construction includes coincident
endpoints and introduces no steering axiom.

Physical completeness now follows from two explicit generic inputs:
`CompactRegularLevelBallBox` and `EuclideanDirectedArcSuperposition`.
The fully parameterized implication has only standard Lean axioms;
the convenience wrapper uses the existing named superposition axiom
while retaining the ball-box input. The ball-box proposition itself
remains unproved; the main `Completeness.lean` API now carries both
generic inputs explicitly and uses the checked physical proof, but
supplying them is still required.

## Main conditional completeness API

`Completeness.lean` now uses the constructed system-specific local steering.
The main `Cstar_le_pRelaxed`, `pRelaxed_eq_Cstar`, and
`smooth_subsolution` declarations take only
`hSuperposition : EuclideanDirectedArcSuperposition`.
Their proofs use only standard Lean axioms; the physical-realization
`sorry` has been removed.

This is an API change: `polynomial_certificates`,
`stationary_completeness`, and `fixed_partition_convergence` take
only superposition before their threshold or partition arguments. C¹ approximation
is supplied by the proved Bernstein theorem; matrix SOS representation uses M5.
The certificate construction uses the physical-threshold smooth bound,
so its remaining assumptions stay visible through convergence.
Weak duality, nesting, embedding, finite-order hierarchy bounds,
and face compression remain unconditional.

`polynomial_certificates` now invokes the checked SOS construction.
Both convergence theorems use this result and have only the standard
axioms `propext`, `Classical.choice`, and `Quot.sound` as dependencies.
`CompletenessAudit.lean` prints the generic input definitions and
the theorem signatures, and rejects any nonstandard axiom in the three
final results. The general ball-box theorem is not proved or required:
the finite-pulse construction supplies this system's local steering directly.

## Cost-weighted polynomial approximation

`PolynomialApproximation.lean` constructs the exposure-coordinate map
as real polynomials and proves its evaluation agrees exactly with `Jmap`.
For a supplied differentiable function `φ`, `C1ApproxOnY φ P η` records
uniform value error and derivative operator-norm error at most `η` on
`Yset`. The derivative norm uses the existing sup norms; it is not a
coordinatewise derivative bound with an omitted dimension factor.

The identity `DJ·vf = c·B` and the proved bound `‖B‖ ≤ 32` give physical
drift error at most `32 η c`, including the zero-cost face. If the supplied
centered smooth bound has drift magnitude at most `c`, the actual state
polynomial `Q = (P∘J-P(yPi))/(1+32η)`, for `η ≥ 0`, has the same rate
bound and is zero on every state in `XCZ`. Its initial-value error is at most
`(2+32|b|)η`, where `b=φ(y0)-φ(yPi)`.

For `0<α<1`, the polynomial `W=(1-α)Q` has residual
`c+f_u W ≥ α c` for every disk control. Its initial-value error is at most
`α|b|+(2+32|b|)η`. Given `a<b`, Lean chooses positive `α,η` so that every
supplied polynomial satisfying the approximation bounds yields `W(x0)>a`,
exact terminal zero, and the weighted strict residual.

These are transfer and tolerance theorems. This module alone does not
establish existence, average over `G`, or supply an SOS representation;
the subsequent modules provide those steps under explicit inputs.
All these transfer results use only standard Lean axioms.

## Polynomial existence from a generic approximation input

`C1ApproximationInput.lean` defines `BoxC1PolynomialApproximation`:
a globally `C¹` function in dimension at least two admits simultaneous
polynomial approximation of values and all first coordinate derivatives
on a positive-radius closed symmetric box. This is an explicit,
unchanged proposition, now proved by `boxC1PolynomialApproximation` in
`BernsteinApproximation.lean`; no axiom supplies it.

The corresponding classical result is a corollary of Veretennikov and Veretennikova,
arXiv:1507.05235v2, Theorems 3 and 4 for the cube Bernstein polynomials.
The inspected full text proves uniform convergence of values and first
partial derivatives. The Lean proof constructs the tensor polynomial,
regroups its actual partial derivatives into mixed-degree Bernstein sums,
proves uniform convergence of forward differences using only C¹ regularity,
and selects one order for the value and all finitely many partials.
Affine rescaling uses tolerance `min δ (2*R*δ)`, accounting for the derivative
factor `1/(2*R)` even when the box radius is small.

`PolynomialExistence.lean` proves the application. Compactness supplies
a box containing `Yset`. For the sup norm on `ℝ^n`, coordinate derivative
errors at most `δ` give derivative operator-norm error at most `nδ`.
At `n=11`, requesting `δ=η/11` therefore yields `C1ApproxOnY φ P η`.
The resulting polynomial is then passed to the previously checked
normalization and tolerance construction.

`exists_strict_candidate_below_Cstar` now takes only directed-arc superposition
as a generic input. For every real `a<Cstar`, it produces
`P,η,α` with `η>0` and `0<α<1`, such that the actual state polynomial
`W=strictPolynomial P η α` satisfies `W(x0)>a`, is zero on every CZ
target state, and has residual `c+f_u W≥αc` for every disk control.
Its representation as a scaled polynomial in `J` remains explicit.

All application proofs use only standard Lean axioms. The generic
approximation theorem remains unproved. This module supplies neither
`G`-averaging nor an SOS representation; subsequent modules supply both.

## Reflection averaging and preservation of the initial objective

`PolynomialSymmetry.lean` constructs the reflection average
`(W + W ∘ reflection)/2` as an actual real polynomial. It proves that
degree does not increase and that the initial value, terminal zero,
and weighted residual margin `c+f_u W≥αc` are preserved. The dynamics
identity uses the control `−conj u`; omitting the minus sign is wrong.
All these statements include the zero-cost face and disk controls.

The initial exposure fibre is the set of states satisfying `J(x)=y0`.
It is characterized by `c(x)=0` and `z(x)=1`, and every generator of
`G` preserves it. Thus polynomials constructed from `J` retain their
initial value along the symmetry orbit. This does not assert that `J`
is invariant everywhere, or that arbitrary state polynomials retain
their objective under rotation. The audit includes an explicit
counterexample to the latter interpretation.

Reflection averaging preserves the concrete `strictPolynomial P η α`
form: it equals `strictPolynomial P' η α` for an explicitly constructed
exposure-coordinate polynomial `P'`. The resulting
`exists_reflection_candidate_below_Cstar` has the same superposition
input as `exists_strict_candidate_below_Cstar`, with no added
assumption. If a polynomial is already invariant under both continuous
rotations, `reflectionAverage_isGInvariant` proves that its reflection
average is fully `G`-invariant.

## Full continuous symmetry averaging

`RotationAverage.lean` completes the symmetry milestone. Haar measure is
the translation-invariant measure on a compact group; mathlib supplies its
construction, normalized here to total mass one on `Circle × Circle`.
`PolynomialIntegration.lean` integrates coefficients in a finite exponent
set, yielding a genuine polynomial with no degree increase. Every real
linear functional commutes with this operation, including evaluation and
the directional derivative. No differentiation under an integral is assumed.

`RotationAction.lean` proves the physical rotation action and its control
transformation. Continuous averaging followed by reflection preserves the
initial value of candidates constructed from `J`, terminal zero, and the
weighted residual margin, including at zero cost. The exposure-coordinate
action also proves the exact polynomial identity
`symmetryAverage (strictPolynomial P η α) = strictPolynomial P' η α`.
Thus the next matrix construction retains the required polynomial-in-`J`
form, not merely equality on the normalized state space.

`exists_G_invariant_candidate_below_Cstar` supplies the fully invariant
candidate under directed-arc superposition alone. The audit checks
its axiom dependencies and examples where constants and cost survive,
an odd amplitude coordinate vanishes, and the zero-cost boundary is included.
This averaging module alone asserts no SOS representation or
`StationaryFeasible` conclusion.

## Uniform positive-matrix correction

`MatrixCorrection.lean` proves the correction step of Appendix E. A matrix
is positive definite when its quadratic form is positive on every nonzero
vector. For the amplitude vector `r`, the correction is
`B(r) = (r · r) I - r rᵀ`. Its identities hold over any commutative ring,
so also for polynomial entries: `B(r)r=0`, and adding `Λ B(r)` preserves
the scalar residual `rᵀ A r` exactly. Over the reals, the correction is
positive semidefinite; for nonzero `r`, its quadratic form vanishes
exactly on scalar multiples of `r`.

`exists_corrected_posDef` proves that one nonnegative real `Λ` makes
`A(x)+Λ B(r(x))` positive definite throughout a compact domain, provided
`A` and `r` are continuous, `A` is symmetric, `A` is positive definite
where `r=0`, and `rᵀ A r>0` elsewhere. It does not assume positivity
in the other directions. The proof takes a finite open subcover of
the compact domain times the unit sphere, rather than introducing
explicit Schur-complement bounds. This is a proved compactness argument,
not another general theorem input.

The audit checks a matrix with nonzero cross entries: coefficient 8
repairs it, while coefficient 7 leaves it singular. It also checks that
the zero-amplitude face is unchanged. All audited dependencies are
standard Lean axioms. The physical polynomial matrix is now extracted
and corrected as described below; `SOSRepresentation` supplies its
sum-of-squares representation under the explicit matrix positivity input.

## Exact polynomial extraction from the candidate residual

The amplitude ideal is the set of polynomial combinations of the four
real Rydberg-amplitude coordinates. Its cube consists of sums containing
at least three amplitude factors. `ResidualFactors.lean` proves that
the drift of every `strictPolynomial P η α` belongs to this cube,
with no assumptions on `P`, `η`, or `α`. It checks the real and imaginary
progress-derivative identities explicitly and proves the remaining
exposure-coordinate cases using the polynomial product rule.

`MatrixExtraction.lean` extracts two amplitude factors from each cubic
generator, then symmetrizes the coefficient matrix without changing its
quadratic form. The entries retain one amplitude factor, so they vanish
on the entire zero-amplitude face. Adding the cost diagonal yields
`exists_residual_matrix`: a symmetric real polynomial matrix `A₀` with
`rᵀ A₀ r = cpoly + lieDeriv (strictPolynomial P η α)` exactly, and
`A₀ = diag(1/2,1/2,1/4,1/4)` wherever all four amplitudes vanish.
The diagonal's positive definiteness is also proved. These are polynomial
identities before imposing normalization, not only equalities modulo its ideal.

This applies to the fully averaged candidate because symmetry averaging
preserves its `strictPolynomial` form. The extraction does not assume
the cubic-factor property from the caller and adds no external theorem
input. The audit includes asymmetric complex amplitudes and control to
check the derivative signs, the cost weights, and mixed-term symmetrization.
The uniform correction is now applied to this matrix as described below.
`SOSRepresentation` obtains the matrix sum-of-squares representation and
connects finite degrees to `StationaryFeasible`, conditional on the generic
matrix positivity input.

## Positive matrix on the physical domain

`PositiveResidualMatrix.lean` completes the positive-matrix construction.
For any strict candidate with positive weighted margin, it constructs a
symmetric polynomial matrix representing the same residual exactly and
positive definite on every normalized state and every control in the closed
unit disk, including the zero-cost face. The caller supplies no matrix,
factorization, or compactness hypothesis.

The compact domain is `Xset × closedBall (0 : ℂ) 1`. The polynomial ring
also contains an unused cell coordinate `ξ`, so the construction evaluates
the extracted matrix at `ξ=0` when applying compactness. It then applies
the polynomial substitution `freeze` to the corrected matrix. This removes
`ξ` without changing the residual identity, and the resulting matrix is
proved independent of `ξ` and positive for every real value of it.
No compactness in an unbounded auxiliary coordinate is assumed.

`exists_positive_matrix_candidate_below_Cstar` combines this construction
with the nearly optimal invariant candidate under superposition alone.
It preserves the initial objective and exact target zero.
No matrix Positivstellensatz input is used yet. The audit checks polynomial
specialization and a concrete candidate whose matrix is strictly positive
at zero cost for both zero and unit controls and nonzero cell coordinates.
`SOSRepresentation.lean` subsequently supplies the matrix SOS representation
and finite-degree feasibility used by the integrated completeness theorem.

## Build and audit

From the repository root:

```bash
cd lean/appendix-e
lake exe cache get
lake build RequestProject.AppendixE.BFieldRegularity
lake env lean BFieldRegularityAudit.lean
lake build RequestProject.AppendixE.ExposureCompactness
lake env lean ExposureCompactnessAudit.lean
lake build RequestProject.AppendixE.RelaxedSubsolution
lake env lean RelaxedSubsolutionAudit.lean
lake build RequestProject.AppendixE.ExposureDisintegration
lake env lean ExposureAveragingAudit.lean
lake build RequestProject.AppendixE.ExposureCurrent
lake env lean ExposureCurrentAudit.lean
lake build RequestProject.AppendixE.ExposureDecomposition
lake env lean ExposureDecompositionAudit.lean
lake build RequestProject.AppendixE.ExposureArc
lake env lean ExposureArcAudit.lean
lake build RequestProject.AppendixE.ExposureClock
lake env lean ExposureClockAudit.lean
lake build RequestProject.AppendixE.ExposureReparamODE
lake env lean ExposureReparamAudit.lean
lake build RequestProject.AppendixE.ExposureSubcurrent
lake env lean ExposureSubcurrentAudit.lean
lake build RequestProject.AppendixE.ExposurePolarCurrent
lake env lean ExposurePolarCurrentAudit.lean
lake build RequestProject.AppendixE.ExposureSuperposition
lake env lean ExposureSuperpositionAudit.lean
lake build RequestProject.AppendixE.PhysicalClock
lake env lean PhysicalClockAudit.lean
lake build RequestProject.AppendixE.PhysicalReparam
lake env lean PhysicalReparamAudit.lean
lake build RequestProject.AppendixE.ExposureExcursions
lake env lean ExposureExcursionsAudit.lean
lake build RequestProject.AppendixE.ExposureRecordSelection
lake env lean ExcursionSelectionAudit.lean
lake build RequestProject.AppendixE.DiscardedProgress
lake env lean DiscardedProgressAudit.lean
lake build RequestProject.AppendixE.LowCostPhase
lake env lean PhaseTransportAudit.lean
lake build RequestProject.AppendixE.ExcursionGaps
lake env lean ExcursionGapsAudit.lean
lake build RequestProject.AppendixE.SectorPhase
lake build RequestProject.AppendixE.SteeringExposure
lake env lean SteeringExposureAudit.lean
lake build RequestProject.AppendixE.ControlLieAlgebra
lake env lean ControlLieAlgebraAudit.lean
lake build RequestProject.AppendixE.StateGeometry
lake env lean StateGeometryAudit.lean
lake build RequestProject.AppendixE.FaceBlockAssembly
lake env lean PhysicalAssemblyAudit.lean
lake build RequestProject.AppendixE.ActiveExposure
lake env lean ActiveTimeAudit.lean
lake build RequestProject.AppendixE.UnitControlRealization
lake env lean UnitControlAudit.lean
lake build RequestProject.AppendixE.EndpointRepair
lake env lean EndpointRepairAudit.lean
lake build RequestProject.AppendixE.ExcursionAssembly
lake env lean ExcursionAssemblyAudit.lean
lake build RequestProject.AppendixE.PhysicalCompleteness
lake env lean PhysicalCompletenessAudit.lean
lake build RequestProject.AppendixE.BallBoxSteering
lake env lean BallBoxSteeringAudit.lean
lake build RequestProject.AppendixE.PolynomialApproximation RequestProject.AppendixE.Completeness
lake env lean PolynomialApproximationAudit.lean
lake build RequestProject.AppendixE.PolynomialExistence
lake env lean PolynomialExistenceAudit.lean
lake build RequestProject.AppendixE.PolynomialSymmetry
lake env lean PolynomialSymmetryAudit.lean
lake build RequestProject.AppendixE.RotationAverage
lake env lean RotationAverageAudit.lean
lake build RequestProject.AppendixE.MatrixCorrection
lake env lean MatrixCorrectionAudit.lean
lake build RequestProject.AppendixE.ResidualFactors
lake env lean ResidualFactorsAudit.lean
lake build RequestProject.AppendixE.PositiveResidualMatrix
lake env lean PositiveResidualMatrixAudit.lean
lake build RequestProject.AppendixE.SOSRepresentation
lake env lean SOSRepresentationAudit.lean
lake build RequestProject.AppendixE.Completeness
lake env lean CompletenessAudit.lean
lake build RequestProject.AppendixE.TerminalCertificate
lake env lean TerminalCertificateAudit.lean
lake build RequestProject.AppendixE.ReducedBasis
lake env lean ReducedBasisAudit.lean
lake build RequestProject.AppendixE.FaceRestriction
lake env lean FaceRestrictionAudit.lean
lake build RequestProject.AppendixE.QuotientNormalForm
lake env lean QuotientNormalFormAudit.lean
lake build RequestProject.AppendixE.SymmetryGram
lake env lean SymmetryGramAudit.lean
lake build RequestProject.AppendixE.StationaryGram
lake env lean StationaryGramAudit.lean
```

The audit prints the target types and their axiom dependencies. Run
`lake build` in the same directory to build all modules. The main
module has no admitted proof. The main audit enforces a standard-axiom
allowlist for the certificate and convergence results. The regularity
module has two non-blocking linter warnings. Its `maxHeartbeats 800000`
setting affects the elaboration budget only.

## Remaining general assumptions

The main completeness API exposes one generic input:
`EuclideanDirectedArcSuperposition`.
The system-specific application and physical reconstruction are
proved under this input. The main declarations do not silently
invoke the named superposition axiom; convenience wrappers in the
separate reconstruction modules still document that dependency.

The checked `polynomial_certificates` construction
uses polynomial approximation that preserves the weighted rate
inequality near the zero-cost face, symmetry averaging, and the
matrix Positivstellensatz. The cost-weighted transfer for a supplied
`C¹` approximant is proved in `PolynomialApproximation.lean`, and
`PolynomialExistence.lean` produces such an approximant and a strict
polynomial candidate using the proved `boxC1PolynomialApproximation` theorem.
Only superposition is needed at this stage. Full symmetry averaging is checked in
`PolynomialSymmetry.lean` and `RotationAverage.lean`, retaining the exact
normalized polynomial-in-`J` representation. The uniform matrix correction
is proved in `MatrixCorrection.lean`, `ResidualFactors.lean` extracts
the physical polynomial matrix exactly, and `PositiveResidualMatrix.lean`
applies the correction on the physical domain. `MatrixSOSInput.lean`
states the generic matrix Positivstellensatz proposition, proved in
`MatrixSOSTheorem.lean`. `SOSRepresentation.lean` applies that theorem,
contracts the matrix representation into scalar squares, and proves
`exists_stationary_feasible_below_Cstar` with only superposition explicit.
The proof temporarily adds the equation ξ=0 to obtain an Archimedean ideal
(a constant minus the squared coordinate norm is SOS modulo the ideal).
Substitution then removes that equation and returns to the original
`normIdeal`. The finite order is chosen after obtaining the finite family
of squares; no effective degree bound is assumed or claimed.
The construction and its integrated dependents `polynomial_certificates`,
`stationary_completeness`, and `fixed_partition_convergence` have no
`sorryAx` or project-axiom dependency. Superposition remains an explicit,
unproved theorem input.
There is no unconditional completeness claim from the checked
conditional proofs.

The first step toward proving the matrix input, M1, is complete in
`SOSOrderBounds.lean`. From `IdealArchimedean I`, every element `a` of the
polynomial quotient has a natural bound `N` with both `N+a` and `N-a` in
mathlib's finite sum-of-squares cone `IsSumSq`. The proof first bounds
squares of variables, then constants, sums, and products, and finally
completes squares to obtain both signs with the same bound. It imposes no
partial-order or proper-ideal assumption. `isSumSq_quotient_iff` identifies
this cone exactly with the project's finite-degree `IsSOS` certificates
modulo `I`; `polynomial_order_certificates` returns those certificates for
both signs. The audit instantiates the result on the physical `sliceIdeal`,
the zero-variable case, and the unit ideal.

M2, the scalar strict-positivity representation theorem, is proved in
`ScalarSOSRepresentation.lean`: `IdealArchimedean.scalar_representation`
turns strict positivity on every real zero of `I` into an exact finite-degree
`IsSOS` certificate modulo `I`. `SOSSeparation.lean` uses algebraic Riesz
extension to separate a nonmember of the SOS cone by a normalized positive
linear functional; it does not assume the cone is closed. `SOSStates.lean`
uses the M1 bounds and Tychonoff compactness for the state space, obtains an
extreme minimizing state by the Krein–Milman lemma, and proves that extreme
states are multiplicative. Quotient characters are then identified with
evaluations on the real zero set. The theorem needs neither a nonempty zero
set nor a proper ideal. Its strict-positivity hypothesis is not weakened to
nonnegativity, and it does not give an effective degree bound. The audit
checks the physical slice, the variety `x²=1`, zero variables, the unit ideal,
and rejection of an unconstrained negative constant, with a transitive
axiom allowlist.

M3 is proved in `MatrixSOSApproximation.lean`. On any compact real coordinate
set, a continuous positive semidefinite matrix field has a continuous
canonical square root, including at changes of rank. A local proof of the
isometric real-matrix functional calculus supplies the needed continuity;
no continuously chosen eigenbasis is assumed. Stone–Weierstrass gives one
finite polynomial matrix approximating all square-root entries uniformly.
The explicit entrywise Gram-error bound is `k δ (2M+δ)`, where `M` bounds
the exact factor entries and `δ` bounds the factor errors. The theorem
`exists_polynomial_sqrt_gram_approximation` makes both errors smaller than
any positive tolerance. `IdealArchimedean.isCompact_realZeroSet` proves
compactness from the existing witness, and
`IdealArchimedean.polynomial_matrix_gram_approximation` specializes the result
to polynomial matrices on that zero set, without new analytic assumptions.
The audit covers the physical slice, a nonscalar family whose rank changes,
and zero-dimensional matrices and coordinate spaces. This is uniform
approximation, not an exact matrix SOS identity.

M4 is proved in `MatrixSOSRemainder.lean`.
`IdealArchimedean.diagonally_dominant_gram` gives an exact finite rectangular
polynomial Gram representation modulo the ideal for every symmetric matrix
whose diagonal entries strictly exceed the sums of absolute off-diagonal
entries on the real zero set. Compactness gives a uniform positive row gap;
polynomial approximation of absolute values supplies symmetric majorants
without treating absolute values as polynomials. `dd_decomposition` proves
the exact rank-one identity using directions `e_i` and `e_i ± e_j`.
M2 represents the positive scalar coefficients modulo the ideal, and
`finite_rankOne_gram` stacks their finite square families into one matrix.
`near_scalar_gram` supplies the M3 tolerance interface: an entrywise error
less than `μ/(2*(k+1))` from `μ Id`, for `μ>0`, suffices for an exact
certificate. No external positivity theorem or numerical checker is used.
The audit covers the physical slice, changing off-diagonal signs with unequal
diagonal margins, the non-unit-shift error budget, empty zero sets, zero
matrix dimension, and rejection of a negative scalar Gram certificate.
M5 is proved in `MatrixSOSTheorem.lean`. Compactness of the zero set times
the unit sphere gives one positive scalar shift `μ` with `A-μ Id` positive
semidefinite throughout the zero set. M3 approximates that shifted matrix;
its remainder relative to `A` is close enough to `μ Id` for M4. Stacking
the approximate factor and the exact remainder factor proves the original
`MatrixPositivstellensatz` proposition without changing its statement.
There is no diagonal-dominance premise on `A`, no supplied spectral gap,
and no nonempty-variety premise. The audit includes a positive definite
polynomial family that is not diagonally dominant and an empty variety.
`hSOS` is removed from the residual-square, polynomial-certificate, abstract
convergence, concrete convergence, and finite-real epsilon APIs. The
transitive axiom checks include the new theorem and these downstream results.
Only superposition remains unproved; Appendix E is still conditional on it.

## Correspondence with the concrete reduced certificate program

The concrete convergence theorems use the real charge-block and face-reduced
matrix cones described below, not aliases for the abstract optimal values.
The degree-preserving stationary conversion, concrete soundness, and
convergence transfer are complete. Successful-pulse existence follows from
the controllability input, and finite-real epsilon corollaries are proved.
Partitioned results retain the successful-pulse-below-ceiling hypothesis.

`TerminalCertificate.lean` closes the terminal part of the stationary embedding.
It proves that every exact CZ target lies in the qubit-phase orbit of
`(1,0,-1,0)`, so evaluating an invariant polynomial there agrees with evaluating
it anywhere on the target. The polynomial substitution `terminalRestriction`
implements Appendix C's τ while retaining the cell coordinate ξ.
For stationary W, its terminal restriction is constant. Its negative is
represented in the actual column `(1,ξ,…,ξ^d)` by the positive-semidefinite
matrix `diag(-W(x_CZ),0,…,0)`; the interval multiplier is zero. This preserves
the order and uses no general positivity theorem. This module handles only
the terminal restriction; the following modules supply the drift conversion
and concrete partitioned program.

`ReducedBasis.lean` proves the finite-dimensional face conversion for an
already grouped column. A formal restriction map records each distinct
restriction character in its own coefficient slot. The prescribed columns
`Σ_{i<ℓ} m_i - ℓ m_ℓ`, together with the already vanishing monomials, span
exactly the kernel of that map within the original span (`face_span_eq`).
The group conversion works over any characteristic-zero field, including
both ℝ and ℂ. These are integer-coefficient columns, but their coordinates
are field elements; no integral-lattice basis claim is made.
`reducedColumn_degree` proves that all new columns retain the original
degree bound. `face_sos_gram` converts a real sum of squares into a
positive-semidefinite Gram matrix on those columns, with exactly the same
polynomial and no degree increase. It does not require the columns to be
linearly independent and handles singleton groups and empty columns.

`FaceRestriction.lean` supplies the physical-to-formal bridge. A Laurent
polynomial is a finite sum allowing negative powers of the unit phases.
The constructed restriction map has coefficient index
`(ξ degree, u winding, g₁ winding, g₂ winding)`. It substitutes zero for the
excited amplitudes and writes each real/imaginary ground or control coordinate
using its positive- and negative-winding modes. Its evaluations agree with
the actual physical state and control. Distinct characters are proved
linearly independent using mathlib's checked independence-of-characters
theorem; their distinctness is proved by differentiating the one-parameter
exponentials at zero. Character independence is not an additional input.

`stationary_factors_restriction_zero` proves that every stationary SOS factor
has zero formal restriction. The proof uses positive ξ and arbitrary phases;
the existing stationary face-vanishing lemma supplies vanishing for every
real ξ, so no interval-only hypothesis is silently strengthened.
`normIdeal_restriction_zero` also proves that the normalization-ideal terms
are killed. `stationary_factor_mem_reduced_span` connects the actual
restriction to the previous finite-column conversion for a supplied monomial
expansion and an injective list of restriction characters.

`QuotientNormalForm.lean` constructs the degree-bounded expansion. A
quotient-normal monomial has no simultaneous barred/unbarred powers of
u, g₁, or g₂. The mixed polynomial coordinates are
`ξ,u,ū,g₁,ḡ₁,r₁,r̄₁,g₂,ḡ₂,r₂,r̄₂`. The construction removes common
control powers using `u ū = 1` and common ground-state powers using
`gₖ ḡₖ = 1 - rₖ r̄ₖ`, expanding the latter powers in the polynomial ring.
`exists_normal_expansion` proves equivalence modulo the ideal generated by
these three relations, no increase in total degree, and normality of every
monomial with nonzero coefficient. It does not assert uniqueness.

`factorExpansion` converts an actual real-coordinate polynomial into these
mixed coordinates and normalizes it. Its degree does not increase and its
value agrees with the original polynomial on normalized physical states
with unit controls. `stationary_expansion_restriction_zero` proves that the
expanded stationary square factors still have zero formal face restriction.
The audit checks the theorem dependencies and examples with unequal powers,
complex coefficients, repeated ground pairs, control-pair cancellation,
negative ξ, and the actual degree-one stationary cost decomposition.

`SymmetryGram.lean` constructs the matrices for a supplied finite column
representation. A charge is the pair of integer phase responses to optical
and qubit rotations. `separate` sets entries between different charges to
zero. Positivity follows by writing this matrix as a sum of coordinate
compressions of the original positive matrix. Preservation of an invariant
expression follows from the already proved independence of phase characters;
individual factors need not be invariant. `factor_gram_value` constructs
the complex matrix from factor coefficients, and `monomial_gram` applies
charge separation to finite mixed-monomial expansions.

`rotatePoint_physical` identifies the mixed-coordinate rotation with the
actual physical gauges. `rephased_monomial_reflection` checks the reflection
sign and its absorption by i for odd total control degree. `rephaseMatrix`
transforms the matrix with the basis, preserving positivity, values, and
charge blocks; the scalar rephasing does not increase polynomial degree.
`realMatrix` takes entrywise real parts, which preserves positivity and
represents the reflection average, not an arbitrary unchanged expression.
`real_invariant_gram` combines the constructions to produce a real symmetric
positive charge-block matrix under explicit rotation/reflection identities
for the supplied representation. The audit includes cancellation across
redundant columns, retained within-charge off-diagonals, the rephasing sign,
and negative controls showing why the invariance hypotheses are necessary.

`StationaryGram.lean` now supplies the stationary-certificate application.
`stationary_matrix` assumes only `StationaryFeasible d W`. It constructs a
common finite column set from the supports of the normalized square factors,
with zero coefficients where a factor lacks a column. Every column is normal
and has degree at most d. The polynomial symmetry of W implies symmetry of
the residual through the checked covariance of its drift. Thus the finite
representation and its rotation/reflection identities are proved from the
certificate, not requested as extra hypotheses.

The resulting matrix is real symmetric and positive semidefinite, has zero
entries between different charges, and represents `c + f_u W` on every
normalized state and unit control for every real ξ, with the prescribed
parity rephasing of its columns. The audit applies this result to the actual
order-one W=0 certificate: the same matrix gives costs 1/2 and 1/4 for the
two separately excited sectors and zero at the initial state. It also checks
empty factor families and coefficient padding across unequal supports.

`NormalFaceBasis.lean` constructs a fixed degree-bounded face column. An
excited monomial contains at least one of r₁, r̄₁, r₂, r̄₂. For fully normal
unexcited monomials, the restriction label (ξ degree and three signed phase
powers) is injective. Thus the nonzero restriction groups are singletons;
the within-group difference columns contribute nothing in this presentation.
`face_span_iff` proves that a normal polynomial of degree at most d has zero
restriction exactly when it belongs to the span of the normal excited
monomials of degree at most d. This does not assert the same characterization
for polynomials that have not been normalized.

`StationaryGram.stationary_face_submatrix` puts every stationary column in
that fixed set. `FaceGram.stationary_face_matrix` extends the resulting
matrix by zero to the whole fixed column, preserving positivity, charge
blocks, and the represented physical values without increasing degree.
It assumes only `StationaryFeasible d W`; no factor expansion or face
vanishing is supplied as an extra hypothesis. Both conjugate charge signs
are retained. The audit checks the degree boundary, a nonnormal restriction
collision, preservation of general off-diagonal quadratic terms, and an
actual stationary certificate's unequal sector costs and zero face value.

`ConjugateGram.lean` compresses each pair of opposite charges to one block.
Its exponent involution swaps barred/unbarred coordinates, fixes ξ, and
preserves normality, face-basis membership, and total degree. The rephased
conjugate column is the conjugate of the original column times the real
sign (-1)^k, where k is total control degree. Consequently the opposite
matrix is reindexed and transformed by that diagonal sign matrix before
being added; simply adding the two blocks would be incorrect.

`retained` selects charges with positive first coordinate, or zero first
coordinate and nonnegative second coordinate. `retained_covers` and
`retained_unique` prove coverage and uniqueness of nonzero conjugate pairs.
The zero charge is retained without doubling. `stationary_compressed`
assumes only `StationaryFeasible d W` and constructs real positive matrices
whose sum over these representatives equals the physical residual, at the
same degree. The arbitrary sign convention chooses one representative per
pair; it does not assert agreement with an external serialized block order.
The audit distinguishes the correct signed value 29 from the naive value
53 on a nonzero off-diagonal example, and checks the compressed stationary
family on unequal sector costs and the zero-cost face.

`QuotientCertificate.lean` supplies the exact algebraic starting identity.
Equality modulo the normalization ideal means that the polynomial difference
is a polynomial combination of the three normalization constraints.
`normalization_ideal_eq` proves that the ideal generated by the converted
real-coordinate constraints is exactly `QuotientNormalForm.relations`;
no extra constraint or stronger vanishing ideal is substituted.
`normalized_squares` transfers the original square identity through the
coordinate conversion and factor normalization. Polynomial conjugation
conjugates coefficients and swaps barred/unbarred variables, fixing ξ.
It preserves the normalization ideal, and each normalized real factor is
fixed by it modulo that ideal. `normalized_gram` then proves the exact
polynomial Gram identity using the same coefficient matrix as the earlier
physical-domain construction.

`stationary_exact_gram` assumes only `StationaryFeasible d W` and gives a
positive complex matrix on degree-d normal face columns with the exact
quotient identity. This matrix is **before** charge separation and reflection
averaging. It is not the previously constructed compressed real matrix.
The audit covers arbitrary polynomial multipliers, a normalization generator
that is nonzero off the constraint set, coefficient conjugation, signed
off-diagonal polynomial terms, empty columns, and an actual feasible W=0
certificate. The polynomial identities are checked with independent formal
barred variables, not inferred from equality only on physical states.

`QuotientSymmetry.lean` proves that both symmetry projections preserve the
normalization ideal. A charge component retains exactly the monomials of
one specified charge. The generators all have charge zero, so mathlib's
graded-ideal theorem proves preservation even for arbitrary polynomial
multipliers. `chargePart_gram` identifies zero-charge projection with
deleting cross-charge Gram entries as a literal polynomial identity.
Projection is linear, not multiplicative: two charged factors can multiply
to an invariant term.

The formal reflection swaps barred/unbarred variables, negates both control
coordinates, and leaves coefficients unchanged. `reflectionAverage` averages
a polynomial with that substitution; it preserves ideal membership.
`reflectionAverage_gram` identifies the average with entrywise matrix real
parts for a Hermitian matrix when reflection conjugates the supplied columns.
The column condition remains explicit; odd-control columns need rephasing.
`separated_congr` and `real_averaged_congr` transfer quotient identities.
`stationary_projected_identity` applies the projections to actual stationary
Gram data, preserving its normal face columns, degree bound, positivity,
and charge separation. Both sides of its identity are explicitly projected.

`ResidualSymmetry.lean` removes the projection from the target.
`residual_chargePart` and `residual_reflectionAverage` prove that each
projection fixes the embedded stationary residual as an exact polynomial,
using only the existing symmetry assumption on W. `mixedPoint_ext` justifies
polynomial equality from unrestricted real state and control coordinates:
an invertible Cartesian coordinate substitution reduces it to polynomial
extensionality on infinite coordinate sets. No normalization constraint is
imposed in this step. Independent rotation characters extract the
zero-charge component; reflection uses the signed conjugate control and
leaves complex coefficients unchanged. `stationary_identity` applies these
results to `StationaryFeasible`, retaining the degree-bounded normal face
columns, positivity, and charge separation while removing the target's
projection. The Gram expression on the right is still reflection-averaged.
`ResidualSymmetryAudit.lean` checks dependencies, a nonconstant invariant W,
a feasible W=0 certificate, unrestricted zero-control evaluation, and the
distinction between reflection and coefficient conjugation.

`reflect_rephased_term` now proves the column-reflection identity for every
exponent vector as an exact polynomial equality. The prescribed multiplier
is i for odd total control degree (counting both u and its barred coordinate),
and 1 otherwise. This needs no normal-form, face, or degree hypothesis, so it
also covers every column in the fixed face basis. The proof uses unrestricted
polynomial extensionality, not equality restricted to normalized states.
`reflectionAverage_rephased_gram` specializes the real-part Gram theorem to
any finite family of these columns; its only matrix assumption is Hermitian
symmetry. The audit checks asymmetric control exponents, even total degree
with both exponents odd, and failure of the identity for a raw odd column.

`rephaseMatrix_gram` proves that rephasing the matrix and its columns together
preserves the Gram polynomial exactly, for arbitrary polynomial columns and
matrices. `stationary_real_identity` combines this with reflection averaging:
from only `StationaryFeasible d W`, it constructs a real positive-semidefinite,
charge-separated matrix on a subset of the degree-d normal face basis. The
original embedded residual equals its rephased Gram polynomial modulo the
normalization ideal, with no projection or reflection average left in the
identity. The audit checks the sign of mixed-parity imaginary off-diagonal
entries and specializes the real-matrix result to a feasible W=0 certificate.

`pad_gram` lifts the existing inclusion padding to an exact polynomial identity
for arbitrary polynomial columns. Its subset hypothesis ensures no source
column is discarded. `stationary_fixed_identity` applies it to the real
stationary matrix: the result is indexed by the full prescribed degree-d
normal face basis, with positivity, charge separation, and the same residual
identity modulo normalization. No degree increase, new mathematical input,
or physical-set-to-ideal inference is used. The audit covers an empty source,
single-column inclusion into an arbitrary larger basis, and the integrated
fixed-basis W=0 certificate.

`compressed_gram` now proves exact polynomial preservation under the existing
conjugate-block compression. It keeps one charge representative, applies the
parity signs when folding its opposite, and counts the zero block once.
The underlying compression lemmas hold for unrestricted state and control
values, allowing polynomial extensionality without a normalization assumption.
`stationary_compressed_identity` combines this with the fixed-basis result:
from only `StationaryFeasible d W`, it constructs real positive matrices on
the prescribed degree-d charge-sector columns, whose retained Gram sum equals
the original residual modulo the normalization ideal. No projection or
reflection average remains in that identity.

This strengthens the older physical-domain `ConjugateGram.stationary_compressed`
result with an exact quotient identity. These modules introduce no general
theorem input and do not silently strengthen the existing abstract convergence
results. The concrete feasibility definitions and convergence transfers below
complete this real-coefficient correspondence (AE-01); serialized archive
correspondence remains outside scope.

`ConcreteStationary.Feasible` now gives a standalone stationary matrix
feasibility definition: the degree bound and state symmetry, a finite family
of positive real matrices indexed only by retained charges, the exact drift
identity modulo normalization, and a positive terminal matrix on (1, ξ, …,
ξ^d). It does not include `StationaryFeasible` as an assumption. The terminal
restriction is constant in this stationary specialization, so an interval
multiplier is unnecessary. This is not the full partitioned feasibility cone.
`ConcreteStationary.of_stationary` constructs all these witnesses from an
abstract stationary certificate at the same order, with the same W and hence
unchanged objective W(x₀). The audit accepts W=0 at every order d≥1 and rejects
W=1 at every order using terminal positivity. This theorem proves the
stationary inclusion. Convergence is proved separately below; reverse
feasible-set equality is not required or asserted.

Concrete soundness is now proved directly from those witnesses.
`Feasible.drift_nonneg` evaluates the normalization-ideal identity on physical
states with unit control; a real positive matrix contributes a nonnegative
quadratic form on complex columns by splitting real and imaginary parts.
`Feasible.terminal_nonpos` evaluates the terminal matrix at ξ=1 and uses state
symmetry to cover the whole CZ target orbit. `Feasible.weak_duality` integrates
the resulting drift inequality along every successful pulse, proving
W(x₀) ≤ exposure. `Feasible.le_Cstar` bounds the infimum over pulses as well.
These results do not assume abstract feasibility, any of the four general
completeness inputs, or finiteness/attainment of the physical optimum.

`ConcreteStationary.optimum d` is the extended-real supremum over the concrete
order-d feasible set, not an alias for `Lunsplit d`. The proved bounds are
`Lunsplit d ≤ optimum d ≤ Cstar` for every d and `0 ≤ optimum d` for d≥1.
`stationary_convergence` squeezes this sequence between `Lunsplit` and the
constant `Cstar`, transferring stationary convergence with exactly the four
existing explicit inputs: controllability, superposition, first-derivative
polynomial approximation, and matrix positivity representation. No new
external input, reverse feasible-set inclusion, or monotonicity assumption
is needed. `ConcretePartitioned.fixed_partition_convergence` supplies the
partitioned result below. This theorem states convergence in the extended-real
topology; the later finiteness and epsilon theorems give the finite-real
conclusion. Attainment of the physical optimum is not asserted.

`ConcreteStationary.Feasible.mono` separately proves concrete degree nesting
for every d≤e, preserving the same W. `sector_mono` and `retained_mono` ensure
that the old columns and charges persist. Old matrices are zero-padded into
the larger sectors; newly retained charges receive zero matrices. Exact Gram
padding preserves the drift identity. The terminal constant is represented
by `constantGram e`, using the terminal sign already proved from the source
certificate. No abstract-feasibility conversion is used. `optimum_mono` then
proves that the concrete optimal-value sequence is nondecreasing, without
any of the four completeness inputs. The audit checks order-zero and skipped-
order transport, successor monotonicity, and a monomial at the sector degree
boundary.

`ConcretePartitioned.Feasible` defines finite real-matrix constraints for
every cell, interior interface, and terminal restriction. The occupation
cone uses degree-d face columns plus ξ(1-ξ) times full normal columns of
degree d-1. Interface columns exclude ξ and both control coordinates.
The terminal cone has both univariate Gram blocks of orders d and d-1.
All drift/interface identities use the normalization quotient. The redundant
scalar squared-magnitude interval family is represented by the full Gram
blocks, following the manuscript's absorbed-diagonal formulation; separate
equivalence to archived coefficient data is not asserted. Order zero keeps
the existing truncated natural-number d-1 convention.

The definition uses Appendix E's W sign: next-cell W at ξ=0 minus previous-
cell W at ξ=1 is in the interface cone, and -τW is in the terminal cone for
every cell. `ConcretePartitioned.of_stationary` embeds any concrete stationary
certificate at the same order by using identical cells and zero interval
and interface witnesses. It is algebraic and imposes no U positivity or
successful-pulse hypothesis.
The audit distinguishes full from face columns, excludes ξ/u/ū from interface
columns, exercises a nonzero terminal interval block, checks the interface
orientation, and verifies the zero certificate on arbitrary partitions.

`ConcretePartitioned.Feasible.weak_duality` proves that the initial value is
a lower bound for every successful pulse with exposure strictly below U.
The proof evaluates the real positive matrices on complex columns, makes
the normalization relations vanish on physical states and unit controls,
and uses ξ(1-ξ)≥0 on the closed cell interval. The terminal substitution is
transported to every target state by the certificate's symmetry.
`split_weak_duality_of_nonneg` contains the shared integration argument for
pointwise drift, interface, and terminal inequalities; the original abstract
`split_weak_duality` and `cell_step` keep their signatures and are wrappers.
No conversion to abstract SOS feasibility or external completeness input is
used for concrete soundness.

`ConcretePartitioned.Feasible.le_Cstar` further bounds the physical infimum
provided an explicitly supplied successful pulse has exposure below U.
This witness also bounds pulses at or above U, and is not constructed here.
The audit checks the axiom dependencies, endpoint/all-target terminal bounds,
rejection of a polynomial negative only inside the interval, and a valid
interval polynomial that is negative outside it.

`ConcretePartitioned.optimum P U d` is the extended-real supremum of initial
values over the concrete partitioned feasible set, not an alias for the
abstract optimum. `stationary_le_optimum` embeds the concrete stationary
optimum at the same order, including order zero and arbitrary U.
`optimum_nonneg` gives nonnegativity for d≥1 without a pulse witness;
`optimum_le_Cstar` requires a successful pulse with exposure strictly below U.
`fixed_partition_convergence` squeezes this sequence between the concrete
stationary sequence and Cstar. It retains exactly the four explicit general
inputs and the successful-below-ceiling witness. No reverse feasible-set
equivalence or partitioned degree monotonicity is used in that convergence proof.
The audit checks all four new theorem dependencies, the initial-value
objective, order-zero stationary inclusion, and the distinct hypotheses
for the lower and upper bounds.

`ConcretePartitioned.Feasible.mono` separately transports every concrete
partitioned certificate from d to any e≥d, preserving all cell polynomials.
`GramCone.mono` pads existing charge sectors and gives new charges zero
matrices, preserving the exact polynomial modulo normalization. Both the
face/full occupation bases and the state-only interface bases are nested.
`terminalGram_pad` preserves the full univariate polynomial, and
`TerminalCone.mono` applies it to both terminal blocks (orders d and d-1).
This is not the constant-terminal shortcut used for stationary certificates.
`optimum_mono` proves nondecreasing concrete optimal values for arbitrary
P and U, including order zero, without a pulse witness or any of the four
completeness inputs. The audit covers skipped-order transport, successor
monotonicity, a nonzero interval block transported from order zero to four,
and the interface degree boundary. Full archived-program correspondence
remains separate work.

`ConcretePartitioned.shifted n V = -C n - V` now implements the manuscript's
shared offset exactly. Applying this conversion twice returns V, preserves
every degree bound (including zero), and preserves G-invariance. Its drift
is -L V; interface differences reverse sign with the shared constant
cancelled; its negative terminal restriction is τV+n. Evaluation gives
the objective -n-V₀(0,x₀).
`PotentialFeasible` states the V,n constraints independently over the same
concrete real matrix cones. `feasible_shifted_iff` and
`potential_shifted_iff` prove both directions for any offset n.
`potentialOptimum` explicitly optimizes over n and V, and
`potentialOptimum_eq` proves equality with the W optimum at every order,
without a pulse witness or completeness input. The audit includes a
nonzero offset, asymmetric neighboring potentials, constant cancellation
at order zero, and transfer of optimum monotonicity.

`GramCone.monomial_kept` represents a nonnegative scalar times a monomial's
squared magnitude by a diagonal entry, cancelling reflection rephasing
exactly. `partner_squared` proves equality of the squared magnitudes for
opposite charge representatives as polynomials; `fullBasis_partner` retains
the same degree and normal form. `GramCone.monomial` therefore covers any
normal support monomial, not only those in retained charge sectors.
`GramCone.scalar_family` sums finite nonnegative families, allowing repeated
squared magnitudes. `OccupationCone.absorb_scalar_family` adds their
matrices to the full degree-(d-1) interval blocks, leaving the face block
and order unchanged. `occupation_iff_with_scalar_family` proves equality
with the cone extended by any prescribed allowed finite scalar family;
the reverse inclusion chooses zero weights. No physical-domain inequality
is substituted for the polynomial identities, and no completeness input
or pulse witness is used. The audit exercises zero charge, odd control
parity with opposite charges and unequal weights, rejection of negative
constants, and absorption into an existing occupation certificate.
Serialized archive correspondence remains separate work.

Finiteness can use a supplied successful `Pulse` without geometric inputs.
`Cstar_finite` excludes both extended-real infinities, and `coe_Cstar_toReal`
justifies conversion to a real number. Neither needs a completeness input.
`polynomial_certificates_epsilon` supplies a certificate with initial value
strictly greater than `Cstar.toReal - ε` at an order at least one, conditional
on the same four general inputs. Both concrete modules prove `optimum_finite`
for positive orders and `optimum_epsilon`: for every positive ε, all orders
beyond some D ≥ 1 satisfy `0 ≤ Cstar.toReal - optimum.toReal < ε`.
The partitioned results retain the successful-pulse-below-U hypothesis.
The transitive audit covers these declarations.

`BallBoxSteering.nonempty_pulse_of_ballBox` now derives successful-pulse
existence from the accepted `CompactRegularLevelBallBox` input alone.
Local steering extends reachability along a continuous curve: the reachable
parameter set and its complement are open, so connectedness of the real
line makes every parameter reachable. The curve
`mkState 1 0 (exp (t * I)) 0` connects x₀ at t=0 to an exact CZ target at
t=π. This is only a geometric connectivity witness, not a zero-exposure
physical trajectory. The resulting finite disk-control segment is converted
to unit control by the previously checked active-time construction.
`Cstar_finite_of_ballBox` therefore needs no separately supplied pulse.
The polynomial and concrete stationary epsilon APIs likewise no longer
take a pulse argument; their four general inputs are unchanged.
Partitioned bounds still require a pulse below the specified ceiling U;
existence alone supplies no bound for an arbitrarily chosen U.
No superposition input is used for pulse existence or physical finiteness.
The superposition input still includes unformalized current identification
and measurable decomposition existence; its local directional implication
is proved next.

`PolarAlignment.lean` proves the directional part of the superposition
bridge. `EuclideanCurrentArcData.CurrentIdentity` records the discarded
remainder's unit direction, the full vector identity against bounded
measurable vector fields, and measurability of the ensemble pairing.
It does not assume tangent alignment or zero directional deficit.
`CurrentIdentity.isDirected` tests against the parent's polar direction,
modified to zero off its unit-norm set so that the test is globally bounded.
The remainder's pairing cannot exceed its mass. Scalar mass preservation
then forces the nonnegative arc deficits to integrate to zero, first over
the ensemble and then along almost every arc. Equality of unit vectors
follows from the Euclidean inner-product identity. Localized mass and
subcurrent domination transport the parent's exceptional null set to arcs.

`EuclideanCurrentSuperposition.directed` converts the new source-shaped
existence hypothesis into the existing directed-superposition input.
`PolarAlignmentAudit.lean` checks this bridge transitively against the
standard-axiom allowlist and applies it to stationary epsilon bounds and
fixed-partition convergence, retaining the latter's ceiling witness.
No new axiom is introduced. `length_integrable_and_integral` derives finite
mean arc length from `LocalizedMeasureDecomposition`; its integral equals
the retained vector variation. `mass_identity` combines this with subcurrent
additivity, retaining the discarded remainder's mass. Both former assumed
fields are removed. `CurrentIdentity.pairing_integrable` derives integrability
by bounding the absolute signed pairing by arc length, so the former
integrability field is weakened to measurability alone. The dependency audit
covers these deductions and the downstream convergence applications.
Current representation, decomposition existence, the remainder direction,
and the vector identity remain supplied inputs. Ensemble-pairing measurability
is derived from a supplied measurable arc realization as described next;
existence of that realization remains external. Existing final APIs and
their original explicit inputs are unchanged.

`MeasurableArcs.pairing_measurable` now derives the ensemble-test
measurability from jointly measurable arc positions and tangents that are
derivatives almost everywhere. No directional alignment is assumed.
The proof uses the measurable real component mass as an almost-everywhere
version of arc length, integrates a measurable variable-interval indicator,
and transfers equality back to the actual arcs. Tests may be unbounded:
this lemma proves measurability, not finite integrability for arbitrary tests.
`MeasurableArcs.of_continuous` constructs the tangent data from jointly
continuous positions on a second-countable Borel parameter space, using
mathlib's derivative-with-parameters theorem.
`CurrentIdentity.of_measurableArcs` fills the original pairing-measurability
field from this data; it still requires the remainder direction and vector
identity. These are sufficient conditions, not a claim that the current
arbitrary curve-class ensemble already has such a realization. Constructing
that realization from the cited decomposition remains external, and the
existing general superposition hypothesis is not silently strengthened.

S1 of the superposition proof is implemented in `ArcCurrent.lean`. Every
existing `EuclideanArc` defines an oriented vector measure. Its measurable
tangent field is obtained by extending the parameter derivative through the
embedded compact interval; the simple-arc injectivity hypothesis prevents
cancellation from repeated visits. `vectorCurrent_apply` identifies its value
on each measurable region with the parameter integral of the tangent over
the preimage, and `vectorCurrent_eq_map` proves the equivalent vector-measure
pushforward formula. `vectorCurrent_variation` is equality with the entire
length measure, not just its total mass. Compact support and total mass equal
to arc length follow. `boundary` proves integrability and the oriented endpoint
identity for every smooth compactly supported test function, using absolute
continuity and the chain rule almost everywhere, without assuming a C¹ arc.
`toNormalCurrentData` fills the existing normal-current record with terminal
and initial Dirac measures; `action_eq` identifies its action with the oriented
line integral. The arc audit checks translated straight segments with arbitrary
unit directions and positive lengths, local mass, the boundary sign, and
transitive standard-axiom dependencies. This constructs the current of a
supplied single arc, not a measurable family or a decomposition of an arbitrary
current.

S2 is implemented in `ArcSpace.lean`: a concrete space of positive-length,
simple unit-speed Lipschitz arcs with constant tails, with the subspace topology
of length times compact-open path space and its Borel measurable structure.
Every existing `EuclideanArc` has a stopped representative; this preserves its
path on the parameter interval, length measure, and oriented vector current.
Length, joint evaluation, and both endpoints are continuous; the parameter
derivative is jointly measurable. The arc's length measure, vector-current
evaluation on each measurable region, and pairing with any measurable vector
field depend measurably on the arc. No integrability against an arbitrary
ensemble is asserted. `measurableArcs` fills the existing realization interface
for any measurable family taking values in this space, without assuming that
the family is continuous. The arc audit includes both constant tails,
preservation of local mass, and a discontinuous two-arc family, and checks the
transitive axioms of all new proof-bearing APIs.

This does not construct a measure decomposing an arbitrary current, prove a
measurable selection from curve equivalence classes, or assert that the arc
space is Polish or closed under limits.

S3 is implemented in `CycleRemoval.lean` for the existing
`EuclideanNormalCurrentData` model. `exists_acyclic_subcurrent` constructs a
normal subcurrent with exactly the same `boundaryPlus` and `boundaryMinus`,
no nonzero normal subcurrent with zero distributional boundary, and the local
measure identity `variation (T - S) + variation S = variation T`. In
particular, compact support is inherited. This is an existence proof, not a
new assumed cycle-removal interface. It uses Hilbert projection on the closed
convex set of L² densities between zero and one preserving all smooth compact
boundary tests. The auxiliary L² objective does not change physical `Cstar`.
`subcurrent_density` proves that every normal subcurrent has a scalar density
in the parent's polar direction, using Radon--Nikodym and equality in the
variation triangle inequality; the no-cycle conclusion is therefore not
restricted to an assumed density representation. The original finite boundary
measures need not be Jordan parts. No arc decomposition, metric-current
identification, or new axiom is used. The arc audit tests total removal when
the boundary measures coincide, preservation of a nonzero tested boundary,
support inheritance, and standard transitive axioms.

S4 has preliminary compactness results in `ArcCompactness.lean`, but its
decomposition existence theorem is not proved. `StoppedPathSpace` is a closed
space of stopped 1-Lipschitz paths allowing zero duration, constant paths,
and repeated visits. Duration is not identified with geometric length.
Bounded-duration paths in a fixed compact spatial set form a compact set.
A common bound on the first duration moment implies tightness of supplied
ensembles; Prokhorov then gives compactness of their closure for probability
ensembles. Fixed initial and terminal laws are closed under these limits.
The existing arcs embed continuously without changing their paths or duration.
The audit checks zero-duration and constant paths, both sides of a duration
cutoff, and the standard-axiom dependency allowlist.

The finite combinatorial decomposition is proved in
`FinitePathDecomposition.lean`. `FiniteRouting.exists_decomposition` takes
only nonnegative edge weights on a finite vertex type and absence of directed
cycles in the positive-edge relation. It constructs a finite list of weighted
walks: all weights are nonnegative, every positive-weight walk has distinct
vertices and uses positive edges, and its endpoints lie at a net source and
a net sink. Initial and terminal weighted sums equal the positive and negative
parts of outgoing-minus-incoming flow. The additive edge ledger holds for
every real edge cost, so it preserves each individual edge and any assigned
edge-length sum. `Flow.ofAcyclic` derives a decreasing natural-number height
by counting reachable vertices; a topological ordering is not an additional
input. Zero-weight terms may be discarded. The arc audit includes an
asymmetric split/merge graph with internal source/sink vertices, reverse-edge
zero usage, nonuniform edge costs, and a zero-throughput graph.

`PolygonalRealization.lean` constructs the geometric paths explicitly from
constant paths, arc-length-parametrized straight segments, and concatenation.
`Walk.realize` preserves both endpoints, is globally 1-Lipschitz with constant
tails, has duration equal to the sum of Euclidean edge lengths, and has unit
speed away from finitely many corners (hence almost everywhere on its duration
interval). These properties hold without assuming geometric simplicity;
coincident consecutive positions contribute zero duration.

For simplicity, `StraightEmbedding` explicitly requires injective vertex
positions, no vertex on a nonincident edge, and intersection of distinct
undirected edges only at common vertices. `realize_injOn` derives injectivity
of the entire realized simple graph path from these local geometric conditions.
`Flow.geometric_arc` constructs an actual `EuclideanArc` for each positive
term of the finite decomposition. `Flow.geometric_length_ledger` proves the
weighted sum of durations equals the original edge-flow-weighted Euclidean
length sum. The audit checks unequal edge lengths, values at and after a join,
both stopped tails, a retracing counterexample to unconditional simplicity,
and a concrete nondegenerate single-edge embedding. No construction of a
noncrossing subdivision of arbitrary intersecting segments is asserted.

These results do not yet construct ensembles representing an arbitrary
Euclidean normal current or prove uniform integrability of duration-weighted
tails. Remaining S4 work includes identifying the realized arcs' local vector
currents with the oriented edge-current sums, constructing compatible embedded
polyhedral approximations, passage of current and mass identities to the limit,
and recovery of simple unit-speed arcs using acyclicity. The embedding
conditions must be proved for those approximations, not supplied as a new
external superposition assumption. Neither finite geometric realization nor
compactness alone proves the required continuous-current decomposition.

S4--S6 (existence of an acyclic arc decomposition, the remaining current
identities, and discharge of `EuclideanDirectedArcSuperposition`) remain
unfinished. Appendix E convergence still depends on the superposition input.
