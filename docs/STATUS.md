# Formalization status

All seven requested main declarations are proved:
`BergmanWeakType.projection_constant_eq_one`,
`BergmanWeakType.positiveProjection_constant_eq_one`,
`BergmanWeakType.weightedPositiveProjection_constant_eq`,
`BergmanWeakType.one_le_weightedProjection_constant`,
`BergmanWeakType.weightedProjection_constant_le` for every parameter greater than −1, and
`BergmanWeakType.boundaryConstant_le_weightedProjection_constant` for nonnegative parameters, and
`BergmanWeakType.positive_constant_eq_one_iff_disk` for bounded simply connected domains.
Challenge specifies their exact statements independently; Solution exports the complete proofs.

## Completed foundations

| Module | Content |
| --- | --- |
| `Definitions` | Disk, normalized and weighted area, actual integral kernels and operators, weak type constants, numerical constants |
| `Measure` | Disk and weighted probability normalization, radial distribution, support, positive interior-ball mass |
| `Kernel` | Nonvanishing denominators, branch domain, norm identities, pointwise domination, parameter-zero identities |
| `KernelIntegrability` | Uniform kernel bounds, measurable integrands, integrability, finiteness of positive outputs |
| `WeakType` | Monotonicity, comparison, upper bounds from distribution estimates, lower bounds from test inputs |
| `Comparison` | Complex-to-positive comparison of the actual optimal constants and zero-parameter specialization |
| `Domain` | Standard reproducing-kernel characterization and the domain's positive integral operator |
| `RigidityWitness` | Ratio lower bound and strictness from an input whose output is at least one |
| `DomainLowerBound` | Constant reproduction and the lower bound one on domains of finite positive area |
| `CompactGap` | Uniform relative separation of continuous functions on a compact parameter set |
| `Reproduction` | The universal complex weighted lower bound one via ordinary shrinking-disk inputs; unweighted and positive lower bounds |
| `Weighted/MovingCap` | Integral estimates from finite differences or interior derivatives, without endpoint regularity |
| `Weighted/SmoothCap` | Nonnegative smooth truncation, first and second derivatives, concavity, and tangent bounds |
| `Weighted/PoissonCap` | Poisson extension, preservation of supermean inequalities under truncation, decreasing truncated circle averages |
| `Weighted/KernelPDE` | Exact coordinate derivatives and elliptic defect of the weighted kernel |
| `Weighted/CompactIntegral` | Continuity and differentiation under compact dominated integrals |
| `Weighted/BetaIntegral` | Real beta integral and the sine-power gamma evaluation |
| `Weighted/Normalizer`, `Weighted/CircleMobius`, `Weighted/NormalizerEndpoint` | Boundary normalizer, genuine Möbius substitution, sharp gamma bound, and endpoint limit |
| `Weighted/DiskSupermean`, `Weighted/DiskPotential` | Poisson supermean inequality for the actual normalized disk kernel and its integral potential |
| `Weighted/DiskCap`, `DiskSharp` | Measurable circular truncations, sharp distribution bound, and both sharp disk constants |
| `Rigidity/RiemannMapping`, `Rigidity/UnitDiscShift` | Full Riemann mapping theorem, adapted from the upstream mathlib contribution below |
| `Rigidity/AnalyticInverse` | Holomorphic inverses and nonzero derivatives; paired biholomorphic Riemann maps |
| `Rigidity/ChangeOfVariables` | Complex Jacobian and normalized-area substitution for holomorphic injections |
| `Rigidity/PolarIntegral` | Disk integration through circle averages, including squared-radius substitution |
| `Weighted/PolarKernel`, `Weighted/PolarPotential` | Exact polar derivatives and differential inequalities under the source integral |
| `Weighted/AngularMean`, `Weighted/RadialFlux`, `Weighted/PolarCap`, `Weighted/QuotientCap` | Divergence inequality, smooth truncations, exact truncated-mean monotonicity |
| `Weighted/NormalizerRadial`, `Weighted/WeightedPotential` | Genuine normalizer ODE and normalized actual weighted potentials |
| `Weighted/AnnulusMeasure`, `Weighted/RadialKernel`, `Weighted/AnnularSharpness` | Admissible annular inputs attaining the sharp positive weighted lower bound |
| `Weighted/MassCoordinate`, `Weighted/RadialLevel`, `WeightedSharp` | Weighted mass substitution, distribution estimates, sharp positive constant and complex upper bound |
| `Rigidity/DiskReproducing`, `Rigidity/KernelTransform` | Actual disk reproduction, kernel existence and uniqueness, conformal covariance |
| `Rigidity/IntegralPhase`, `Rigidity/PhaseRigidity`, `Rigidity/MobiusGeometry` | Equality in the triangle inequality and the resulting disk or unbounded Möbius geometry |
| `Rigidity/DomainGap`, `Rigidity/Perturbation` | Uniform cancellation on a compact interior set and an actual integrable perturbation witness |
| `Boundary/Sharpness` and its dependencies | Genuine interior concentration, boundary-column lower bound, half-disk beta integral, and boundary-cap asymptotic |
| `Rigidity/DiskSimilarity`, `Rigidity/BoundedRigidity` | Similarity transfer of the sharp disk bound and the full bounded-domain equivalence |

These modules contain no proof holes or custom axioms.

## Verification status

All proof obligations are discharged locally. Each main theorem's dependency closure was checked
to use only `propext`, `Classical.choice`, and `Quot.sound`. Full Linux comparator verification of
the final development and the official Palomar preflight are pending.

See the accompanying proof notes for the actual analytic arguments and parameter restrictions.
No proof step is replaced by an extra axiom, a hypothesis asserting the target bound, or a
different definition of the Bergman operator.

## Completion gates

- All seven configured declarations must exist in Solution with the exact Challenge statements.
- Their entire dependency closures must use only the permitted standard axioms.
- The real comparator and the official full Palomar preflight must pass for the public commit.
- Metadata must distinguish completed proofs from targets and source-prose arguments.
- Palomar intake and registration must follow its required concrete human decisions.

The three-result milestone at commit `061dc8796e789fa4c716c994cbadfce716d4e470`
[passed the comparator and Lean, NanoDa, and con-ron kernels](https://github.com/CoolRmal/bergman-weak-type/actions/runs/39195499666/job/117877271189).
That earlier commit still lacked four declarations. The final seven-target run is pending.
There has been no Palomar review or registration.

## Upstream proof attribution

The full Riemann mapping theorem and disk shifts were adapted from Yury Kudryashov's
[mathlib PR 33505](https://github.com/leanprover-community/mathlib4/pull/33505), at commit
`d43061d911b1aeae0788591da437a3b115098962`. Their original authorship and Apache-2.0 notices
are retained in the files. They are supporting results, not original Bergman theorems.
