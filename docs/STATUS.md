# Formalization status

This is an incomplete formalization. Three of the seven requested main declarations are proved:
`BergmanWeakType.projection_constant_eq_one`,
`BergmanWeakType.positiveProjection_constant_eq_one`, and
`BergmanWeakType.one_le_weightedProjection_constant` for every parameter greater than −1.
The other four remain unproved. Challenge contains their exact statements; Solution exports
the completed results and foundations. The full comparator must fail while declarations are absent.

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

These modules contain no proof holes or custom axioms. The main analytic dependencies below are
not consequences already obtained from these foundations.

## Remaining proof chain

1. Extend the proved disk polar integration to the weighted angular integration API.
2. Prove that positive supersolutions of a divergence operator with radial coefficients have
   decreasing circle averages after increasing concave truncation.
3. Apply the proved finite-difference moving-truncation inequality to the weighted normalization.
4. Verify the differential identity for the weighted kernel and differentiate under the input
   integral.
5. Use the completed positive radial normalizer, sharp bound, and beta/gamma endpoint limit.
6. Combine these to obtain the sharp positive weighted upper bound.
7. Prove annular concentration, Fatou passage, and the matching positive lower bound.
8. Prove the additional boundary-column lower bound for nonnegative parameters. The universal
   complex lower bound one is already proved by interior concentration, without requiring
   constant reproduction for the explicit weighted kernel.
9. The unweighted identities are already proved directly through Poisson supermean inequalities.
10. Develop the conformal covariance and reproducing-kernel bridges for domains. The complete
    Riemann mapping theorem and its biholomorphic upgrade are now available locally.
11. Prove strict cancellation on a fixed interior set, uniformly over the closed parameter disk,
    and construct the compact-interior perturbation input. Apply `RigidityWitness`.
12. Prove the disk direction by translation and dilation; complete the exact bounded-domain
    equivalence in Challenge.

See the accompanying proof notes for the actual analytic arguments and parameter restrictions.
No missing step may be replaced by an extra axiom, a hypothesis asserting the target bound, or a
different definition of the Bergman operator.

## Completion gates

- All seven configured declarations must exist in Solution with the exact Challenge statements.
- Their entire dependency closures must use only the permitted standard axioms.
- The real comparator and the official full Palomar preflight must pass for the public commit.
- Metadata must distinguish completed proofs from targets and source-prose arguments.
- Palomar intake and registration must follow its required concrete human decisions.

At this stage there is no successful main-theorem comparison, Palomar review, or registration.

## Upstream proof attribution

The full Riemann mapping theorem and disk shifts were adapted from Yury Kudryashov's
[mathlib PR 33505](https://github.com/leanprover-community/mathlib4/pull/33505), at commit
`d43061d911b1aeae0788591da437a3b115098962`. Their original authorship and Apache-2.0 notices
are retained in the files. They are supporting results, not original Bergman theorems.
