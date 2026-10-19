# Formalization status

This is an incomplete formalization. None of the seven requested main declarations has yet been
proved. Challenge contains their exact statements; Solution exports only proved foundations.
The main comparator must fail while those declarations are absent.

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

These modules contain no proof holes or custom axioms. The main analytic dependencies below are
not consequences already obtained from these foundations.

## Remaining proof chain

1. Extend the proved weighted-area normalization and radial distribution to the angular
   integration API needed below.
2. Prove that positive supersolutions of a divergence operator with radial coefficients have
   decreasing circle averages after increasing concave truncation.
3. Prove the moving-truncation distribution inequality, including strict levels and passage to
   the boundary.
4. Verify the differential identity for the weighted kernel and differentiate under the input
   integral.
5. Construct the positive radial normalizer; prove its boundary-circle change of variables,
   monotonicity, and exact beta/gamma limit.
6. Combine these to obtain the sharp positive weighted upper bound.
7. Prove annular concentration, Fatou passage, and the matching positive lower bound.
8. Prove reproduction for the explicit weighted kernel, the complex lower bound one, and the
   additional boundary-column lower bound for nonnegative parameters.
9. Deduce the unweighted identities by specializing the weighted results at zero.
10. Develop the conformal covariance and reproducing-kernel bridges for domains. The pinned
    mathlib's Riemann mapping file still contains only partial results.
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
