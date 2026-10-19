# Bergman weak type constants

A Lean 4 project, dependent on mathlib, for sharp weak type estimates of Bergman projections.

**All seven main statements are proved in Lean:** both sharp disk constants, the sharp positive
weighted constant, all stated complex weighted upper and lower bounds, and the characterization
of disks among bounded simply connected domains. The proofs use only the standard permitted
Lean axioms. Full comparator verification of this final development is pending; the project is
not registered on Palomar.

## Mathematical targets

We use normalized planar area and its standard radial weights:

$$
\mathbb D=\{z\in\mathbb C:|z|<1\},\qquad
dA=\frac{dx\,dy}{\pi},\qquad
dA_\alpha=(\alpha+1)(1-|z|^2)^\alpha dA,\quad\alpha>-1.
$$

The complex projection and its positive majorant are

$$
P_\alpha f(z)=\int_{\mathbb D}
\frac{f(w)}{(1-z\overline w)^{\alpha+2}}\,dA_\alpha(w),\qquad
P_\alpha^+f(z)=\int_{\mathbb D}
\frac{|f(w)|}{|1-z\overline w|^{\alpha+2}}\,dA_\alpha(w).
$$

The complex power uses the analytic branch normalized at zero. The positive operator is defined
as an extended nonnegative integral; its finiteness for integrable inputs at interior points is
proved. The optimal weak constant is the infimum of all constants in the strict-superlevel
inequality (with the nonnegative output itself for the positive operator)

$$
\lambda A_\alpha\{|Tf|>\lambda\}
\le C\int_{\mathbb D}|f|\,dA_\alpha,\qquad \lambda>0.
$$

The requested targets, all retained in the comparator configuration, are:

1. **Unweighted disk:** both weak constants are one.

   $$C_0=C_0^+=1.$$

2. **Standard radial weights:**

   $$
   D_\alpha=\frac{\Gamma(\alpha+1)}{\Gamma(1+\alpha/2)^2},\qquad
   C_\alpha^+=D_\alpha,\qquad 1\le C_\alpha\le D_\alpha
   \quad(\alpha>-1).
   $$

   The additional complex lower bound has the source's narrower parameter range:

   $$
   C_\alpha\ge\frac{\alpha+1}{\alpha+2}D_\alpha\quad(\alpha\ge0).
   $$

   Together the two lower bounds give their maximum. No exact complex weighted constant is
   asserted for general nonzero parameters. These are standard radial weights, not arbitrary
   Békollé–Bonami weights.

3. **Domain rigidity:** for every bounded, open, simply connected planar domain,

   $$
   C_\Omega^+=1\quad\Longleftrightarrow\quad
   \Omega\text{ is a Euclidean disk}.
   $$

   There are no boundary regularity or conformal derivative bounds. The weak constant may be
   infinite. Translation and dilation cannot distinguish a particular center or radius. The
   formal statement quantifies over kernels satisfying the usual holomorphic, Hermitian, L²
   reproducing properties. Kernel existence, uniqueness, conformal covariance, and the
   compact-interior cancellation argument are proved as supporting results.

The unrestricted statement about all simply connected regions is false: the upper half-plane
also has positive weak constant one. Boundedness is the agreed scope of the formal target.

## Current checked development

The library defines the actual integral kernels, measures, operators, weak type bounds, and their
optimal constants. Completed lemmas include disk and weighted-area normalization, kernel nonvanishing,
pointwise complex-to-positive domination, kernel integrability and positive-output finiteness,
the parameter-zero specializations, weak-constant comparison, and test-function lower bounds.
It also proves the lower bound one for the explicit complex weighted projections, for both disk
operators, and for a domain equipped with its reproducing Bergman kernel and finite positive area.
The sharp disk upper bound follows from the actual normalized kernel's Poisson supermean
inequality, decreasing circular truncations, finite differences, and polar integration.
The weighted proof now includes the kernel differential inequality, radial normalizer,
decreasing truncated averages, the sharp upper bound, and admissible annular inputs attaining
the lower bound. The complex boundary lower bound uses genuine interior concentration and a
proved boundary-cap asymptotic. The bounded-domain characterization uses genuine conformal
covariance, uniform cancellation on a compact interior set, an integrable perturbation witness,
and translation/dilation for the converse.

See [the development status](docs/STATUS.md), [the weighted proof](docs/weighted-estimates.md),
and [the bounded-domain proof](docs/domain-rigidity.md). The proof notes are mathematical source
material, not Lean certificates. No claim of literature priority is made.

## Build and verification

The project pins Lean `v4.35.0-rc2` and mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```sh
lake exe cache get
lake build BergmanWeakType
lake build Challenge Solution
python3 scripts/check-proof-holes.py
python3 scripts/check-comparator-targets.py
```

The Challenge intentionally contains statement holes. Solution exports the complete proofs of
all seven statements. The proof-hole scan is only a source check; the comparator independently
checks the proof closures and agreement with Challenge.

On Linux, run the actual comparator, including the independent kernels, with:

```sh
./scripts/verify-comparator.sh
```

The configuration includes all seven targets and permits only `propext`, `Quot.sound`, and
`Classical.choice`. It neither permits `sorryAx` nor replaces mathematical definitions with
comparison holes. GitHub Actions runs the library build and the main-theorem check separately.
The historical supplementary configuration `comparator.completed.json` now also contains all
seven declarations; the canonical full-project configuration remains `comparator.json`.
The earlier three-result milestone at commit `061dc8796e789fa4c716c994cbadfce716d4e470`
[passed comparison and all three kernels](https://github.com/CoolRmal/bergman-weak-type/actions/runs/39195499666/job/117877271189).

The official Palomar full-preflight workflow is also installed. Palomar submission remains
pending verification of an exact public commit and its required
human review and registration decisions.

## License

Apache-2.0. See [LICENSE](LICENSE).
