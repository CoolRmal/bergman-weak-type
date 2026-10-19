# Bergman weak type constants

A Lean 4 project, dependent on mathlib, for sharp weak type estimates of Bergman projections.

**Work in progress. The main theorems are stated but not proved. The project has not passed the
comparator and is not registered on Palomar.** The checked library contains foundational results;
a successful library build is not completion of the statements in `Challenge.lean`.

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
inequality

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
   reproducing properties. The existence and identification of that kernel are also pending
   analytic milestones, not axioms added to mathlib.

The unrestricted statement about all simply connected regions is false: the upper half-plane
also has positive weak constant one. Boundedness is the agreed scope of the formal target.

## Current checked development

The library defines the actual integral kernels, measures, operators, weak type bounds, and their
optimal constants. Completed lemmas include disk and weighted-area normalization, kernel nonvanishing,
pointwise complex-to-positive domination, kernel integrability and positive-output finiteness,
the parameter-zero specializations, weak-constant comparison, and test-function lower bounds.
It also proves the lower bound one for a domain equipped with its reproducing Bergman kernel and
finite positive area. These results do not prove the sharp upper estimates or disk rigidity.

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

The Challenge intentionally contains statement holes. Solution currently exports completed
foundations and does not supply the missing main theorems. The proof-hole scan is only a source
check; it cannot establish that a theorem exists or has the intended statement.

On Linux, run the actual comparator, including the independent kernels, with:

```sh
./scripts/verify-comparator.sh
```

**This comparison is expected to fail until every selected main theorem is implemented.** Its
configuration includes all seven targets and permits only `propext`, `Quot.sound`, and
`Classical.choice`. It neither permits `sorryAx` nor replaces mathematical definitions with
comparison holes. GitHub Actions runs the library build and the main-theorem check separately.

The official Palomar full-preflight workflow is also installed. Palomar submission remains
pending proof completion, passing verification of an exact public commit, and its required
human review and registration decisions.

## License

Apache-2.0. See [LICENSE](LICENSE).
