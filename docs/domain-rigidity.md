# Positive Bergman weak constant and disk rigidity

This document records a mathematical proof to be formalized. It is not a claim that Lean has checked the analytic arguments below.

The agreed formalization target is the characterization among all bounded simply connected planar domains, without derivative bounds. The argument below also establishes the stronger finite-area version. The correct geometric conclusion is a Euclidean disk, up to translation and dilation. The weak constant cannot specify its radius or center. The upper half-plane is a simply connected nondisk with the same positive weak constant one, so a theorem over unrestricted simply connected domains would be false.

## Statement and conventions

Use the same normalized planar area on every domain:

$$
dA=\frac{dx\,dy}{\pi},\qquad A(E)=\int_E dA.
$$

Let the following be a nonempty, open, connected, simply connected planar domain of finite area:

$$
\Omega\subset\mathbb C,\qquad 0<A(\Omega)<\infty.
$$

Its Bergman kernel is normalized relative to this area measure. For a nonnegative integrable input, define the positive operator as an extended nonnegative integral, and its sharp distributional weak constant by

$$
P_\Omega^+f(a)=\int_\Omega |K_\Omega(a,w)|f(w)\,dA(w),
$$

$$
C_\Omega^+
=\sup_{\substack{f\ge0,\ 0<\|f\|_{L^1(\Omega)}<\infty\\\lambda>0}}
\frac{\lambda A\{a\in\Omega:P_\Omega^+f(a)>\lambda\}}
{\|f\|_{L^1(\Omega)}}\in[0,\infty].
$$

This is also the constant for the linear positive-kernel operator on complex inputs, wherever its integral is defined, and for its sublinear majorant with the absolute value of the input inside the integral. The pointwise triangle inequality proves that restricting to nonnegative inputs does not change the constant.

**Theorem.** Assuming the sharp positive disk endpoint inequality,

$$
\boxed{C_\Omega^+=1\quad\Longleftrightarrow\quad
\exists b\in\mathbb C\ \exists R>0:\ \Omega=B(b,R).}
$$

In particular, this covers every bounded simply connected planar domain, without boundary regularity or bounds on a conformal derivative. The statement allows the weak constant of a nondisk to be infinite; it does not assert weak-type boundedness on every such domain.

## Uniform cancellation on a fixed interior set

Assume that the domain is not a Euclidean disk. The Riemann mapping theorem supplies a conformal bijection

$$
\phi:\mathbb D\longrightarrow\Omega,\qquad q=\phi'.
$$

Fix an interior radius and its image:

$$
0<r<1,\qquad E=\phi(r\mathbb D).
$$

This set has positive area and compact closure in the domain. For a parameter in the closed unit disk, define

$$
B_\zeta(w)=\frac{q(w)}{(1-\zeta\overline w)^2},
\qquad |\zeta|\le1,\quad |w|<r,
$$

$$
J(\zeta)=\int_{r\mathbb D}|B_\zeta(w)|\,dA(w),
\qquad
I(\zeta)=\int_{r\mathbb D}B_\zeta(w)\,dA(w).
$$

Both functions are continuous on the closed unit disk. Indeed, the derivative is bounded on the closed inner disk and the denominators have modulus at least one minus the inner radius. Dominated convergence therefore applies uniformly on the parameter set. Moreover, the derivative never vanishes, so the positive integral is strictly positive.

We claim that the triangle inequality is strict at every parameter:

$$
|I(\zeta)|<J(\zeta)\qquad(|\zeta|\le1).
\tag{1}
$$

If equality held, equality in the integral triangle inequality would make the continuous, nonzero function in the integrand have constant complex phase on the inner disk. Multiplication by a strictly positive real function preserves that phase. In particular,

$$
B_\zeta(w)|1-\zeta\overline w|^4
=q(w)(1-\overline\zeta w)^2
\tag{2}
$$

would have constant phase. The right-hand side is holomorphic in the integration variable. The open mapping theorem makes it a nonzero constant on the inner disk; the identity theorem gives the same identity throughout the unit disk. Thus, for constants with nonzero second member,

$$
q(w)=\frac{c}{(1-\overline\zeta w)^2},
\qquad
\phi(w)=b+\frac{cw}{1-\overline\zeta w},
\qquad c\ne0.
\tag{3}
$$

The image of this map is explicit. Set

$$
v=\frac{w}{1-\overline\zeta w}.
$$

Then the inverse condition for the unit disk is

$$
|v|<|1+\overline\zeta v|.
$$

If the parameter is interior, completing the square gives

$$
\left|v-\frac{\zeta}{1-|\zeta|^2}\right|
<\frac1{1-|\zeta|^2}.
$$

Consequently, the image domain is the disk

$$
B\!\left(b+\frac{c\zeta}{1-|\zeta|^2},
\frac{|c|}{1-|\zeta|^2}\right),
$$

contrary to the nondisk assumption. If the parameter lies on the unit circle, the inverse condition instead becomes

$$
\operatorname{Re}(\overline\zeta v)>-\frac12.
$$

The image is then an affine image of a half-plane and has infinite area, contrary to the finite-area assumption. This proves (1), including the boundary parameters.

Compactness now produces a uniform relative cancellation gap:

$$
\eta:=\min_{|\zeta|\le1}
\left(1-\frac{|I(\zeta)|}{J(\zeta)}\right),
\qquad 0<\eta\le1.
\tag{4}
$$

Only the parameter of an integral over a fixed interior disk has been extended to the boundary. No boundary extension of the conformal map or its derivative has been used.

## An input with smaller mass and output greater than one

Define

$$
F(a)=P_\Omega^+1(a),\qquad
H(a)=P_\Omega^+\mathbf1_E(a).
$$

These quantities are finite: every Bergman kernel section is square integrable, and the domain has finite area. The constant function belongs to the Bergman space, so reproduction gives

$$
\int_\Omega K_\Omega(a,w)\,dA(w)=1.
$$

Split this integral over the chosen interior set and its complement. The triangle inequality gives

$$
1\le
\left|\int_E K_\Omega(a,w)\,dA(w)\right|
\; + F(a)-H(a).
\tag{5}
$$

The conformal transformation law and the area change of variables are

$$
K_\Omega(\phi(z),\phi(w))
=\frac1{q(z)\overline{q(w)}(1-z\overline w)^2},
\qquad
dA(\phi(w))=|q(w)|^2\,dA(w).
$$

Therefore

$$
H(\phi(z))=\frac{J(z)}{|q(z)|},
\qquad
\left|\int_E K_\Omega(\phi(z),w)\,dA(w)\right|
=\frac{|I(z)|}{|q(z)|}.
\tag{6}
$$

Equations (4)–(6) prove the pointwise inequality

$$
F(a)\ge1+\eta H(a)\qquad(a\in\Omega).
\tag{7}
$$

Use the nonnegative, bounded, integrable input

$$
f=1-\frac\eta2\mathbf1_E.
$$

Its positive projection satisfies

$$
P_\Omega^+f=F-\frac\eta2H
\ge1+\frac\eta2H>1.
$$

The final strict inequality holds because the simply connected Bergman kernel has no zeros, as is also immediate from its displayed conformal formula, and the chosen set has positive area. Its input mass is

$$
\|f\|_1=A(\Omega)-\frac\eta2A(E),
\qquad
0<\|f\|_1<A(\Omega).
$$

Testing the strict superlevel set at threshold one now proves

$$
\boxed{
C_\Omega^+\ge
\frac{A(\Omega)}{A(\Omega)-\frac\eta2A(E)}>1.
}
\tag{8}
$$

This proves the nondisk direction. It does not require a strict lower bound for the infimum of the positive projection of the constant input.

## Disks and the normalization of the conclusion

The sharp unit-disk endpoint theorem gives its positive weak constant one. Under a similarity

$$
S(z)=b+cz,\qquad c\ne0,
$$

the kernel and operator transform as

$$
K_{S(\Omega)}(S(z),S(w))=|c|^{-2}K_\Omega(z,w),
$$

$$
(P_{S(\Omega)}^+f)(S(z))=P_\Omega^+(f\circ S)(z).
$$

Both input mass and output superlevel area are multiplied by the squared modulus of the similarity factor. Their weak ratio is unchanged. Thus every Euclidean disk has positive weak constant one, completing the equivalence.

To conclude that the domain is literally the unit disk, additional geometric normalization must fix its center at zero and its radius at one, for example by fixing the centroid and area. The norm identity alone cannot impose those normalizations.

## Why unrestricted simply connected domains are excluded

The upper half-plane supplies a genuine nondisk counterexample:

$$
\mathbb H=\{z:\operatorname{Im}z>0\},\qquad
K_{\mathbb H}(z,w)=-\frac1{(z-\overline w)^2},\qquad
\boxed{C_{\mathbb H}^+=1.}
$$

Here is a proof using only the sharp disk endpoint estimate and elementary limits.

### Upper bound by an increasing exhaustion of disks

Consider the increasing disks

$$
D_R=B(iR,R),\qquad \bigcup_{R>0}D_R=\mathbb H.
$$

For fixed half-plane points, their kernels satisfy

$$
K_{D_R}(z,w)
=\frac{R^2}{\left(R^2-(z-iR)(\overline w+iR)\right)^2}
\longrightarrow-\frac1{(z-\overline w)^2}.
$$

For each fixed output point, this convergence is uniform on compact source sets. Hence a nonnegative integrable input with compact support in the half-plane has positive disk projections converging pointwise to its positive half-plane projection, once the disks contain that support. Extend each disk output by zero outside its disk. Fatou's lemma for strict superlevel sets and the disk endpoint estimate give

$$
\lambda A\{P_{\mathbb H}^+f>\lambda\}\le\|f\|_1.
$$

Nonnegative truncations on increasing compact subsets of the half-plane converge monotonically to any nonnegative integrable input. Monotone convergence extends the estimate to every such input. This proves the upper bound one.

### Lower bound by mass spread along a boundary interval

For positive parameters, use ordinary area inputs of mass one:

$$
f_{\varepsilon,L}(t+is)
=\frac{\pi}{2L\varepsilon}
\mathbf1_{\{-L<t<L,\ 0<s<\varepsilon\}}.
$$

At each fixed output point, as the strip height decreases to zero their positive outputs converge to

$$
Q_L(x+iy)
=\frac1{2L}\int_{-L}^{L}\frac{dt}{(x-t)^2+y^2}
=\frac{\arctan((L-x)/y)+\arctan((L+x)/y)}{2Ly}.
$$

Every admissible weak constant for the area operator consequently bounds the distribution of this limit, by Fatou's lemma. Fix any parameter strictly between zero and one. For sufficiently large interval length, the following rectangle lies in the strict superlevel set at threshold one:

$$
0<\theta<1,\qquad
|x|<(1-\theta)L,\qquad
0<y<\frac{(1-\theta)\pi}{2L}.
$$

Indeed, throughout that rectangle,

$$
Q_L(x+iy)\ge
\frac{2}{\pi(1-\theta)}
\arctan\!\left(\frac{2\theta L^2}{(1-\theta)\pi}\right),
$$

whose limit is greater than one. The normalized area of the rectangle is the square of one minus the fixed parameter. It follows that

$$
C_{\mathbb H}^+\ge(1-\theta)^2.
$$

Letting that parameter decrease to zero proves the lower bound one. Thus an unrestricted equivalence over all simply connected regions would be false even if its conclusion were weakened from the unit disk to an arbitrary Euclidean disk.

## Formalization dependencies and provenance

The compact-interior-set proof depends on the Riemann mapping theorem; the normalized Bergman kernel on the disk; its transformation law; the reproducing property for constants; square integrability of kernel sections; conformal change of variables; equality in the complex integral triangle inequality; continuity under a uniformly dominated integral; the open mapping and identity theorems; compactness of the closed disk; and the sharp positive disk endpoint theorem. A proof using a conformally defined kernel can start with the explicit displayed formula, but identifying that object with the actual Bergman projection still requires the reproduction or orthogonal-projection bridge. These dependencies must be proved or imported as established mathlib results, not introduced as unproved analytic assumptions in a claimed complete formalization.

The bounded-domain theorem is now fully checked in
[`BoundedRigidity.lean`](../BergmanWeakType/Rigidity/BoundedRigidity.lean), as
`BergmanWeakType.positive_constant_eq_one_iff_disk`. Its statement uses the standard
`IsBergmanKernel` characterization and imposes no boundary regularity or conformal derivative
bounds. The stronger finite-area extension and the half-plane discussion in this note are
informal arguments; the implemented theorem assumes boundedness.

At the pinned mathlib version, `Mathlib/Analysis/Complex/RiemannMapping.lean` only supplies partial
results. This project ports the complete proof from
[mathlib pull request 33505](https://github.com/leanprover-community/mathlib4/pull/33505), commit
`d43061d911b1aeae0788591da437a3b115098962`, retaining Yury Kudryashov's authorship and Apache 2.0
license. The adapted [`RiemannMapping.lean`](../BergmanWeakType/Rigidity/RiemannMapping.lean) and
[`UnitDiscShift.lean`](../BergmanWeakType/Rigidity/UnitDiscShift.lean) compile against the project's
pinned Lean and mathlib versions. The full theorem is proved locally, with no additional axioms.

The remaining bridges are also checked:

- [`DiskReproducing.lean`](../BergmanWeakType/Rigidity/DiskReproducing.lean) proves disk reproduction
  for holomorphic integrable inputs and verifies the standard disk kernel characterization.
- [`KernelTransform.lean`](../BergmanWeakType/Rigidity/KernelTransform.lean) proves uniqueness,
  conformal covariance, and existence of the standard kernel on every proper simply connected
  open planar domain.
- [`PhaseRigidity.lean`](../BergmanWeakType/Rigidity/PhaseRigidity.lean) and
  [`MobiusGeometry.lean`](../BergmanWeakType/Rigidity/MobiusGeometry.lean) prove the equality phase
  identity, integrate the derivative, classify the interior image as a disk, and exclude boundary
  parameters by unboundedness.
- [`CoreGap.lean`](../BergmanWeakType/Rigidity/CoreGap.lean) and
  [`DomainGap.lean`](../BergmanWeakType/Rigidity/DomainGap.lean) establish the uniform cancellation
  gap on a positive-area interior set of every bounded simply connected nondisk.
- [`Perturbation.lean`](../BergmanWeakType/Rigidity/Perturbation.lean) constructs an integrable input
  of smaller mass with positive output at least one, proving strictness of the weak constant.
- [`DiskSimilarity.lean`](../BergmanWeakType/Rigidity/DiskSimilarity.lean) transfers the sharp disk
  estimate to arbitrary centers and positive radii.

The final theorem's axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
This is a proof and axiom check; comparator verification is recorded separately in the project
status and CI results.

The derivative-free compact-interior-set argument was recovered from the project chat titled “Prove Bergman kernel minimum bound”, dated October 16, 2026. The earlier project note titled “Positive Bergman weak norm rigidity and its antecedents” proved the result only with upper and lower conformal derivative bounds. The argument recorded here checks the phase calculation explicitly and strengthens the bounded-domain statement to finite-area simply connected domains: the excluded boundary equality case is a half-plane and therefore has infinite area. The half-plane discussion gives a self-contained proof of the scope obstruction using the project's sharp disk endpoint result. No private chat transcript is included.

The related classical equality classification for a constant Bergman kernel section is discussed in Dong and Treuer, [*Rigidity Theorem by the Minimal Point of the Bergman Kernel*](https://arxiv.org/html/2001.01856), Theorem 1 and Corollary 2. It allows relatively closed polar deletions when simple connectivity is absent. A punctured disk therefore illustrates why simple connectivity should not silently be dropped. That paper's kernel equality result is distinct from the weak-constant identity proved above. No publication-priority claim is made for the latter.
