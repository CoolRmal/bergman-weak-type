# Weighted estimates: statements, sources, and proof dependencies

This document records the intended mathematical results and their informal proofs. A theorem
listed here is not thereby proved in Lean. The checked declarations currently implemented in
`BergmanWeakType/Kernel.lean` establish elementary kernel identities, pointwise domination,
the zero-weight specializations, and positivity and normalization of the proposed sharp constant.

## Normalization and intended results

Write

$$
\mathbb D=\{z\in\mathbb C:|z|<1\},\qquad
dA(z)=\frac{dx\,dy}{\pi},\qquad
dA_\alpha(z)=(\alpha+1)(1-|z|^2)^\alpha dA(z),\qquad \alpha>-1.
$$

Both disk measures have total mass one. The weighted projection and its positive majorant are

$$
P_\alpha f(z)=\int_{\mathbb D}
(1-z\overline w)^{-(\alpha+2)}f(w)\,dA_\alpha(w),
\qquad
P_\alpha^+f(z)=\int_{\mathbb D}
|1-z\overline w|^{-(\alpha+2)}|f(w)|\,dA_\alpha(w).
$$

The complex power uses the analytic branch equal to one when its argument is one. For interior
disk points the base has positive real part, so the principal complex power is this branch.
The implementation defines the positive majorant as an extended nonnegative integral. This
preserves its meaning before a finite bound has been established. The linear positive-kernel
operator has the same weak constant, since it is dominated by its value on the absolute input
and nonnegative inputs suffice for the lower bounds.

Use strict superlevel sets and the distribution weak quasi-norm:

$$
\|g\|_{1,\infty;\alpha}
=\sup_{\lambda>0}\lambda A_\alpha\{|g|>\lambda\}.
$$

Let the corresponding optimal operator constants be

$$
C_\alpha=\|P_\alpha\|_{L^1(dA_\alpha)\to L^{1,\infty}(dA_\alpha)},
\qquad C_\alpha^+=\|P_\alpha^+\|_{L^1(dA_\alpha)\to L^{1,\infty}(dA_\alpha)}.
$$

The strongest supplied positive-kernel result is

$$
C_\alpha^+=D_\alpha:=\frac{\Gamma(\alpha+1)}{\Gamma(1+\alpha/2)^2},
\qquad 1\le C_\alpha\le D_\alpha
\qquad(\alpha>-1).
$$

The separate boundary-column argument supplies

$$
\max\{1,c_\alpha\}\le C_\alpha\le C_\alpha^+=D_\alpha
\qquad(\alpha\ge0),
$$

where

$$
c_\alpha=
\frac{2^\alpha(\alpha+1)}{\sqrt\pi(\alpha+2)}
\frac{\Gamma((\alpha+1)/2)}{\Gamma((\alpha+2)/2)}
=\frac{\alpha+1}{\alpha+2}D_\alpha.
$$

The supplied lower-bound proof uses nonnegative weight parameters; no extension of that proof
to negative parameters is asserted here. At zero the results yield both unweighted equalities:

$$
C_0=C_0^+=1.
$$

For orientation, the claimed positive constants include

$$
D_1=\frac4\pi,\qquad D_2=2,\qquad D_3=\frac{32}{3\pi},\qquad D_4=6.
$$

The radial examples that prove positive-kernel sharpness have constant complex projection.
They do not prove equality between the two constants for nonzero parameters.

## Source provenance

The project owner supplied these proofs through the local research files and earlier project
chats. The sources were audited on 18 October 2026.

- `research/bergman-weighted-exact.tex`, dated 16 October 2026, is the current six-page proof.
  Its sections 2–5 contain the radial truncation lemma, kernel differential identity,
  radial normalizer, and annulus sharpness argument. It removes the hypergeometric functions
  used in an earlier version.
- `research/bergman-weighted-boundary-reduction.md` gives the earlier detailed proof, including
  an explicit smooth truncation and the reduction to boundary measures.
- `research/bergman-weak-weighted-note.tex` and `research/bergman-weighted-and-shapes.md`
  supply the separate boundary-column lower bound. Their earlier claims that only a
  qualitative weighted upper bound was available are superseded by the exact positive result.
- `research/bergman-weak-sharp.md` supplies an independent unweighted proof by a harmonic
  majorant and the planar torsion estimate. The weighted proof specializes to zero, so this
  coarea and isoperimetric route need not be formalized to obtain the disk equalities.
- The research discussion titled “Bound Bergman projection constants” records the proof
  development and subsequent audit.
  Its 16 October revision explains the boundary substitution and moving-cap simplification.
  Its last clarification distinguishes the linear positive operator from the absolute-input
  majorant and explains why their sharp constants agree.

These references identify the user's source material; they do not establish publication
priority. The research notes explicitly leave novelty unverified. Original chats and unrelated
source files are not copied into the public repository.

## Dependency map for a complete Lean proof

1. Prove that weighted disk area is a probability measure and derive polar integration in the
   radial mass variable

   $$
   s=\alpha+1>0,\qquad y=(1-r^2)^s,
   \qquad dA_\alpha=dy\,\frac{d\theta}{2\pi}.
   $$

2. For a nonnegative twice continuously differentiable function and a positive continuously
   differentiable radial coefficient, establish

   $$
   \operatorname{div}(\omega\nabla v)\le0
   \quad\Longrightarrow\quad
   r\longmapsto\frac1{2\pi}\int_0^{2\pi}
   \min\{v(re^{i\theta}),c\}\,d\theta
   \text{ is nonincreasing}
   $$

   for each fixed nonnegative cap. The source proves this by the chain rule, the divergence
   theorem on interior disks, and approximation by smooth increasing concave functions.

3. Set the cap to the threshold times the radial mass. The moving-cap mean is locally
   Lipschitz and nondecreasing in the mass variable. Its right difference quotient dominates
   the angular measure of the strict superlevel set. Integrating this inequality proves

   $$
   \lambda A_\alpha
   \left\{\frac{v(z)}{(1-|z|^2)^s}>\lambda\right\}\le v(0).
   $$

   Strict levels matter: the right derivative of the minimum with respect to the cap is
   the indicator of a strict inequality, including at equality points. No regularity of
   an output level set is assumed.

4. For the positive kernel, differentiate in the output variable. With

   $$
   k=\alpha+2,\quad t=1-|z|^2,\quad
   k_w(z)=|1-z\overline w|^{-k},\quad
   \mathcal L=\Delta-\frac{2k}{t}z\cdot\nabla-\frac{k^2}{t},
   $$

   the exact identity is

   $$
   \mathcal Lk_w(z)=
   -\frac{k^2(1-|w|^2)}{t|1-z\overline w|^2}k_w(z)\le0.
   $$

   Kernel derivatives are uniformly bounded in the closed input disk on each compact output
   subdisk. This justifies differentiating the potential of every integrable input.

5. Define the positive radial boundary average and prove its exact bound:

   $$
   J(r)=\frac1{2\pi}\int_0^{2\pi}|1-re^{i\theta}|^{-k}\,d\theta,
   \qquad
   (1-r^2)^sJ(r)\uparrow D_\alpha.
   $$

   The boundary Möbius substitution rewrites the scaled average as

   $$
   (1-r^2)^sJ(r)=\frac1{2\pi}\int_0^{2\pi}|1-re^{i\theta}|^\alpha\,d\theta.
   $$

   Subharmonicity gives monotonicity. Dominated convergence, the beta integral, and gamma
   duplication evaluate the endpoint. For negative parameters, domination uses an integrable
   power of the sine of the half-angle.

6. Divide the positive output by the normalizer. The kernel differential identity gives

   $$
   F=P_\alpha^+f,\qquad v=F/J,\qquad
   \omega=(1-|z|^2)^kJ^2,\qquad
   \operatorname{div}(\omega\nabla v)\le0.
   $$

   Apply the truncation lemma and the normalizer bound to get the upper constant.

7. Normalize indicators of thin outer annuli to have mass one. Their positive outputs converge
   pointwise to the radial normalizer. Fatou's lemma transfers any weak bound to this limit.
   Strict radial increase and the exact weighted outer-annulus measure recover the endpoint
   constant. Boundary measures describe a limit; all test inputs remain integrable functions.

8. Use pointwise domination for the complex upper bound and reproduction of the constant
   function for the lower bound one. For the boundary-column lower bound, approximate an
   interior point mass by admissible normalized bumps, let the source approach the boundary,
   then rescale a small boundary cap. Dominated convergence and a beta integral give the
   explicit boundary constant.

## Audit conclusion

The informal argument was checked for its signs, normalizations, parameter range, strict
superlevel sets, and approximation by admissible inputs. No gap was identified in the
weighted exact proof. Completing the Lean argument still requires the analytic and
measure-theoretic dependencies above; elementary kernel lemmas alone do not establish the
sharp estimates.
