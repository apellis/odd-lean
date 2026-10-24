# Sorted boundaries and the all-upward coefficient comparison

**Conditional mathematical result.** Assume full upward SKM PBW with the
abstract coefficient algebra `SYM`, at all weights used below. Then an
adapted strict matching family for source `UD` and target `D'U'` has
injective coefficient expansion. Here `U,U'` are upward words and `D,D'`
are downward words. This is a coefficient-level proof, not an inference
from a Hom adjunction isomorphism. It is not yet a compiled Lean theorem.

The assumption is independence in the actual SKM presentation with full
bubble coefficients. Ordinary affine quiver-Hecke PBW does not supply it.

## The literal right closure

Write `E_rev(D)` for the upward word with the colours of `D` in reverse
order, and set

\[
 R=E_{\mathrm{rev}(D)},\quad L=E_{\mathrm{rev}(D')},\quad
 \lambda=\mu-\sum_{j\in D}\alpha_j.
\]

With chronological composition, close `f:UD→D'U'` by

\[
 LU\xrightarrow{1_{LU}\eta_R}LUDR
   \xrightarrow{1_Lf1_R}LD'U'R
   \xrightarrow{\epsilon_L1_{U'R}}U'R.
\]

The cups and caps are the right-adjunction `cupN` and `capN` of
[`MateN.lean`](../../OddMath/SKM/MateN.lean). Their parities are zero.
The copy of `f` has external region `λ+α(R)=μ`; the cap block has external
region `λ+α(U'R)=μ+α(U')`. Every local rewrite with right word context `v`
is instantiated at `wt D λ v`, not automatically at the global `λ`.

If no matching exists, the coefficient label module is zero. Otherwise
its oriented pairing itself gives a common strand count and a
colour-preserving bijection between `LU` and `U'R`. No independence of
simple roots is inferred from equality of weights.

## Adapted strict representatives

Place `U,D,D',U'` in the bottom-left, bottom-right, top-left and top-right
quadrants of a disk, in their boundary orders. Draw each matched pair as
a straight chord, choosing endpoint positions generically to avoid triple
intersections. Add disjoint collars to flatten the original boundaries.
Each oriented strand runs left to right: its source is in `U` or `D'`,
and its sink in `U'` or `D`.

Two chords intersect at most once and exactly when their endpoints
interleave. A bottom-bottom strand has one right cap, a top-top strand
one right cup, and a through strand no extremum. There are no left cups
or caps. At a mixed crossing the upward branch is on the lower left,
so its type is `EF→FE`, not the opposite mixed crossing.

Choose distinguished points at the sink collars, and choose one serializer.
Every matching class occurs once. Horizontal sweeping has source `LU`
and target `U'R`, and its crossings form a reduced permutation wiring.
This constructs the original strict representatives directly; arbitrary
inverse bending of an upward diagram would not by itself prove strictness.

## A finite generator-level sweep

Rotate the height function from `y` to
`y cos(ϑ)+x sin(ϑ)`, for `0≤ϑ≤π/2`. Use generic piecewise-polynomial
collars and perturbations so there are finitely many isolated events.
The drawing's crossing vertices neither appear nor disappear, and no
triple point occurs. This motion enumerates rewrites; it is **not** an
assumption of unrestricted pivotal isotopy.

At a tangency the derivative in the complementary horizontal direction
is `x'/cos(ϑ)>0`, away from the final angle. Consequently all bends are
right bends. Endpoint events introduce exactly the nested right cups on
`D` and right caps on `D'` in the displayed closure. The remaining events
are bend cancellation, a bend passing a dot or crossing, and interchange
of disjoint events.

For completeness, put `σ_ij:E_jF_i→F_iE_j` and
`δ_ij:F_iF_j→F_jF_i`. The crossing events use these exact equalities in
[`Mates.lean`](../../OddMath/SKM/Mates.lean):

| Event | Typed identity | Declaration |
|---|---|---|
| Up/mixed, cap | `(1_Ei σ_ij);(ε_i 1_Ej) = (τ_ij 1_Fi);(1_Ej ε_i)` on `E_iE_jF_i→E_j` | `eq_2_4_a` |
| Up/mixed, cup | `(1_Ej η_i);(σ_ij 1_Ei) = (η_i 1_Ej);(1_Fi τ_ij)` on `E_j→F_iE_jE_i` | `eq_2_4_b` |
| Mixed/down, cup | `(η_i 1_Fj);(1_Fi σ_ji) = (1_Fj η_i);(δ_ji 1_Ei)` on `F_j→F_iF_jE_i` | `eq_2_5_a` |
| Mixed/down, cap | `(σ_ji 1_Fi);(1_Fj ε_i) = (1_Ei δ_ji);(ε_i 1_Fj)` on `E_iF_jF_i→F_j` | `eq_2_5_b` |

All four coefficients are one, at arbitrary weights and colours, including
equal colours. They use the literal right mates, with no bubble correction
or inverse-crossing assumption. Bend pairs cancel by `cl_zigE`, `cl_zigF`;
dots pass bends by `cl_cup_slide`, `cl_cap_slide`. Disjoint events interchange
by `cl_ixc` in [`MateBlock.lean`](../../OddMath/SKM/MateBlock.lean), retaining
`(-1)^{|A||B|}`. Cups and caps contribute no such sign because they are even.
Events sharing a strand use the mate identities, not disjoint interchange.

This is a finite algorithm for equality of the specified closure with a
sign times the reduced upward wiring. It retains exactly the original
crossing vertices and eliminates the auxiliary bends. It supplies more
than an identification of the two Hom spaces.

## Labels, dot powers and signs

The matching pairing gives the upward permutation `w`. Put each strand's
dot count at its sink. A sink in `U'` keeps its position; a sink at position
`k` in `D`, indexed from zero, becomes position

\[
 |U'|+|D|-1-k
\]

in `U'R`. This is a bijection on dot-count functions, with no exponent shift.
Dots near their sinks pass no crossing on their own strand when serialized
at the top of the final wiring.

Repeated downward dots carry the actual mate reversal factor

\[
 (-1)^{|i|\binom m2}=(-1)^{|i|\lfloor m/2\rfloor}.
\]

This is the composition sign of `cl_mate_comp` and `cl_ddot_pow`. In
particular two odd dots give a minus sign, not zero. Other signs come from
the fixed event serializer; count individual interchanges or use the batch
mate formula, but do not count the same reversal twice. Their product is
a unit `ε_(w,m)∈{1,-1}`.

Changing the reduced wiring to a fixed upward PBW reduced expression
preserves its leading permutation up to sign. Distant interchanges give
signs, and braid corrections have smaller crossing length. Lower terms
can be normalized without increasing that length. No quadratic reduction
is needed on the reduced top-length term.

## Full-SYM source coefficients

Move the source coefficient past the **entire original decorated diagram**
`g` before simplifying the closure. Super-interchange gives `Θ^{|g|}(p)`.
The bubble then lies between `U'` and `R`, in region `μ`. It crosses only
`R`, not `L`, `U` or `U'`.

The [one-strand full-SYM transport](ElementaryClosure.md#one-strand-transport-on-full-sym)
provides finite nonnegative dot powers, with constant coefficient exactly
`p`. Its proof uses the stipulated upward independence, normalized scalar
cancellation, and algebra-hom extensionality for all generators of `SYM`.
It includes ordered products of distinct exterior generators. The
coefficient-last serializer `ρ_j⁺` is additive, not asserted multiplicative.

For `R=(r_1,...,r_q)`, the local right region at stage `t` is
`λ+∑_(s>t)α_(r_s)`. Iteration changes dots only on these strands. It cannot
erase a previously added positive exponent, and its all-zero exponent
coefficient is still `p`. Thus the top-crossing column is

\[
 \epsilon_{w,m}\,\tau_w X^{n(m)}
       \rho_R^+(\Theta^{|g_{w,m}|}(p)).
\]

This formula uses an upward PBW convention with the coefficient last.
The source-placed convention is equivalent by the homogeneous
super-interchange involution on each PBW label. Changing convention does
not change crossing length or strand-dot counts.

## Injectivity by finite-support detection

In a finite input relation take the greatest occupied crossing length.
Shorter columns cannot contribute there. Within each permutation of that
length, take the least occupied total input dot count. Positive transport
terms cannot reach that degree from these or higher-dot inputs. The
count bijection leaves the diagonal coefficient blocks

\[
 p\longmapsto\epsilon_{w,m}\Theta^{|g_{w,m}|}(p),
\]

which are invertible `k`-linear maps on full `SYM`, not necessarily
`SYM`-linear scalar maps in this convention. Kill these coefficients,
continue through the finite input support, then descend crossing length.
Upward independence turns a vanishing evaluated closure into the formal
coefficient vanishing used here.

No bubble coefficient is inverted, and no finite inverse of `ρ_R⁺` is
claimed. Arbitrarily high dots in lower-crossing errors do not affect this
order of detection. This proves the conditional adapted-family result,
not upward independence, arbitrary-choice equivalence, or full oriented
nondegeneracy.

`python3 scripts/Nondegeneracy/sorted_boundary_chords.py` checks finite
pairing/permutation, dot-count and mate-sign cases. It is not a categorical
model or a kernel verification of the sweep. Formalizing the geometric
event enumeration and its coefficient comparison remains work.
