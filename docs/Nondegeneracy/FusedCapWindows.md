# Dotted cap windows of the content-shifted Hom sectors

## Status and scope

This is a proposed written calculation, not a new Lean theorem. It computes the
postcomposition cap block, including its parity-shift transport, and identifies
an earlier obstruction to computing the reservoir block of the proposed fused
Hom action. It does not establish the residual partial-fraction comparison.
The calculation applies to a finite window `0 ≤ t < N`, with `N ≥ 0`; it does
not require either individual height to be nonnegative.

The definitions used below are `homContentPostE`, `homContentPostF`,
`homContentPostAdjunction`, `homContentPreE` in `RouquierHomContent.lean`,
`homPostCounit` in `RouquierHomAdjunction.lean`, and
`homContentPreF`, `homContentPreAdjunction` in `RouquierShiftedAdjunction.lean`.
The coupled construction is in `RouquierCoupled.lean`; there is no module
`RouquierCoupledAdjunction.lean` in the inspected research tree.
The even comparison is `RouqCoproduct.rouqCaps`, `rouqCaps_eq` and
`schur_const_eq` in `Categorification/TwoRep/RouqCoproduct.lean`.

Composition in the displays is in Lean order: `f ≫ g` means first f, then g.
Let B denote the probe/postcomposition sector and A the
reservoir/precomposition sector. Do not identify a sector's source with an
unshifted factor source without the transports below.

## 1. What the diagonal coupled construction actually gives

For `C : CoupledFactors`, put `D = C.DF₁.comp C.DE₁`, and define the dotted
counit using the constructed dot and adjunction:

```
w_t = C.F₁ ◁ rouquierPower C.x₁ t ≫ C.A₁.counit.
```

Directly from `SectorDecomp.inc_diag`, `inc_coupledCounit` and
`inc_coupledCounit_ne`, one obtains

```
D.inc (a,b) ≫ w_t = 0                                      if a ≠ b,
D.inc (a,a) ≫ w_t = C.P₁ a ◁ rouquierPower (C.dot₁ a) t
                    ≫ (C.adj₁ a).counit.                  (1)
```

Indeed commute the inclusion through each of the t dot factors, then through
the final counit. Every sector inclusion is even (`SectorDecomp.inc_mem`), so
superinterchange contributes `(-1)^(0·tp)=1`, not an omitted sign. This is a
finite-window formula for every t, without nilpotence or a geometric series.
It is a calculation from the existing definitions, not a new theorem proved
in this document. `C.sourceSector a` already records the corresponding dot
and counit compatibility.

Crucially, `CoupledFactors` takes `DE₁`, `DF₁`, the sector adjunctions and dots
as inputs. It does not construct these data from the content-shifted Hom
family. Thus (1) must not be read as an unconditional calculation in that
family. In particular its right-hand side is not automatically a factor's
unshifted `capD t`.

## 2. Computed postcomposition block with its actual shift

Fix the B edge `muM + α_i = nuM`, reservoir content `betaP`, and `muP`.
Write `L₀ = homPost (W.E i h)` and `R₀ = homPost (W.F i h)`. On the target
Hom category set

```
κ = homContentShift D i betaP = p(i) · contentParity D betaP,
S = homParityShift κ,
ξ_Y : S(S(Y)) ≅ Y.
```

Here ξ is the counit isomorphism of `homParityShiftAdjunction κ`, explicitly
the identity for κ=0 and `PiSupercategory.ξ` for κ=1. These are not freely
chosen shifts. The definitions give exactly

```
L_B = L₀ ⋙ S,       R_B = S ⋙ R₀,
(R_B ⋙ L_B)(Y) = S(L₀(R₀(S(Y)))).
```

For the dot transported by postcomposition and then S, its homogeneous
component at X is `S.map (X ◁ x)`, where `x = W.dot i h`. This is the
transport of `homPostTransform x`; it is not an extra scalar-shifted dot.
The composed adjunction's dotted counit is consequently

```
c_t(Z) = ((Z ≫ F) ◁ x^t) ≫ α_(Z,F,E).hom
           ≫ (Z ◁ ε) ≫ ρ_Z.hom,
w_(B,t)(Y) = S.map (c_t(S(Y))) ≫ ξ_Y.hom.                  (2)
```

The formula retains associators and the right unitor: `c_t` has source
`(Z ≫ F) ≫ E`, not `Z ≫ (F ≫ E)`. It follows by expanding
`homContentPostAdjunction`, whose counit is `S.map(c_0(S(Y))) ≫ ξ_Y.hom`,
and using functoriality to combine the t dot factors. In particular this is
an explicit finite cap formula, not a parameter named w supplied as input.
It describes the postcomposition sector before any unproved identification
with a `CoupledFactors` instance.

There is no hidden Koszul coefficient in (2). The functor S preserves
composition and ξ is even. If one instead removes a *single* S using the
odd comparison ζ, its supernatural law contributes
`(-1)^(κ·tp)` when crossing `x^t`; suppressing that transport changes the
formula. `ParityShiftDatum.hom_naturality` is the repository law that fixes
this sign. Keeping (2) avoids an arbitrary choice of such a trivialization.

### An exact low-window composite

For positive probe height `h_B`, let `a_B(s)=cupN s`, `0≤s<h_B`, for the
factor local inverse. Transport it first to the unshifted postcomposition
source by

```
a_s^post(Z) = ρ_Z.inv ≫ (Z ◁ a_B(s)) ≫ α_(Z,F,E).inv,
ã_s(Y) = ξ_Y.inv ≫ S.map (a_s^post(S(Y))).
```

Then the exact block entry, with no quotient or radical assumption, is

```
ã_s(Y) ≫ w_(B,t)(Y)
  = ξ_Y.inv ≫ S.map (a_s^post(S(Y)) ≫ c_t(S(Y))) ≫ ξ_Y.hom
  = if s=t then 𝟙 Y else 0,                              (3)
```

for `0≤t<min(N,h_B)`. To prove the second equality, cancel the adjacent
associators, use whiskering functoriality, and apply
`SuperRouquierLoc.cupN_capD` with both indices in its stated window.
The unitors and ξ cancel. No odd factors are exchanged, so (3) also holds
for odd i. If `h_B≤0` there are no such columns; (2) still holds. If `N>h_B`,
(3) makes no claim about the remaining t: the low-window inverse relation
does not compute those entries.

These are monomial inverse-window coordinates. They are **not** yet the
paired probe coordinates `z^ε(z²-c)^j`. The desired polynomial columns in
those coordinates would be

```
[t ≡ ε mod 2] · binom((t-ε)/2,j) · c^((t-ε)/2-j).
```

They follow algebraically by expanding `z^t` at `z²=c`, but identifying
the transported categorical inverse cups with that dual jet basis remains
necessary. Equation (3) cannot by itself supply that coordinate change or
the higher-window entries. No odd dot is replaced by `c+x`.

## 3. The reservoir obstruction is before the cap comparison

At the precomposition edge `-nuP + α_i = -muP`, set
`σ = leftAdjParity D i (-nuP)`. The declared raising and lowering functors are

```
L_A = homPre (T.E i h),
R_A = homPre (T.F i h) ⋙ homParityShift σ.
```

The right adjunction of L_A is **not** obtained from `T.adj`:
`homPreAdjunction (T.adj i h)` has `homPre F ⊣ homPre E`, the wrong direction.
The constructor `homContentPreAdjunction T W L ...` needs
`L : RouquierLeftAdjoints T` explicitly. Its `L.adjL` fields are shifted
left adjunctions of the factor, not consequences supplied by that constructor.

The repository defines the proposed factor cup and cap as `T.leftCup` and
`T.leftCap`. `T.leftAdjointsOfZigzags H` normalizes the cap by a unit `c⁻¹`,
but requires `H : T.LeftZigzags`. This proposition asks at each edge for

```
T.leftZigF = c • 𝟙 F,
T.leftZigE = ((-1)^σ c) • 𝟙 E,       c ∈ kˣ.              (4)
```

Neither `LeftZigzags` nor a concrete `RouquierLeftAdjoints T` for the intended
reservoir is constructed by the cited modules. Even a bounded construction
needs (4) at the edges traversed by its window. Nonnegative *total* height
does not imply either equation, and does not make the precomposition adjoint
point in the required direction. The explicit conditional shifted counit is
`homPreShiftCounitApp`:

```
(P.iso (E ≫ F ≫ Y)).hom ≫ α_(E,F,Y).inv
  ≫ (L.adjL.counit ▷ Y) ≫ λ_Y.hom.
```

Thus the missing datum is localized: the normalized factor left cap and its
two signed triangles, followed by the specific `homContentPreAdjunction`
transport. Assuming a cap restriction or supplying a new w-interface would
bypass precisely this missing construction.

The parity shifts of the functors are specified above (κ on both sides of
the postcomposition pair, σ on the lowering precomposition output). No
integer-graded Hom shift is constructed in these modules. Consequently
numbers `δ_a` for the residual degree table, and their identification with
sector transports in a graded realization, cannot be extracted from them.
Even for parity one must distinguish the raw factor source from its reversed
Hom-sector source; κ or σ alone is not a license to assign an arbitrary
`ε_a` in a different source convention.

## 4. Normalization and the remaining comparison

Set `q=(-1)^p`. Multiplying the principal mate by `-q` is not multiplication
of the counit in (2) by `-q`. In an even shifted block category, transport the
entire factor augmented map by `diag(-q,1)` on its `Y⊕P` target. This scales
both σ and u by `-q`; the inverse's r and b scale by `(-q)⁻¹`, whereas the
positive inverse cups a and the cap row v remain unchanged. With that
specified normalization, (3) is unchanged. Changing only σ is not the same
operation and does not justify reusing its original inverse columns.

The exact residual still has first row `wa − wr(1+Kr)⁻¹Ka` and second row
`−b(1+Kr)⁻¹Ka`. Formula (2), and (3) in the positive probe low window, compute
only the indicated wa entries after the postcomposition transport. The
following remain open, rather than being assumed by the calculation:

* the reservoir's bounded shifted left-adjunction triangles (4);
* the Hom-family realization of the coupled decompositions and dots, with
  its graded sector transports;
* the identification of monomial inverse cups, higher probe windows and
  inverse-dot windows with the parity-block jet coordinates;
* control of the residual correction by the same nilpotent reservoir ideal.

Accordingly there is no established identity `S mod J = L H Q` here, and no
new nonzero categorical consumer or Lean declaration is claimed.
