# Nondegeneracy for symmetrizable Cartan superdata: proof and open steps

This document is the end-to-end argument of [GeneralRoute](GeneralRoute.md),
written as a proof. Every step carries one of these statuses:

* **Lean**: proved in Lean; the declaration is named.
* **paper**: a proposed written argument, not a Lean theorem; qualifications
  in [FusionReservoirLemma](FusionReservoirLemma.md) and
  [CyclotomicDeformationProof](CyclotomicDeformationProof.md) take precedence.
* **cited**: a published statement; the locator is given only where the
  source text was read in `formalization-workspace/sources/ocr`.
* **OPEN**: not proved; the exact missing statement is given.

The proof is not complete. In particular the all-height residual Schur matrix
is not eliminated by reservoir nilpotence, and arbitrary homogeneous
exterior-coefficient cyclotomic deformations need not be flat. Steps A0, A1,
A2-b, A2-c, A3 and the final
assembly B1/B2 contain OPEN statements, listed in §6. No step uses a
finite-degree computation. The computations recorded in SeparatedFusion §7 are
evidence only and are not cited as proof.

Notation. `D` is a Cartan superdatum with index set `I = I_even ⊔ I_odd` and
symmetrizable Cartan matrix `(a_ij)` with symmetrization `d_i a_ij = (α_i|α_j)`.
`Q_ij(u,v)` are the KKO/BE polynomials. They are even, satisfy
`Q_ij(u,v) = Q_ji(v,u)`, and have invertible pure coefficient
`t_ij` of `v^{-a_ji}`. `q = -1` for an odd colour and `q = +1` for an even one.
`K` is a field, with `char K ≠ 2` if `I_odd ≠ ∅`.

---

## 1. Statement

**Theorem (Nondegeneracy).** For every symmetrizable Cartan superdatum `D`
and admissible scalars `Sc`, `cs`, the conjecture `SKM.NondegeneracyConjecture
cs` (`OddMath/SKM/Nondegeneracy.lean`) holds. That is, for all words `a`, `b`
of equal weight, every weight `μ` and every matching basis choice `F`, the
decorated family `F` is a basis. This means it has unique finite `SYM`
coefficients.

Equivalently (**Lean**, `SKM.nondegeneracyConjecture_iff_injective`), every
expansion map `F.expansion cs μ` is injective. Surjectivity is Brundan–Ellis
Theorem 8.1 and is already in the library.

## 2. Reduction to upward independence (B0)

**Lean.** `SKM.nondegeneracy_iff_upward_independence :
NondegeneracyConjecture cs ↔ WeakMate.UpwardIndependence cs`
(`OddMath/SKM/UpwardNondegeneracyReduction.lean`). It holds over any
commutative ring, and its axioms are printed in the file.

So it suffices to prove `UpwardIndependence cs`: injectivity of the expansion
of upward words at every weight.

## 3. Detection from fused sector actions (C)

**Lean.** Over a field `K`:

```
OddMath.QuiverHecke.upward_independence_of_fused_sector_actions
  (A : ∀ μ, FusedSectorAction D S cK μ B) : SKM.WeakMate.UpwardIndependence cK
```

(`OddMath/QuiverHecke/ReservoirFusedSectors.lean`). A `FusedSectorAction` at
`μ` consists of the following.

1. `family : FusedRegularVacuumFamily D S cK μ (fun j => D.h j μ)`. This is a
   family of fused vacuum words realised in a 2-representation, together with
   the *regular identification*: the reservoir `SYM`-action on the vacuum Hom
   spaces is the regular representation.
2. For each generator `g` of `SYM`, a `VacuumSectorBubble` with these fields:
   * the two adjunctions;
   * the dots `x₁`, `x₂`;
   * the coupled crossing with its **slide**
     `cross ≫ E₁ ◁ x₂ − q (x₁ ▷ E₂ ≫ cross) = 1`;
   * reservoir and probe sector summands (`SourceSector`, `TargetSector`);
   * **probe inverses** `w`, `z`;
   * **reservoir nilpotence** `hnC`, `hnD`;
   * the **fused bubble identification** `fused`: the evaluated
     probe-cup–mate–reservoir-cap composite equals the fused bubble of `g`;
   * the vacuum values `probe`, `reservoirValue` and `normalize`.

The mate projection formula is **not** a hypothesis. It is proved from the
slide, the probe inverses and the reservoir nilpotence by
`SKM.SuperRouquierLoc.MateProjectionFormula.of_sectors`, used in
`VacuumSectorBubble.toSector_mateProjection`. The underlying algebra is
`SKM.mate_signed_series`, `mate_series_probe_source` and
`mate_series_probe_target` (`OddMath/SKM/RouquierMateSeries.lean`), with
`MateProjectionFormula.of_coordinates`
(`OddMath/SKM/RouquierMateCoordinates.lean`). §5.2 below gives the paper
version.

So the theorem follows once, for every `μ`, one constructs a
2-representation carrying these data. The remaining sections do this:

* A0/A1 construct the factors;
* A2 fuses them and proves the slide and the inversion that define the fused
  bubbles;
* A3 supplies the regular identification.

## 4. The factors (A0, A1)

### 4.1 Reservoir and probe

**Reservoir.** Take the super cyclotomic quiver Hecke algebras
`R^Λ(β)` (KKO-I Definition 7.1), in deformed form: odd colours `i` may carry
`a_i^Λ(u) = u^{N_i} + Σ c_{i;k} u^{N_i-k}`, where the `c_{i;k}` are
homogeneous, of positive degree and of parity `k·p(i)`. The base is
`K` or `K ⊗ Λ(δ)` with odd generators `δ`. The 2-representation is
`⊕_β Mod R^Λ(β)`, with:

* `E_i` = restriction to `e(β, i)` (in KKO, `E^Λ_i`);
* `F_i` = induction `R^Λ(β+α_i)e(β,i) ⊗_{R^Λ(β)} −`;
* dots = right multiplication by `x_{n+1}`;
* crossings = right multiplication by `τ_n`.

**Probe.** A second cyclotomic 2-representation with invertible dots.
Its cyclotomic polynomials have nonzero constant term. Example:
`f_i = (u² − 1)^M` for odd `i`, `(u − 1)^M` for even `i`. On every
finite-dimensional block, `x` (even `i`) or `x²` (odd `i`) is unipotent,
hence invertible.

**Constraint (cited from KKO-I, Definition 4.1 and §7).** For odd `i`, the
cyclotomic polynomial has only even-`k` coefficients. For odd `N_i` it is
therefore divisible by `u`, so the probe dot cannot be invertible. **A probe
exists only for even `⟨h_i, Λ_B⟩` at odd colours.** Whether the detection
weights of §3 can always be reached with such probes is the A3 question (§6).

### 4.2 Action theorem

The factor actions are A1. The statements needed:

**(A1-a) KLR relations.** `R(n)` acts on `E^n` by the defining relations.
This holds by construction, since the action is right multiplication.

**(A1-b) `i ≠ j`.** `E_i F_j ≅ q^{-(α_i|α_j)} Π^{p(i)p(j)} F_j E_i`.
**cited**, KKO-I Theorem 9.1, for undeformed `a^Λ`.

**(A1-c) `i = j`.** For `λ = Λ − β`:

* if `⟨h_i,λ⟩ ≥ 0`:
  `Π_i q_i^{-2} F_iE_i ⊕ ⊕_{k<⟨h_i,λ⟩} Π_i^k q_i^{2k} → E_iF_i` is an
  isomorphism;
* dually if `⟨h_i,λ⟩ < 0`.

**cited**, KKO-I Theorem 9.6, for undeformed `a^Λ`.

**Written proof (A1-map), not yet Lean.** The detection data need the
specific Rouquier map, not just an abstract isomorphism:

> (A1-map) For the cyclotomic super 2-representation, the map
> `ρ = [σ ; ε∘x^0, …, ε∘x^{h-1}]` (resp. with dotted units for `h<0`) is
> invertible. Here `σ` is the cup–crossing–cap mate.

For the actual full-ELV coefficient algebra and its stated admissibility
hypotheses, `DeformedMatrixComparison.md` proves this at every height using
`DeformedMackeyBoundary.md`, `DeformedBoundaryDivision.md` and
`DeformedRouquierMatrix.md`. The output parity transport in the cap rows
and their semilinear kernel-pivot calculation are explicit. This does not
prove the full action, fusion, or a Lean version of the full-coefficient result.

In the even case this is Kang–Kashiwara's theorem: Kang–Kashiwara
*Categorification of highest weight modules via KLR algebras*, the source
`kang-kashiwara-cyclotomic_1102.4677v4.txt`. The statement there was not
re-read for this document, so no locator is given. The companion notes above
resolve the specific-map comparison in the super case at the written level.
Lean modules in progress for this map are listed in HANDOFF (A0).

**A0-deform: standard integer-graded action proved on paper; Lean
implementation open.** `DeformedActionAssembly.md` and
`DeformedMixedBraid.md` supply the full underlying presentation action,
including the mixed quadratic, corrected braid and prescribed mates.
`DeformedGradedAction.md` supplies weight-dependent restriction shifts
and coherent adjunction transport, with all generator and inverse-component
degrees checked. Unshifted restriction alone does not preserve those degrees.
KKO permits homogeneous even coefficients over an
ordinary commutative graded base; odd super coefficients require a separate
argument. The unrestricted family suggested in §4.1 is too broad: already
the one-strand relation `x²−xd+ef=0` over `Λ(d,e,f)` forces `def=0` and is
not flat. Use the precise ELV coefficient ring, including `d_iχ_(i,m)=0`
at even cutoffs, as specified in [CyclotomicDeformationProof](CyclotomicDeformationProof.md).
That ring is itself not flat over the independent exterior subalgebra.
The translated KKO subfamily has a proposed tower-freeness proof, but does
not supply the even-cutoff ELV deformation. The direct full-family matrix argument is now supplied by the companion
notes above, without nilpotent lifting. A lifting-based alternative would
still need exact base-change comparison and Tor vanishing for the target
convolution kernel; algebra freeness alone is not sufficient. The graded
all-module action is supplied above; restricting to projectives also needs the
appropriate side-specific projectivity statements.

## 5. Separated-sector fusion (A2)

### 5.1 Setting and hypotheses

`𝒱_A`, `𝒱_B` are 2-representations of the KLR data. `𝒱 = 𝒱_A ⊠ 𝒱_B` is the
category of modules over `A ⊗̂ B`, with the Koszul sign rule. Fix the following
hypotheses.

* **(H1) reservoir nilpotence.** On every object, every dot of `𝒱_A` acts
  nilpotently. For a finite-dimensional, nonnegatively graded `A` with dots
  of positive degree this is automatic: the degree argument also holds with
  `δ`'s of positive degree.
* **(H2) probe invertibility.** Every dot `x` of `𝒱_B` at an even colour, and
  every `x²` at an odd colour, acts invertibly.
* **(H3) factor actions.** Both factors satisfy A1 (all of §4.2, including
  (A1-map)).

**Fused functors.** `E_i = E_i^A ⊕ Π^{s} E_i^B` and `F_i` = its biadjoint,
where `Π^{s}` is the parity twist of SeparatedFusion. Dots: `x = x^A ⊕ x^B`.
For a word `ν` the composite `E_ν` splits into *sector patterns*
`P ∈ {A,B}^n`. Write `E_ν^P` for the summands.

**Interchange.** For a pattern `P` and the pattern `P'` obtained by swapping
an adjacent `(A,B)`, the Koszul interchange gives an isomorphism
`J : E^P → E^{P'}`. It is natural for the factor 2-morphisms with the Koszul
sign.

**(J1) paper.** For an odd colour `i`, let `X_{AB}`, `Y_{AB}` be the outer and
inner dots on `E_i^A E_i^B`. Then the twisted interchange satisfies
`J X_{BA} = q Y_{AB} J` and `J Y_{BA} = q X_{AB} J`.

*Proof.* The twist `Π^s` makes `J` odd for odd `i` (SeparatedFusion §7,
crossing parity). An odd 2-morphism anticommutes with odd dots under the
Koszul interchange. For even `i` everything is even and `q = 1`. ∎

### 5.2 (A2-a) The mate projection formula from the dot slide

**Proposition (paper; abstract version Lean).** Assume (H1), (H2), and that
the fused crossing satisfies the slide `T X − q Y T = 1` on `E_iE_i`. Then
the reservoir–probe blocks of the normalized mate `−q·σ` are:

```
C = Σ_{r≥0} q^r  u_{A,r} ∘ v_{B,−r−1}
D = −Σ_{r≥0} q^{r+1} u_{B,−r−1} ∘ v_{A,r}
```

Here `C : E^BF^B → F^AE^A`, `D : E^AF^A → F^BE^B`, `u` are dotted units and
`v` are dotted counits. Negative powers are powers of the inverse probe dot,
and the sums are finite by (H1).

*Proof.* Rouquier's slide for the mate
(**Lean** `SKM.rouquierMate_slide`, normalized as
`rouquierMate_normalized_slide`) reads `σ'∘(F◁x) − q (x▷F)∘σ' = η∘ε`. Here
`σ' = −qσ`, and the source dot and target dot are whiskered on the relevant
sides.

Project onto the block `C`, composing with the sector inclusion and
projection. Sector inclusions and projections commute with dots, by
naturality of the direct-sum decomposition. On `E^BF^B` the source dot is
the probe dot `Y_B`. On `F^AE^A` the target dot is the reservoir dot `X_A`.
So

`C Y_B − q X_A C = η_A ∘ ε_B`.

The operator `Z ↦ Z Y_B − q X_A Z` is the sum of two commuting operators.
Right composition with `Y_B` is invertible by (H2). Left composition with
`q X_A` is nilpotent by (H1). Hence it is invertible, and the unique solution
is the terminating Neumann series

`C = Σ_r q^r X_A^r η_A ε_B Y_B^{−r−1}`.

Finally, `X_A^r ∘ η_A = u_{A,r}` and `ε_B ∘ Y_B^{−r−1} = v_{B,−r−1}`, by
naturality of the units in the dots. The case of `D` is symmetric, with
target-probe orientation. ∎

**Status.** This is exactly `MateProjectionFormula.of_sectors` /
`of_coordinates` (**Lean**). The odd case is automatic: `q` enters only
through the slide. Hypotheses: only the slide on `E_iE_i`, (H1) and (H2).
In particular, no crossing data enter. This explains why the round-5 parity
mutation was invisible to the mate check.

### 5.3 (A2-c) The fused crossing and its relations

**Definition of the fused crossing `T_ij : E_iE_j → E_jE_i`.**

*Same sector* (`AA`, `BB`): the factor crossing, transported along the
Koszul tensor product.

*Equal colours, cross sectors.* On the two summands `AB`, `BA` of
`E_iE_i`, write `X = X_{AB}` and `Y = Y_{AB}`. Put

```
          ⎡ a            J        ⎤        even i:  a = (X − Y)^{-1}
T_cross = ⎢                       ⎥
          ⎣ −J^{-1}a²   −J^{-1}aJ ⎦        odd i:   a = (X − Y)(X² − Y²)^{-1}
```

with rows and columns ordered (AB, BA), source on the right.

*Distinct colours, cross sectors.* On `E_i^A E_j^B → E_j^B E_i^A` the map is
`J`. On `E_i^B E_j^A → E_j^A E_i^B` the map is `Q_ij(X,Y)∘J^{-1}` (the
polynomial evaluated at the outer and inner dots). All other cross
components vanish.

`a` is well defined: `X − Y` (even), resp. `X² − Y²` (odd), is invertible.

**Lemma 0 (paper).** If `x` is nilpotent, `y` is invertible and
`xy = ±yx`, then `x − y` is invertible when `xy = yx`, and
`x² − y²` is invertible when `xy = −yx`. Also, `Q_ij(x,y)` is invertible
for an outer reservoir dot `x` and an inner probe dot `y`.

*Proof.*
* For `xy = yx`: `x − y = −y(1 − y^{-1}x)` and `y^{-1}x` is nilpotent.
* For `xy = −yx`: `x²` and `y²` commute and `x²` is nilpotent, so the same
  argument applies to `x² − y²`.
* For `Q_ij`: `Q_ij(x,y) − t_ij y^{−a_ji}` lies in the two-sided ideal
  generated by `x`. Since `xy = ±yx`, that ideal is `x·K[x,y]`, and it is
  nilpotent. `t_ij y^{−a_ji}` is invertible. ∎

**Proposition c1 (paper): two-strand relations.** On every fused `E_iE_j`:

1. The dot slides hold:
   * `T X − q Y T = δ_ij` and `X T − q T Y = δ_ij`, for `i = j`;
   * `T X = ± Y' T` without correction, for `i ≠ j`.
2. `T² = 0` on `E_iE_i`.
3. `T_ji T_ij = Q_ij(x_1, x_2)` on `E_iE_j` for `i ≠ j`.

Moreover, given the same-sector blocks and the choice `J` for the `BA→AB`
block, the equal-colour cross blocks are *forced* by 1 and 2.

*Proof.*
* *Same-sector blocks*: these are the factor relations (H3).

*Equal colours, cross blocks.* Write `T = [[a,b],[c,d]]`.

* *Diagonal slides.* The `(AB,AB)` component of (1) is `aX − qYa = 1`.
  - By Lemma 0 and the Sylvester argument of §5.2, it has a unique solution.
  - Even case: `(X−Y)^{-1}` commutes with `X` and `Y` and solves it.
  - Odd case: `X² − Y²` commutes with `X` and `Y`, and
    `(X−Y)X + Y(X−Y) = X² − Y²` because `XY = −YX`. So `a` solves it.
  - The second slide `Xa − qaY = 1` follows in the same way, from
    `X(X−Y) + (X−Y)Y = X² − Y²`.
  - The `(BA,BA)` component is the conjugate by `J`, using (J1).
* *Off-diagonal slides.* The `(AB,BA)` component reads `b X_{BA} − q Y b = 0`,
  which `b = J` satisfies by (J1).
  - For `c = −J^{-1}a²`, first note that `a²` commutes with `X` and `Y`. From
    the two slides, `a²X = a(1 + qYa) = a + q(aY)a`, and `aY = q(Xa − 1)`.
    Hence `a²X = a + Xa² − a = Xa²`, and similarly for `Y`.
  - Then (J1) gives `c X − q Y_{BA} c = 0`.
* *Square.* `T² = 0` is the four identities `a² + bc = 0`, `ab + bd = 0`,
  `ca + dc = 0` and `cb + d² = 0`.
  - The first two hold by the definitions of `c` and `d`.
  - The last two: `ca + dc = −J^{-1}a³ + J^{-1}a³ = 0` and
    `cb + d² = −J^{-1}a²J + J^{-1}a²J = 0`.
* *Uniqueness.*
  - `a` is forced by Sylvester.
  - Given `b = J` invertible, `d = −b^{-1}ab` and `c = −b^{-1}a²` are
    forced by `T² = 0`.
* *Distinct colours.*
  - The slides hold by naturality of `J`, and because the even polynomial
    `Q_ij(X,Y)` slides through `J`.
  - The composite `T_ji T_ij` on the summand `E_i^A E_j^B` is
    `(Q_ij(X,Y) J^{-1}) ∘ J = Q_ij`. On `E_i^B E_j^A` it is
    `J ∘ Q_ji J^{-1}`, which equals `Q_ij` evaluated at the transported dots
    because `Q_ji(v,u) = Q_ij(u,v)`. ∎

The odd diagonal identities are also **Lean**:
`separated_diagonal_crossing` and `commute_inverse_square_difference`
(`OddMath/Diagrams/OddNilHecke/SeparatedCrossing.lean`).

**Proposition c2: the three-strand (braid) relations.**
The relation is `T_1T_2T_1 − T_2T_1T_2 = (KLR correction)` on `E_iE_jE_k`.
In every case the relation transports along a homomorphism, by the
following argument.

*Universal algebra.* Let `α`, `β` be the A- and B-contents.
`L = (R(α) ⊗̂ R(β))[Δ^{-1}]`, where

`Δ = Π_{i even} Π_{k∈A_i, l∈B_i} (x_k − y_l) · Π_{i odd} Π (x_k² − y_l²)`

is the product over A-strands `k` and B-strands `l` of each colour.

1. **(Δ central).** In the even case, `Δ` is symmetric in the dots of each
   colour within each factor, hence central. **cited**: KL1, centre of
   `R(ν)` = symmetric polynomials. That source was read only at its
   faithful-representation section, so no locator is given.
   In the odd case, centrality of symmetric functions in the `x_k²` is
   **OPEN-cited**: the centre of the odd nilHecke / quiver Hecke superalgebra
   in this form was not read in a source.
2. **Block algebra.** `𝓢 = L ⊗ Mat_P(K)`, where `P` is the set of sector
   patterns. The interchange isomorphisms are the matrix units, by
   naturality of `J`.
3. **Θ : 𝓢 → End(⊕_P E^P) is an algebra homomorphism (paper).** It is
   built from the factor actions (H3), the Koszul tensor product, the
   invertibility of the image of `Δ` (Lemma 0), and naturality of `J`.
4. **φ.** The assignment `φ(x_k) = diag_P(x_{P,k})`, `φ(τ_a) = (fused T at
   position a)`, `φ(e(ν)) = Σ_P e(ν)_P` lands in `𝓢`. Every entry of the
   fused `T` is in `L ⊗ Mat_P`.

*Claim (c2).* `φ` extends to an algebra homomorphism `R(α+β) → 𝓢`.
Composing with Θ, the fused data then satisfy all KLR relations of the
original datum. This uses no finite-degree computation and holds for any
number of strands and colours.

**Proof of (c2), even case (paper modulo a cited faithfulness).**

* **Faithful rational forms.**
  - `R(n)` acts faithfully on `Pol = ⊕_ν K[x]e(ν)`:
    * Demazure operators for equal colours;
    * `s_a` or `Q·s_a` for distinct colours.

    **cited**: KL1 §2.3, "A faithful representation and a basis of
    `R(ν)`", heading read. This gives an injective homomorphism
    `R(n) ↪ K_n ⋊ S_n` into the localized twisted group algebra, where
    `K_n = Frac`-localization at differences of same-coloured dots.
  - Explicitly, `τ_a e(ii) ↦ (x_a − x_{a+1})^{-1}(1 − s_a) e(ii)`, up to
    the sign convention of R5. For distinct colours, `τ_a e(ν) ↦ s_a` or
    `Q·s_a`.
  - The same applies to `R(α) ⊗ R(β)`, and since `Δ` is invertible in
    `K_n`, it gives an injection `ι_L : L ↪ K_n ⋊ (S_a × S_b)` (block-wise
    over idempotents).
* **Mackey matrices.** `K_n ⋊ S_n` is a free right module over
  `K_n ⋊ (S_a × S_b)` with basis the minimal shuffle coset representatives
  `w_P`, one per pattern. Left multiplication gives an injective algebra map
  `ψ : K_n ⋊ S_n ↪ Mat_P(K_n ⋊ (S_a × S_b))`.
* **Comparison.**
  - Compute `ψ(τ_a e(ii))` with `τ = Δ_a^{-1}(1 − s_a)`, where
    `Δ_a = x_a − x_{a+1}`.
  - *Same-sector positions*: `s_a w_P = w_P s_b` with `s_b ∈ S_a × S_b`.
    The block is diagonal, equal to the factor's Demazure image.
  - *Cross positions*: `s_a w_P = w_{P'}`. The blocks are
    `(P,P) : Δ_a^{-1}` (transported) and `(P',P) : −Δ_{a}^{-1}`
    (transported) times the matrix unit.
  - Thus `ψ∘KL(τ_a) = g·(ι_L ⊗ 1)(φ(τ_a))·g^{-1}`, where `g` is the diagonal
    gauge `g_P = Π_{(l,k)} γ(x_k, y_l)`. The product runs over the
    inversions of `P` (B-strand `l` left of A-strand `k`), with
    `γ = −(x_k − y_l)^{-1}` for equal colours and `γ = 1` or `Q` for
    distinct colours, matching which orientation KL puts `Q` on.
  - `g` commutes with all dots (all entries are rational in dots).
  - `g` commutes with same-sector crossings at positions `a`, `a+1`
    (both A, or both B). Both strands have the same set of opposite-sector
    strands to their left, so `g_P` is symmetric in their two dots (equal
    colours), or is intertwined by `τ` (distinct colours, using
    `τ x_a e(ν) = x_{a+1} τ e(s_aν)`). Symmetric rational functions with
    central denominators commute with `τ`.
  - The diagonal blocks agree directly: `a = (X − Y)^{-1}` with the R5 sign
    convention. The off-diagonal blocks agree after the gauge: the gauge
    rescales `b` by `γ` and `c` by `γ^{-1}`, so `bc = −a²` is preserved. The
    Demazure blocks satisfy `bc = −a²`, by the same `T² = 0` computation in
    `K_n ⋊ S_n`.
* **Conclusion.** For a KLR relation `w = 0`,
  `(ι_L ⊗ 1)(g^{-1}φ(w)g) = ψ(KL(w)) = 0`. Since `ι_L ⊗ 1` is injective,
  `φ(w) = 0`. ∎

**Status of c2, even:** paper modulo the cited KL1 faithfulness and
centre. Note that `Δ` is needed only for equal-colour cross pairs.

**OPEN (c2-odd).** The same argument needs a faithful rational form of the
quiver Hecke superalgebra. The available read statement is **cited** KKT
Theorem 3.8 (`skm-lit_kkt_1107.1039v2.txt`, l. 1484 ff.): the quiver
Hecke–Clifford superalgebra `RC_n` embeds in the localized twisted
`K S_n`, via `σ_a = s_a + f_a`. Together with KKT Theorem 3.13,
`R_β ⊗ Cℓ ≅ RC^†_β`, this yields an injection
`R(β) ⊗ Cℓ ↪ K S_n ⊗ (Clifford)`, since `⊗ Cℓ` is faithful.

The missing statement is:

> (c2-odd) Under the KKT embedding composed with 3.13, the Mackey blocks of
> `τ_a` at cross-sector equal-colour positions are conjugate, by a diagonal
> gauge commuting with dots and same-sector crossings, to
> `[[a, J], [−J^{-1}a², −J^{-1}aJ]]` with `a = (X−Y)(X²−Y²)^{-1}`. Also,
> the symmetric functions in the `x_k²` used in `Δ` are central.

This is a finite symbolic verification in the localized skew-polynomial ring
on two or three variables with Clifford generators. It was not carried out.
Proposition c1 (two-strand) is fully proved in the odd case. The three-strand
odd identities are exactly what (c2-odd) supplies.

### 5.4 (A2-b) Inversion of the fused Rouquier map

**`i ≠ j` (paper, given H3).** The fused mate `E_iF_j → F_jE_i` is block
diagonal in sectors. The cross crossings `J` and `Q J^{-1}` preserve sector
content, so there is no `AA ↔ BB` component. The blocks are:

* the factor isomorphisms (A1-b) on `AA` and `BB`;
* on the cross summands, the mate of `J`, which is the inverse interchange;
* or the mate of `Q_ij J^{-1}`, which is that interchange composed with
  `Q_ij(x,y)`, invertible by Lemma 0.

Hence the fused map is invertible. ∎

**`i = j`.** Order sources as `(E^AF^A, E^BF^B; cross)` and targets as
`(F^AE^A, F^BE^B; cross)`, with heights `h = h_A + h_B`.

**Lemma b1 (written, under the normalized-left snake).**
`HomSwappingMates.md` evaluates the two actual content-shifted partial mates
of `J` and `−J^{-1}a²`. In its specified coordinates they are
`alpha h_A` and `−beta h_B;g_B`, with explicit Koszul scalars and
`g_B=(X²−W²)(X²+W²)^{-2}` for odd colour, or `(X−W)^{-2}` for even colour.
Here W is the right-transposed probe dot. The first mate has no rational
factor; the second does not retain the unbent expression `a²`.
That note constructs both inverse composites by finite series and actual
unit–map–cap calculations. Projected supports show these blocks decouple
from the central block and introduce no extra Schur term.

The central entries from the diagonal upward coefficients still require
their own C,D transport and normalization comparison. The swapping result
does not establish this comparison or residual inversion. Its statement
is parity-supercategorical; coherent integer word shifts for graded fusion
are not supplied by these two inverses.

The originally proposed remaining `2×2` system was

```
ρ = ⎡ ρ_A   C ⎤ ,     ρ_A, ρ_B = factor Rouquier maps (invertible by H3,
    ⎣ D   ρ_B ⎦      extended by the dotted caps/cups of the fused height)
```

with `C` and `D` given by §5.2. **This is not an established reduction.**
At nonzero heights the factor maps are augmented by identity summands;
their principal inverse blocks are not inverses to the bare crossings.
The associative Schur lemma remains **Lean**:
`SKM.RouquierSchur.isUnit_of_nilpotent_feedback`. `fromBlocks A B C D` is a
unit if `A`, `D` are units and `D^{-1}CA^{-1}B` is nilpotent. The filtration
version is `isUnit_of_feedback_filtration` (`OddMath/SKM/RouquierFeedbackIdeal.lean`).
Its unit hypotheses have not been supplied for the displayed blocks.
The even blueprint retains a residual matrix with positive-height cap rows
and fused dotted-window/negative-height cup columns. Its super counterpart,
including the actual dotted-window comparison, remains **OPEN**.

**Proposed feedback expression (not the full inversion theorem).** Insert §5.2:

`Φ = Σ_{r,s} c_{rs} · u_{B,−s−1} ∘ β_{s,r} ∘ v_{B,−r−1} ∘ r_B`, with
`β_{s,r} := v_{A,s} ∘ r_A ∘ u_{A,r} ∈ End(1_{λ_A})`.

Here `r_A` must denote the **principal inverse block**. Each closure then
belongs to the reservoir identity endomorphisms, with supercentral rather
than ordinary-central commutation. For a homogeneous graded action its
degree is `2d_i(r+s+1)>0`. Bounded-above grading support therefore makes all
sufficiently long products of these closures zero. Supercommuting reservoir
closures past probe operators gives nilpotence of this specified feedback.
The general argument and its explicit hypotheses are in
[FusionReservoirLemma](FusionReservoirLemma.md).
[DeformedReservoirBound](DeformedReservoirBound.md) supplies the homogeneous
action and bounded identity-endomorphism support on each fixed content of
finite coefficient quotients. This is a written result, not a Lean theorem
or an identification of the actual fused feedback.

The earlier radical/degree-zero equivalence is false: a degree-zero algebra
can have a nonzero radical. No such equivalence is needed for the positive-
degree argument. The fixed-content bounds do not assert a uniform bound
over infinite weight fibers; feedback supports and truncation-compatible
separation still have to be established for the intended fusion construction.

Even when these hypotheses hold, the residual identity-summand matrix is
not removed. In `RouqCoproduct`, `isIso_lift_of_schur` retains it and
`schur_const_eq` compares it with a separately inverted partial-fraction
matrix. Opposite nonzero factor heights can leave a nonempty residual
matrix even at total height zero. Thus closure nilpotence alone does not
prove A2-b2.

### 5.5 Assembling A2 into the hypotheses of §3

Given A1, the full residual-matrix comparison and inversion, and all the
crossing and mate comparisons of §5.3–5.4, the proposed construction would
make `𝒱_A ⊠ 𝒱_B` an SKM 2-representation of the original datum.
For the even part, the KLR relations are c1 + c2; for the
odd part they are c1 + (c2-odd). Inversion is §5.4.

The `VacuumSectorBubble` fields are then supplied as follows.

**Supplied (paper):**
* `slide`: c1;
* the sector summands: the decomposition of §5.1;
* `w`, `z`: (H2);
* `hnC`, `hnD`: (H1).

**`fused` — OPEN (A2-fused):**

> The fused bubble of `g`, defined through the inverse of the fused Rouquier
> map, evaluates to the probe-cup–(−q mate)–reservoir-cap composite.

This is a statement about which block of `ρ^{-1}` defines the bubbles. It
follows from the block form of §5.4 once the bubble convention of
`FusedVacuumWords` is matched with it. That matching was not done here.

**`probe`, `reservoirValue`, `normalize`:** these are the vacuum values of
the factors, part of A3.

## 6. Status table

| Step | Statement | Status |
|---|---|---|
| Statement | `SKM.NondegeneracyConjecture` | definition (Lean) |
| B0 | `nondegeneracy_iff_upward_independence` | **Lean** |
| C | `upward_independence_of_fused_sector_actions` | **Lean** (conditional on `∀ μ, FusedSectorAction`) |
| A2-a | mate projection formula from slide + (H1) + (H2) | **Lean** (`MateProjectionFormula.of_sectors`) + paper §5.2 |
| A2-c1 | fused two-strand relations, all parities; forcing of cross blocks | **paper** (odd diagonal also Lean: `separated_diagonal_crossing`) |
| A2-c2 even | braid relations via faithful rational form + Mackey + gauge | **OPEN comparison**: gauge localization requires additional justification |
| A2-c2 odd | same, via KKT Thm 3.8/3.13 | **OPEN** (c2-odd) |
| A2-b, `i≠j` | fused mixed relation | **paper** given (H3) |
| A2-b1 | cross summands decouple | **OPEN comparison**: derive the partial mate on the actual tensor supports |
| A2-b2 | total map invertible | **OPEN**: all-height residual identity-summand matrix; abstract Schur lemma **Lean** |
| Reservoir closures | joint nilpotence | **written fixed-content proof** for finite coefficient quotients, `DeformedReservoirBound.md`; actual feedback identification and separation remain |
| A2-fused | fused bubble = mate composite | **OPEN** |
| A1-b,c | KKO-I Thm 9.1, 9.6 (undeformed) | **cited** (read) |
| A1-map | the specific same-colour Rouquier map is invertible (super) | **written proof**, full-ELV hypotheses: `DeformedMatrixComparison.md`; not yet Lean |
| A0-deform | A1 over the actual ELV coefficient ring | **written standard graded action**, `DeformedGradedAction.md`; Lean implementation open; unrestricted exterior flatness is false |
| A3 | detection weights reachable with probes (even `⟨h_i,Λ_B⟩` at odd `i`); regular identification; vacuum values | **OPEN** |
| B1 | assembly over a field | **OPEN** (formal, once A0–A3 hold) |
| B2 | descent from fields to the coefficient rings of `NondegeneracyConjecture` | **OPEN** |

## 7. What this document establishes

The conditional Lean results and proposed written arguments give:
* Given a slide, the mate projection formula is forced by the spectral
  separation of the dots alone. It is insensitive to crossing data.
* The fused crossing on cross sectors is uniquely forced, up to the
  interchange normalization, by the slides and nilpotence of the square.
  Its two-strand relations hold in all parities.
* A proposed even braid comparison through a faithful rational form; the
  gauge's localization still needs justification.
* A reservoir closure nilpotence argument under explicit graded hypotheses.
  It does not eliminate the remaining residual matrix in fused inversion.

The genuinely open mathematics is concentrated in:
* (c2-odd), a finite symbolic three-strand check in KKT's rational form;
* the full residual-matrix comparison and inversion, including all height signs;
* Lean formalization of A1-map and the written standard integer-graded A0-deform action for the super cyclotomic factors;
* A3.
