# Full ELV append polynomial projection and crossing splitting

The producer is `OddMath/QuiverHecke/CyclotomicAction/ELVAppendC0Candidate.lean`.
The construction starts as `appendC0Candidate`; after its recovery and full-crossing
laws are proved, the actual projection is exported as `appendC0`.

Write

- `A = AppendTarget D Sc cutoff i v (t ++ [i])`;
- `P = ℕ →₀ Old D Sc cutoff v t`;
- `j = appendOutputEmbedding D Sc cutoff i v t`;
- `C = appendCrossingSpan D Sc cutoff i v t`.

Here `C` is the span of the genuine `appendCrossingClass r g`, for every old
intermediate word and arbitrary full old arrows on both sides. It is not an
assumed kernel or a selected PBW subspace.

## Construction and quotient compatibility

Decode the already descended input-tail coordinates. For an identity tail the
functional returns the moving-degree monomial with the old quotient coefficient.
For a nonidentity tail it instead composes that coefficient with the explicit
all-power output correction `appendCrossingCorrection` on the stripped canonical
word. Thus nonidentity input rows contribute actual output-polynomial terms.

The coefficient pairing uses the existing quotient composition `oldComp`, which
has descended through both old ideal arguments. The input coordinate equivalence
is already defined on the full old-relation quotient. No scalar freeness,
flatness, chosen complement, or injectivity assumption enters this construction.

To pass from canonical rows to every right old arrow, expand that arrow in full
ELV append PBW coordinates, retain `coefficientTwist` when factoring its old
coefficient, and use `crossLast_comp_rightContext` with the total old-Hom twist.
The canonical run analysis treats old height zero separately; it has no
nonidentity crossing row.

## Verified laws

- `appendC0_embedding`: `C0 (j f) = f`.
- `appendC0_crossing`: `C0 (appendCrossingClass r g) = 0` for arbitrary full old
  arrows `r` and `g`.
- `appendC0_ker`: `ker C0 = C`.
- `appendCrossingSpan_sup_output`: `C ⊔ range j = ⊤`.
- `appendCrossingSpan_disjoint_output`: `C` and `range j` are disjoint.
- `appendOutputEmbedding_injective`: the specified output embedding is injective.
- `appendC0Splitting`: the concrete linear equivalence `A ≃ₗ[k] C × P`.

The prescribed augmented inverse is literal:

```
z ↦ (z - j (C0 z), C0 z),
(c, f) ↦ c + j f.
```

The generic consumer checks this formula and its reconstruction against the
actual maps, not a replacement interface.

## Global output-dot defect

Let `Dout` be `appendOutputDot`, let `T` be `appendOutputShift`, and set

```
δ = C0 ∘ Dout - T ∘ C0.
```

`appendC0Defect_degreeZero` proves for every `z : A` that

```
δ(z) = single 0 (δ(z) 0).
```

Equivalently, `appendC0_outputDot` gives

```
C0 (Dout z) = T (C0 z) + single 0 (δ(z) 0).
```

For a genuine crossing and `a = zsign k (parity i * parity i)`, the checked local
output-dot identity now yields the global formula

```
δ(appendCrossingClass r g)
  = -a • single 0 (q (r ≫ twist k (parity i) g)).
```

In odd parity the coefficient is positive. No polynomial linearity of `C0` is
asserted; that would discard this constant defect. Degree zero here means the
moving polynomial exponent. No new integer-graded Hom infrastructure or further
homogeneous-degree theorem is introduced.

## Scope and checks

All statements retain arbitrary colours, `CommRing k`, cutoff and parity. They
require no finite-colour, domain, nonzero-ring, inverse-of-two, old-quotient
flatness, or assumed splitting hypotheses.

The scoped warnings-as-errors producer build and default-Lean generic consumer
pass. Complete production and consumer declaration inventories, including private
and generated declarations, are restricted to `propext`, `Classical.choice`, and
`Quot.sound`. Checked prerequisite producers are unchanged.

This result supplies the polynomial/crossing splitting and the global constant
defect. It does not claim the separate corrected-rho/S construction, its integer
degree theorem, or the final general nondegeneracy theorem.
