/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.RingQuot
import OddMath.CoveringQuantum.Datum
import OddMath.CoveringQuantum.Integers
import OddMath.CoveringQuantum.PreF.Form

/-!
# The half covering quantum group `f`

Brundan–Ellis, arXiv:1701.04133v2 ([BE2]), §10: `f` is the superalgebra on generators `θᵢ`
(`|θᵢ| = |i|`) subject to the quantum Serre relations (10.1)
```
Σ_{r=0}^{dᵢⱼ+1} (-1)ʳ πᵢ^{r|j| + r(r-1)/2} [dᵢⱼ+1, r]_{qᵢ,πᵢ} θᵢ^{dᵢⱼ+1-r} θⱼ θᵢʳ = 0   (i ≠ j),
```
with `dᵢⱼ = -aᵢⱼ`, `qᵢ = q^{dᵢ}`, `πᵢ = π^{|i|}`. `'f ⊗ 'f` carries the twisted multiplication
`(x ⊗ y)(x' ⊗ y') = π^{|y||x'|} q^{-(β,α')} xx' ⊗ yy'`, `r` is the algebra map with
`r(θᵢ) = θᵢ ⊗ 1 + 1 ⊗ θᵢ`, and the bilinear form has `(θᵢ, θⱼ) = δᵢⱼ / (1 - πᵢ qᵢ²)`.

Clark–Hill–Wang, arXiv:1301.1665v2 ([CHW1]), §1.4, *define* `f` as `'f / I`, the quotient of the
free algebra by the radical of the form; the Serre relations hold in it ([CHW1] Prop. 1.7.3), and
[CHW1] Prop. 3.4.1 states that they generate the radical (by the arguments of Lusztig's book,
Ch. 33). [BE2] cites the latter for the form on its `f`.

This file instantiates the general theory of `OddMath.CoveringQuantum.PreF` at the bicharacter
`χ(i, j) = q^{-i·j} π^{|i||j|}` and the normalization `cᵢ = (1 - πᵢ qᵢ²)⁻¹` of [BE2] (over any
commutative ring `k` with a unit `q` and `π² = 1`; `Ring.inverse` is a genuine inverse whenever
`1 - πᵢ qᵢ²` is a unit, e.g. over `ℚ(q)^π`), and defines both algebras:
* `SuperCartanDatum.radicalF`: `'f / I` ([CHW1]);
* `SuperCartanDatum.serreF`: the algebra presented by (10.1) ([BE2]).

## Main definitions

* `SuperCartanDatum.chi C q π`: the bicharacter `χ(i, j) = q^{-i·j} π^{|i||j|}`.
* `SuperCartanDatum.norm C q π i`: `(θᵢ, θᵢ) = (1 - πᵢ qᵢ²)⁻¹`.
* `SuperCartanDatum.form C q π`: the bilinear form on `'f`.
* `SuperCartanDatum.serreElt C q π i j`: the left side of (10.1).
* `SuperCartanDatum.serreF C q π`, `SuperCartanDatum.radicalF C q π`.

## Main results

* `SuperCartanDatum.twistedMul_tmul_tmul`: the twisted multiplication is [BE2]'s.
* `SuperCartanDatum.form_θ_θ`, `SuperCartanDatum.form_mul_left`, `SuperCartanDatum.form_mul_right`,
  `SuperCartanDatum.form_comm`: the defining properties of the form ([BE2] §10, [CHW1] Prop. 1.4.1).
-/

noncomputable section

namespace OddMath.CoveringQuantum

open PreF TensorProduct

variable {I k : Type*} [CommRing k] (C : SuperCartanDatum I) (q : kˣ) (π : k)

namespace SuperCartanDatum

/-- The bicharacter `χ(i, j) = q^{-(αᵢ,αⱼ)} π^{|i||j|}` of the twisted multiplication of
[BE2] §10. -/
def chi : Bichar k I where
  toFun i j := ((q ^ (-C.dot i j) : kˣ) : k) * π ^ (C.parity i * C.parity j).val
  symm i j := by simp only [C.dot_comm i j, mul_comm (C.parity i)]

/-- `qᵢ = q^{dᵢ}`. -/
def qi (i : I) : kˣ := q ^ C.d i

/-- `πᵢ = π^{|i|}`. -/
def pii (i : I) : k := π ^ (C.parity i).val

/-- The normalization `(θᵢ, θᵢ) = (1 - πᵢ qᵢ²)⁻¹` of [BE2] §10 (`Ring.inverse`, a genuine inverse
when `1 - πᵢ qᵢ²` is a unit). -/
def norm (i : I) : k := Ring.inverse (1 - C.pii π i * ((C.qi q i : kˣ) : k) ^ 2)

/-- The weight-level bicharacter is `χ(ν, μ) = q^{-(ν,μ)} π^{p(ν)p(μ)}` on generators. -/
theorem chi_apply (i j : I) :
    C.chi q π i j = ((q ^ (-C.dot i j) : kˣ) : k) * π ^ (C.parity i * C.parity j).val := rfl

/-- The twisted multiplication on `'f ⊗ 'f` of [BE2] §10:
`(x ⊗ y)(x' ⊗ y') = χ(β, α') xx' ⊗ yy'` for `y ∈ 'f_β`, `x' ∈ 'f_{α'}`, where `χ` is the
bicharacter with `χ(i, j) = q^{-(αᵢ,αⱼ)} π^{|i||j|}` (so `χ(β, α') = q^{-(β,α')} π^{|y||x'|}`). -/
theorem twistedMul_tmul_tmul {β α' : I →₀ ℕ} {y x' : PreF k I} (hy : y ∈ weightSpace k β)
    (hx' : x' ∈ weightSpace k α') (x y' : PreF k I) :
    twistedMul (C.chi q π) (x ⊗ₜ y) (x' ⊗ₜ y') = (C.chi q π).wt β α' • ((x * x') ⊗ₜ (y * y')) :=
  PreF.twistedMul_tmul_tmul _ hy hx' x y'

variable [DecidableEq I]

/-- The bilinear form on `'f` of [BE2] §10 (from [CHW1] Prop. 1.4.1). -/
abbrev form : LinearMap.BilinForm k (PreF k I) := PreF.form (C.chi q π) (C.norm q π)

/-- `(θᵢ, θⱼ) = δᵢⱼ / (1 - πᵢ qᵢ²)`. -/
theorem form_θ_θ (i j : I) :
    C.form q π (θ k i) (θ k j) = if i = j then C.norm q π i else 0 :=
  PreF.form_θ_θ _ _ i j

/-- `(xy, z) = (x ⊗ y, r(z))`. -/
theorem form_mul_left (x y z : PreF k I) :
    C.form q π (x * y) z = formTensor (C.chi q π) (C.norm q π) (x ⊗ₜ y) (comul (C.chi q π) z) :=
  PreF.form_mul_left _ _ x y z

/-- `(x, yz) = (r(x), y ⊗ z)`. -/
theorem form_mul_right (x y z : PreF k I) :
    C.form q π x (y * z) = formTensor (C.chi q π) (C.norm q π) (comul (C.chi q π) x) (y ⊗ₜ z) :=
  PreF.form_mul_right _ _ x y z

/-- The form is symmetric. -/
theorem form_comm (x y : PreF k I) : C.form q π x y = C.form q π y x := PreF.form_comm _ _ x y

/-- [CHW1]'s `f = 'f / I`: the quotient of the free algebra by the radical of the form. -/
abbrev radicalF := PreF.Quotient (C.chi q π) (C.norm q π)

end SuperCartanDatum

namespace SuperCartanDatum

/-- `N = dᵢⱼ + 1 = 1 - aᵢⱼ` (as a natural number; `aᵢⱼ ≤ 0` for `i ≠ j`). -/
def serreDeg (i j : I) : ℕ := (1 - C.a i j).toNat

/-- The coefficient `(-1)ʳ πᵢ^{r|j| + r(r-1)/2} [N, r]_{qᵢ,πᵢ}` of (10.1). -/
def serreCoeff (i j : I) (r : ℕ) : k :=
  (-1) ^ r * C.pii π i ^ (r * (C.parity j).val + r * (r - 1) / 2) *
    qpBinom (C.qi q i) (C.pii π i) (C.serreDeg i j) r

/-- The left side of the quantum Serre relation (10.1) in `'f`:
`Σ_{r=0}^{N} (-1)ʳ πᵢ^{r|j| + r(r-1)/2} [N, r]_{qᵢ,πᵢ} θᵢ^{N-r} θⱼ θᵢʳ`, `N = 1 - aᵢⱼ`. -/
def serreElt (i j : I) : PreF k I :=
  ∑ r ∈ Finset.range (C.serreDeg i j + 1),
    C.serreCoeff q π i j r • (θ k i ^ (C.serreDeg i j - r) * θ k j * θ k i ^ r)

/-- The relations (10.1), `serreElt i j = 0` for `i ≠ j`. -/
inductive SerreRel : PreF k I → PreF k I → Prop
  | serre (i j : I) (h : i ≠ j) : SerreRel (C.serreElt q π i j) 0

/-- [BE2]'s `f`: the algebra generated by the `θᵢ` subject to the quantum Serre relations
(10.1). -/
abbrev serreF := RingQuot (C.SerreRel q π)

/-- The projection `'f → f`. -/
def toSerreF : PreF k I →ₐ[k] C.serreF q π := RingQuot.mkAlgHom k (C.SerreRel q π)

theorem toSerreF_serreElt {i j : I} (h : i ≠ j) : C.toSerreF q π (C.serreElt q π i j) = 0 := by
  rw [toSerreF, RingQuot.mkAlgHom_rel k (SerreRel.serre i j h), map_zero]

theorem toSerreF_surjective : Function.Surjective (C.toSerreF q π) :=
  RingQuot.mkAlgHom_surjective k _

end SuperCartanDatum

end OddMath.CoveringQuantum
