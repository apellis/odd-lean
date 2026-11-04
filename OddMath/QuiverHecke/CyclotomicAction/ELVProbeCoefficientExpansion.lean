import OddMath.QuiverHecke.CyclotomicAction.ELVProbeDenominatorUnits
import OddMath.QuiverHecke.SwappedAssembly.Generators.CrossCoeffExpansion

/-! # Component expansions of the constructed probe–reservoir coefficient

`SwappedHomInversion.md` §3 (2)–(3): evaluate the prescribed crossing
coefficient at a component reservoir bound, with its whole probe-dot
unit and inverse identities supplied by the constructed factor pair.
-/
noncomputable section
open scoped Classical BigOperators
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction SwappedAssembly
universe u
private def even_coefficient_expansion {R : Type*} [Ring R] (x y a : R) : Prop :=
  ∃ n : ℕ, y ^ n = 0 ∧
    a = -∑ r ∈ Finset.range n, Ring.inverse x ^ (r + 1) * y ^ r

private def odd_coefficient_expansion {R : Type*} [Ring R] (x y a : R) : Prop :=
  ∃ n : ℕ, y ^ n = 0 ∧
    a = ∑ r ∈ Finset.range (2 * n), (-1 : R) ^ r * Ring.inverse x ^ (r + 1) * y ^ r

section EvaluatedCoefficient
universe uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : SKM.Datum I X} {Sc : SKM.Scalars D k}
  (P : ProbeReservoir k B D Sc) (c : P.CrossCoeff Sc)
  (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
  (Z : P.H (nextSector (true, i) true (nextSector (true, i) false t)))
  {R : Type*} [Ring R] (φ : End (P.rpObj i i t hv Z) →+* R)

private def evaluated_even_coefficient_expansion : Prop :=
  even_coefficient_expansion (φ (P.rpPreDot i t hv Z))
    (φ (P.rpPostDot i t hv Z)) (φ (c.a i t hv Z))

private def evaluated_odd_coefficient_expansion : Prop :=
  odd_coefficient_expansion (φ (P.rpPreDot i t hv Z))
    (φ (P.rpPostDot i t hv Z)) (φ (c.a i t hv Z))
end EvaluatedCoefficient

local instance probeCoefficientHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ) (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR

section Mixed
/-- The actual mixed coefficient inverse identity determines its even expansion
at the component's constructed reservoir bound. -/
theorem elvProbeMixedCoefficient_even_expansion [Finite I]
    (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H
      (nextSector (true, i) true (nextSector (true, i) false t)))
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (c : (P).CrossCoeff Sc) (hInv : c.IsInverse) (hi : D.parity i = 0)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t)) :
    let φ := elvProbeMixedEndEvaluation D Sc m cutoff bound ΛP ΛR hP hR i t hv Z M δ
    ∃ n : ℕ, φ ((P).rpPostDot i t hv Z) ^ n = 0 ∧
      φ ((c).a i t hv Z) = -∑ r ∈ Finset.range n,
        Ring.inverse (φ ((P).rpPreDot i t hv Z)) ^ (r + 1) * φ ((P).rpPostDot i t hv Z) ^ r := by
  dsimp only
  let φ := elvProbeMixedEndEvaluation D Sc m cutoff bound ΛP ΛR hP hR i t hv Z M δ
  obtain ⟨n, hn⟩ := elvProbeMixedPostDot_isNilpotent D Sc m cutoff bound ΛP ΛR hP hR i t hv Z sy hc M δ
  exact ⟨n, hn, (P).crossCoeff_even_evaluate c i t hv Z φ.toRingHom hInv hi
    (elvProbeMixedInnerDot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i t hv Z M δ) n hn⟩

/-- The odd inverse identity fixes the ordered signed expansion at the same
component bound; its coefficient is the literal mixed crossing entry. -/
theorem elvProbeMixedCoefficient_odd_expansion [Finite I]
    (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H
      (nextSector (true, i) true (nextSector (true, i) false t)))
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (c : (P).CrossCoeff Sc) (hInv : c.IsInverse) (hi : D.parity i = 1)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t)) :
    let φ := elvProbeMixedEndEvaluation D Sc m cutoff bound ΛP ΛR hP hR i t hv Z M δ
    ∃ n : ℕ, φ ((P).rpPostDot i t hv Z) ^ n = 0 ∧
      φ ((c).a i t hv Z) = ∑ r ∈ Finset.range (2 * n),
        (-1 : End ((((P).rpObj i i t hv Z).obj M) δ)) ^ r *
          Ring.inverse (φ ((P).rpPreDot i t hv Z)) ^ (r + 1) *
          φ ((P).rpPostDot i t hv Z) ^ r := by
  dsimp only
  let φ := elvProbeMixedEndEvaluation D Sc m cutoff bound ΛP ΛR hP hR i t hv Z M δ
  obtain ⟨n, hn⟩ := elvProbeMixedPostDot_isNilpotent D Sc m cutoff bound ΛP ΛR hP hR i t hv Z sy hc M δ
  exact ⟨n, hn, (P).crossCoeff_odd_evaluate c i t hv Z φ.toRingHom hInv hi
    (elvProbeMixedInnerDot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i t hv Z M δ) n hn⟩

end Mixed

section CoefficientExpansion

/-- The finite even geometric expansion of a mixed crossing entry at one component. -/
def elvProbeEvenCoefficientExpansion
    (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H
      (nextSector (true, i) true (nextSector (true, i) false t)))
    (c : (P).CrossCoeff Sc)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t)) : Prop :=
  let φ := elvProbeMixedEndEvaluation D Sc m cutoff bound ΛP ΛR hP hR i t hv Z M δ
  evaluated_even_coefficient_expansion (P) c i t hv Z φ.toRingHom

/-- The finite signed odd expansion of a mixed crossing entry at one component. -/
def elvProbeOddCoefficientExpansion
    (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H
      (nextSector (true, i) true (nextSector (true, i) false t)))
    (c : (P).CrossCoeff Sc)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t)) : Prop :=
  let φ := elvProbeMixedEndEvaluation D Sc m cutoff bound ΛP ΛR hP hR i t hv Z M δ
  evaluated_odd_coefficient_expansion (P) c i t hv Z φ.toRingHom

/-- The constructed crossing coefficient has the finite even expansion.
Its inverse identity and component reservoir bound are both proved inputs. -/
theorem elvProbeCrossCoeff_even_expansion [Finite I]
    (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H
      (nextSector (true, i) true (nextSector (true, i) false t)))
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t))
    (hi : D.parity i = 0) :
    elvProbeEvenCoefficientExpansion D Sc m cutoff bound ΛP ΛR hP hR i t hv Z
      (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc) M δ :=
  elvProbeMixedCoefficient_even_expansion D Sc m cutoff bound ΛP ΛR hP hR i t hv Z sy hc
    (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc)
    (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc) hi M δ

/-- The constructed crossing coefficient has the finite signed odd expansion.
No inverse identity or whole-reservoir bound is assumed. -/
theorem elvProbeCrossCoeff_odd_expansion [Finite I]
    (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H
      (nextSector (true, i) true (nextSector (true, i) false t)))
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (M : (P).T.obj (-(P).muP t)) (δ : WeightBlocks D ΛR ((P).muM t))
    (hi : D.parity i = 1) :
    elvProbeOddCoefficientExpansion D Sc m cutoff bound ΛP ΛR hP hR i t hv Z
      (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc) M δ :=
  elvProbeMixedCoefficient_odd_expansion D Sc m cutoff bound ΛP ΛR hP hR i t hv Z sy hc
    (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc)
    (elvProbeCrossCoeff_isInverse D Sc m cutoff bound ΛP ΛR hP hR sy hc) hi M δ

end CoefficientExpansion

end OddMath.QuiverHecke
