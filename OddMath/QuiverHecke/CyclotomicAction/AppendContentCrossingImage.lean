/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendContentRhoCoordinates

/-!
# Crossing tensors in the append content target

The target-image step of `DeformedMackeyBoundary.md` (4)–(5). We identify
precisely the crossing range in the prescribed target and descend algebraic
left-crossing sums to it with their coefficients in the original order.
The final short-shuffle multiplier factorization is not assumed or asserted.
The content index `n` has old height `n + 1`, including when `n = 0`.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Categorification.InductionAlong
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (n : ℕ) (β : Multiset I) (i : I)
local notation "B" => CyclotomicContentCorner D Sc a n β
local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
local notation "T" => Ind B ψ
local notation "eps" => appendContentParity D a β i
local notation "coord" => prependTwistCoordinates D Sc i n eps B

/-- Polynomial projection of the prescribed target decomposition. -/
def appendContentPolynomialProjection : appendTensorFixed D Sc i n B →+ (ℕ →₀ B) :=
  (AddMonoidHom.snd _ _).comp (appendTensorCornerEquiv D Sc i n B).symm.toAddMonoidHom

/-- The kernel is proved from the balanced coordinate equivalence, not postulated. -/
theorem appendContentPolynomialProjection_ker :
    (appendContentPolynomialProjection D Sc a n β i).ker =
      (appendTargetF D Sc i n B).range := by
  ext y
  change ((appendTensorCornerEquiv D Sc i n B).symm y).2 = 0 ↔ _
  constructor
  · intro h
    refine ⟨((appendTensorCornerEquiv D Sc i n B).symm y).1, ?_⟩
    change appendTensorCornerEquiv D Sc i n B (_, 0) = y
    rw [← h]
    exact (appendTensorCornerEquiv D Sc i n B).apply_symm_apply y
  · rintro ⟨x, rfl⟩
    change ((appendTensorCornerEquiv D Sc i n B).symm
      (appendTensorCornerEquiv D Sc i n B (x, 0))).2 = 0
    rw [AddEquiv.symm_apply_apply]

/-- Algebraic crossing coefficients descend by `c ↦ ψ'(1)c • b`.
No right coefficient is moved past a crossing or past another coefficient. -/
def appendContentCrossingCoefficients
    (f : (Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) (b : B) :
    appendTensorLeftCoordinates D Sc i n B :=
  ⟨Finsupp.mapRange (fun c => (appendAlgebra D Sc i n 1 * c) • b)
      (by rw [mul_zero]; exact zero_smul (Hn D Sc (n + 1)) b) f, fun q => by
    change _ • ((_ * f q) • b) = (_ * f q) • b
    rw [← mul_smul, ← mul_assoc, ← map_mul, one_mul]⟩

/-- The crossing tensor with an arbitrary finite algebra coefficient family. -/
def appendContentCrossingTensor
    (f : (Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) (b : B) :
    appendTensorFixed D Sc i n B :=
  ⟨Ind.tmul (appendFamilyCorner D Sc i n (appendLeftSum D Sc i n)
      (appendLeftSum_mul_appendOne D Sc i n) f) b, by
    change (ψ 1 : Hn D Sc (n + 1 + 1)) • _ = _
    rw [Ind.smul_tmul]
    congr 1
    exact Subtype.ext (appendLeftSum_mem_appendTwoSidedCorner D Sc i n f).1⟩

/-- Explicit inclusion of the algebraic crossing tensors into the prescribed `F` image. -/
theorem appendContentCrossingTensor_eq_F
    (f : (Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) (b : B) :
    appendContentCrossingTensor D Sc a n β i f b =
      appendTargetF D Sc i n B (appendContentCrossingCoefficients D Sc a n β i f b) := by
  apply Subtype.ext
  rw [appendTargetF_coe]
  change Ind.tmul (appendFamilyCorner D Sc i n (appendLeftSum D Sc i n)
    (appendLeftSum_mul_appendOne D Sc i n) f) b = _
  have h := appendFamilyTensor_coefficients D Sc i n B (appendLeftSum D Sc i n)
    (appendLeftSum_mul_appendOne D Sc i n) (appendLeftSum_single_right D Sc i n)
    (appendLeftProj D Sc i n f) b
  have he : Finsupp.mapRange (fun c : Hn D Sc (n + 1) => c • b) (zero_smul _ b)
      (appendLeftProj D Sc i n f) =
      (appendContentCrossingCoefficients D Sc a n β i f b).1 := by
    ext q
    rfl
  rw [he] at h
  rw [h]
  congr 1
  apply Subtype.ext
  exact (appendLeftSum_appendLeftProj D Sc i n f).symm

/-- The prescribed target's `F`, with no change of image or target module. -/
theorem appendContentCrossingTensor_mem_range (ha : CyclotomicPolynomialParity D a)
    (f : (Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) (b : B) :
    appendContentCrossingTensor D Sc a n β i f b ∈
      (appendContentMackeyTarget D Sc a n β i ha).F.range :=
  ⟨appendContentCrossingCoefficients D Sc a n β i f b,
    (appendContentCrossingTensor_eq_F D Sc a n β i f b).symm⟩

/-- Project arbitrary source PBW coordinates into the left append corner. -/
def appendContentProjectCoordinates :
    ((PrependShuffle (n + 1) × ℕ) →₀ B) →+ appendContentSource D Sc a n β i where
  toFun f := ⟨(ψ 1 : Hn D Sc (n + 1 + 1)) • coord f, by
    change (ψ 1 : Hn D Sc (n + 1 + 1)) • ((ψ 1 : Hn D Sc (n + 1 + 1)) • _) = _
    rw [← mul_smul, ← map_mul, one_mul]⟩
  map_zero' := Subtype.ext (by
    change (ψ 1 : Hn D Sc (n + 1 + 1)) • coord 0 = 0
    rw [map_zero, smul_zero])
  map_add' f g := Subtype.ext (by
    change (ψ 1 : Hn D Sc (n + 1 + 1)) • coord (f + g) =
      (ψ 1 : Hn D Sc (n + 1 + 1)) • coord f + (ψ 1 : Hn D Sc (n + 1 + 1)) • coord g
    rw [map_add, smul_add])

/-- Projection of the full coordinate expansion recovers the source element. -/
theorem appendContentProjectCoordinates_inverse (z : appendContentSource D Sc a n β i) :
    appendContentProjectCoordinates D Sc a n β i ((coord).symm z.1) = z := by
  apply Subtype.ext
  change (ψ 1 : Hn D Sc (n + 1 + 1)) • coord ((coord).symm z.1) = z.1
  rw [AddEquiv.apply_symm_apply]
  exact z.2

/-- The prescribed `P` on every projected input PBW generator, retaining the right coefficient.
This is the concrete multiplier whose short-shuffle factorization remains to be proved. -/
theorem appendContentP_project_single (ha : CyclotomicPolynomialParity D a)
    (u : PrependShuffle (n + 1)) (m : ℕ) (b : B) :
    (appendContentP D Sc a n β i ha
      (appendContentProjectCoordinates D Sc a n β i (Finsupp.single (u, m) b))).1 =
      (ψ 1 : Hn D Sc (n + 1 + 1)) •
        Ind.tmul ⟨prependPBWTerm D Sc i u m 1 * appendMoveMatrix D Sc a i n,
          Ind.mul_mem_of_mul_right (appendMoveMatrix_mul_appendOne D Sc a i n) _⟩ b := by
  change appendMackeyMap D Sc ha (contentCorner_cyclotomic_smul D Sc a n β)
    (contentCorner_appendQ_smul D Sc a n β i) ((ψ 1 : Hn D Sc (n + 1 + 1)) •
      coord (Finsupp.single (u, m) b)) = _
  rw [LinearMap.map_smul, prependTwistCoordinates_single, appendMackeyMap_tmul]
  rfl

/-- Short inputs have a finite expansion of these prescribed projected generators,
with the full moving-shuffle row absent. -/
theorem appendContentP_short_expansion (ha : CyclotomicPolynomialParity D a)
    (z : appendContentSource D Sc a n β i) (hz : z ∈ appendContentShort D Sc a n β i) :
    ∃ f : (PrependShuffle (n + 1) × ℕ) →₀ B,
      (∀ m, f (longPrependShuffle (n + 1), m) = 0) ∧
      appendContentP D Sc a n β i ha z =
        f.sum (fun q b => appendContentP D Sc a n β i ha
          (appendContentProjectCoordinates D Sc a n β i (Finsupp.single q b))) := by
  refine ⟨(coord).symm z.1, (mem_appendContentShort_iff D Sc a n β i z).mp hz, ?_⟩
  have h (f : (PrependShuffle (n + 1) × ℕ) →₀ B) :
      appendContentP D Sc a n β i ha (appendContentProjectCoordinates D Sc a n β i f) =
        f.sum (fun q b => appendContentP D Sc a n β i ha
          (appendContentProjectCoordinates D Sc a n β i (Finsupp.single q b))) := by
    conv_lhs => rw [← Finsupp.sum_single f]
    rw [map_finsuppSum, map_finsuppSum]
  exact (congrArg (appendContentP D Sc a n β i ha)
    (appendContentProjectCoordinates_inverse D Sc a n β i z)).symm.trans (h _)

/-- A concrete algebraic factorization suffices for an individual PBW image.
The hypothesis is an equality in the affine matrix algebra, not a kernel or
Mackey-coset hypothesis. -/
theorem appendContentP_project_single_mem_of_factorization
    (ha : CyclotomicPolynomialParity D a) (u : PrependShuffle (n + 1)) (m : ℕ) (b : B)
    (f : (Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1))
    (hf : appendAlgebra D Sc i (n + 1) 1 *
      (prependPBWTerm D Sc i u m 1 * appendMoveMatrix D Sc a i n) =
        appendLeftSum D Sc i n f) :
    appendContentP D Sc a n β i ha
      (appendContentProjectCoordinates D Sc a n β i (Finsupp.single (u, m) b)) ∈
        (appendContentMackeyTarget D Sc a n β i ha).F.range := by
  have h : appendContentP D Sc a n β i ha
      (appendContentProjectCoordinates D Sc a n β i (Finsupp.single (u, m) b)) =
        appendContentCrossingTensor D Sc a n β i f b := by
    apply Subtype.ext
    rw [appendContentP_project_single, Ind.smul_tmul]
    change Ind.tmul _ b = Ind.tmul _ b
    congr 1
    exact Subtype.ext hf
  rw [h]
  exact appendContentCrossingTensor_mem_range D Sc a n β i ha f b

/-- Reduction of the short-image inclusion to explicit affine multiplier factorizations.
This is an intermediate statement: factorization for every short shuffle remains open.
It does not construct `MackeyCosets` from an unproved `P_short` field. -/
theorem appendContentP_short_mem_of_factorizations
    (ha : CyclotomicPolynomialParity D a)
    (hfactor : ∀ u : PrependShuffle (n + 1), u ≠ longPrependShuffle (n + 1) → ∀ m : ℕ,
      ∃ f : (Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1),
        appendAlgebra D Sc i (n + 1) 1 *
          (prependPBWTerm D Sc i u m 1 * appendMoveMatrix D Sc a i n) =
            appendLeftSum D Sc i n f)
    (z : appendContentSource D Sc a n β i) (hz : z ∈ appendContentShort D Sc a n β i) :
    appendContentP D Sc a n β i ha z ∈
      (appendContentMackeyTarget D Sc a n β i ha).F.range := by
  obtain ⟨f, hf, he⟩ := appendContentP_short_expansion D Sc a n β i ha z hz
  rw [he, Finsupp.sum]
  apply AddSubgroup.sum_mem
  intro q hq
  have hshort : q.1 ≠ longPrependShuffle (n + 1) := by
    intro h
    have hzq : f q = 0 := by
      have := hf q.2
      simpa only [← h, Prod.mk.eta] using this
    exact (Finsupp.mem_support_iff.mp hq) hzq
  obtain ⟨g, hg⟩ := hfactor q.1 hshort q.2
  exact appendContentP_project_single_mem_of_factorization D Sc a n β i ha q.1 q.2 (f q) g hg

end OddMath.QuiverHecke
