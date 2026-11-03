import OddMath.QuiverHecke.CyclotomicAction.ELVWeightPairDotCoordinates
import OddMath.Algebra.FiniteSupermoduleFunctor

/-! # The selected pair comparison intertwines both prescribed dots

Brundan--Ellis (1.9), supporting the positioned dots in its repeated-outer
correction. The existing component-coordinate squares are retained as
whole module-map identities, so the last induction can act on them.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem moduleCoordinate_map
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M N : Superfunctor k C (SVec k)} (e : M ≅ N) (x : End M) (z : End N)
    (h : ∀ w, ModuleCoordinateSquare e x w (z.total w)) :
    x ≫ e.hom = e.hom ≫ z := by
  apply FiniteSupermodule.hom_ext_total
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  exact h w

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₂)
  (β : WeightBlocks D Λ x₀)
local notation "β₂" => blockSucc₂ D i j Λ h₁ h₂ β
local notation "hP" => elvWeightPair_content_eq D i j Λ h₁ h₂ β β₂ rfl
local notation "C₂" => elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β β₂ rfl

/-- The first prescribed weight dot intertwines as a whole module map
through the pair chart used by the independently given crossing. -/
theorem elvWeightPairComparison_inner_map
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvInductionComponent D Sc cutoff bound i Λ h₂ β₂).map
        ((elvWeightDot D Sc cutoff bound j Λ h₁).app (D.parity j) M) ≫ (C₂).hom.app M =
      (C₂).hom.app M ≫
        (contentInductionTransform D Sc cutoff bound hP hP
          (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [i]))
            (firstDot_parity D Sc j []))).app (D.parity j) (M β) := by
  apply moduleCoordinate_map ((C₂).app M)
  intro w
  rw [contentInductionTransform_total]
  exact elvWeightPairComparison_inner_total D Sc cutoff bound i j Λ h₁ h₂ β M w

/-- The second prescribed weight dot uses the same selected pair chart,
with its affine left context and full coefficient twist retained. -/
theorem elvWeightPairComparison_outer_map
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    elvWeightDotComponent D Sc cutoff bound i Λ h₂ (D.parity i)
        ((elvEFunctor D Sc cutoff bound j Λ h₁).obj M) β₂ ≫ (C₂).hom.app M =
      (C₂).hom.app M ≫
        (contentInductionTransform D Sc cutoff bound hP hP
          (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [j]))
            (firstDot_parity D Sc i []))).app (D.parity i) (M β) := by
  apply moduleCoordinate_map ((C₂).app M)
  intro w
  rw [contentInductionTransform_total]
  exact elvWeightPairComparison_outer_total D Sc cutoff bound i j Λ h₁ h₂ β M w

end OddMath.QuiverHecke.ELVOld
