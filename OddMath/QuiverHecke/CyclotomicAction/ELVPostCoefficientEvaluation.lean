import OddMath.Algebra.HomogeneousSuperfunctorIso
import OddMath.QuiverHecke.CyclotomicAction.ELVEndEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightDenominatorUnits
import OddMath.QuiverHecke.SwappedAssembly.Generators.CrossCoeffExpansion

/-! # Coefficient expansions at the chosen ELV output component

`SwappedHomInversion.md` §3 (3) and §4: evaluate at the actual reservoir
output block and supply its constructed nilpotence bound. The bound may
vary with the block; no full-weight support bound is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open SwappedAssembly CyclotomicAction
universe u v w
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C] [Supercategory k C]
  (F : Superfunctor k C (ELVWeightProduct D Sc cutoff bound Λ x))
local notation "G" => elvPostInduction D Sc cutoff bound i Λ h F
local notation "Y" => elvPostDot D Sc cutoff bound i Λ h F

/-- Total supernatural evaluation followed by the literal output projection. -/
def elvPostEndEvaluation (M : C) (δ : WeightBlocks D Λ y) :
    End G →ₐ[k] End (((G).obj M) δ) :=
  (piEndEvaluation ((G).obj M) δ).comp (supernaturalEndEvaluation G M)

/-- Evaluation retains the prescribed component of a homogeneous endomorphism. -/
theorem elvPostEndEvaluation_of_mem (M : C) (δ : WeightBlocks D Λ y)
    (f : End G) {p : ZMod 2} (hf : f ∈ parity (R := k) _ _ p) :
    elvPostEndEvaluation D Sc cutoff bound i Λ h F M δ f = f.app p M δ := by
  change f.total M δ = f.app p M δ
  exact congrArg (fun a : End ((G).obj M) => a δ) (OddMath.HomogeneousSuperfunctorIso.total_eq_app f hf M)

/-- The evaluated chosen postdot has its already constructed component bound. -/
theorem elvPostEndEvaluation_dot_isNilpotent [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound)
    (M : C) (δ : WeightBlocks D Λ y) :
    IsNilpotent (elvPostEndEvaluation D Sc cutoff bound i Λ h F M δ Y) := by
  rw [elvPostEndEvaluation_of_mem D Sc cutoff bound i Λ h F M δ Y
    (elvPostDot_mem D Sc cutoff bound i Λ h F)]
  exact elvPostDot_component_isNilpotent D Sc cutoff bound hdot i Λ h F M δ

/-- The even finite expansion uses an actual output bound, supplied here. -/
theorem elvPostCoefficient_even_expansion [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound)
    (X a : End G) (hx : IsUnit X) (hxy : Commute X Y) (ha : a * (Y - X) = 1)
    (M : C) (δ : WeightBlocks D Λ y) :
    let φ := elvPostEndEvaluation D Sc cutoff bound i Λ h F M δ
    ∃ n : ℕ, φ Y ^ n = 0 ∧
      φ a = -∑ r ∈ Finset.range n, Ring.inverse (φ X) ^ (r + 1) * φ Y ^ r := by
  dsimp only
  obtain ⟨n, hn⟩ := elvPostEndEvaluation_dot_isNilpotent D Sc cutoff bound i Λ h F hdot M δ
  let φ := elvPostEndEvaluation D Sc cutoff bound i Λ h F M δ
  exact ⟨n, hn, mixedCoefficient_even_map_expansion φ.toRingHom X Y a
    (hx.map φ.toRingHom) hxy ha n hn⟩

end OddMath.QuiverHecke.ELVOld
