import OddMath.QuiverHecke.SwappedAssembly.Supernatural.MatrixInverse
import OddMath.Algebra.HomogeneousSuperfunctorIso
import Mathlib.CategoryTheory.Preadditive.Mat
import OddMath.SKM.AugmentedInverseEvaluation

/-! # Lifting evaluated finite matrix inverses

For the central augmented matrices of Brundan–Ellis (1.13)–(1.14),
pointwise inverses assemble into natural matrix inverses. Their naturality
and parity follow from the prescribed homogeneous forward matrix;
no naturality premise is imposed on the chosen component inverses.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.SwappedAssembly.MatrixEvaluation
universe u v w r s
variable {k : Type u} [CommRing k]
  {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C] [Supercategory k C]
  {D : Type r} [Category.{s} D] [Preadditive D] [Linear k D] [Supercategory k D]

/-- The actual objectwise evaluation of a finite family of superfunctors. -/
def obj (F : Mat_ (Superfunctor k C D)) (M : C) : Mat_ D :=
  ⟨F.ι, fun i => (F.X i).obj M⟩

/-- Evaluate every given matrix entry at its total component. -/
def map {F G : Mat_ (Superfunctor k C D)} (f : F ⟶ G) (M : C) :
    obj F M ⟶ obj G M := fun i j => (f i j).total M

theorem map_comp {F G H : Mat_ (Superfunctor k C D)} (f : F ⟶ G) (g : G ⟶ H) (M : C) :
    map (f ≫ g) M = map f M ≫ map g M := by
  ext i j
  change (∑ l, f i l ≫ g l j).total M = ∑ l, (f i l).total M ≫ (g l j).total M
  change (SKM.superfunctorTotalEvaluation M).map (∑ l, f i l ≫ g l j) = _
  rw [CategoryTheory.Functor.map_sum]
  apply Finset.sum_congr rfl
  intro l _
  exact Superfunctor.comp_total _ _ M

theorem map_id (F : Mat_ (Superfunctor k C D)) (M : C) : map (𝟙 F) M = 𝟙 (obj F M) := by
  classical
  apply Mat_.hom_ext
  intro i j
  change ((𝟙 F : F ⟶ F) i j).total M = (𝟙 (obj F M) : obj F M ⟶ obj F M) i j
  by_cases hij : i = j
  · subst j
    rw [Mat_.id_apply_self, Mat_.id_apply_self]
    exact SuperNatTrans.id_total (F.X i).toFunctor M
  · rw [Mat_.id_apply_of_ne F i j hij, Mat_.id_apply_of_ne (obj F M) i j hij]
    exact (SKM.superfunctorTotalEvaluation M).map_zero _ _

end OddMath.QuiverHecke.SwappedAssembly.MatrixEvaluation
