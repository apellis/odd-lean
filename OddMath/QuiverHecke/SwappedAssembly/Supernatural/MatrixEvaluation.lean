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

/-- Component matrices detect equality of the whole natural matrix. -/
theorem map_ext {F G : Mat_ (Superfunctor k C D)} {f g : F ⟶ G}
    (h : ∀ M, map f M = map g M) : f = g := by
  apply Mat_.hom_ext
  intro i j
  apply HomogeneousSuperfunctorIso.total_ext
  intro M
  exact congrFun (congrFun (h M) i) j

/-- A matrix with target-indexed parity is invertible if every evaluated matrix is. -/
theorem isIso_of_components_target {F G : Mat_ (Superfunctor k C D)} (f : F ⟶ G) (ρ : G.ι → ZMod 2)
    (hf : ∀ i j, f i j ∈ parity (R := k) _ _ (ρ j))
    (h : ∀ M, IsIso (map f M)) : IsIso f := by
  classical
  let inst (M : C) : IsIso (map f M) := h M
  let b := fun j i M => (inv (map f M)) j i
  have ha : ∀ i j, IsSupernatural k (ρ j)
      (F := (F.X i).toFunctor) (G := (G.X j).toFunctor) (fun M => (f i j).total M) := by
    intro i j
    have he : (fun M => (f i j).total M) = (f i j).app (ρ j) := by
      funext M
      exact HomogeneousSuperfunctorIso.total_eq_app _ (hf i j) M
    rw [he]
    exact (f i j).isSupernatural (ρ j)
  have hab : ∀ i i' M, ∑ j, (f i j).total M ≫ b j i' M =
      famDelta (fun i => (F.X i).toFunctor) i i' M := by
    intro i i' M
    exact congrFun (congrFun (IsIso.hom_inv_id (map f M)) i) i'
  have hba : ∀ j j' M, ∑ i, b j i M ≫ (f i j').total M =
      famDelta (fun j => (G.X j).toFunctor) j j' M := by
    intro j j' M
    exact congrFun (congrFun (IsIso.inv_hom_id (map f M)) j) j'
  let hb := isSupernatural_of_inverse_target (R := k) ρ
    (fun i j M => (f i j).total M) b ha hab hba
  let g : G ⟶ F := fun j i => (hb j i).toSuperNatTrans
  have hg : ∀ M, map g M = inv (map f M) := by
    intro M
    ext j i
    exact HomogeneousSuperfunctorIso.homogeneous_total (hb j i) M
  refine ⟨g, ?_, ?_⟩
  · apply map_ext
    intro M
    rw [map_comp, map_id, hg]
    exact IsIso.hom_inv_id _
  · apply map_ext
    intro M
    rw [map_comp, map_id, hg]
    exact IsIso.inv_hom_id _

/-- A matrix with source-indexed parity is invertible if every evaluated matrix is. -/
theorem isIso_of_components_source {F G : Mat_ (Superfunctor k C D)} (f : F ⟶ G) (ρ : F.ι → ZMod 2)
    (hf : ∀ i j, f i j ∈ parity (R := k) _ _ (ρ i))
    (h : ∀ M, IsIso (map f M)) : IsIso f := by
  classical
  let inst (M : C) : IsIso (map f M) := h M
  let b := fun j i M => (inv (map f M)) j i
  have ha : ∀ i j, IsSupernatural k (ρ i)
      (F := (F.X i).toFunctor) (G := (G.X j).toFunctor) (fun M => (f i j).total M) := by
    intro i j
    have he : (fun M => (f i j).total M) = (f i j).app (ρ i) := by
      funext M
      exact HomogeneousSuperfunctorIso.total_eq_app _ (hf i j) M
    rw [he]
    exact (f i j).isSupernatural (ρ i)
  have hab : ∀ i i' M, ∑ j, (f i j).total M ≫ b j i' M =
      famDelta (fun i => (F.X i).toFunctor) i i' M := by
    intro i i' M
    exact congrFun (congrFun (IsIso.hom_inv_id (map f M)) i) i'
  have hba : ∀ j j' M, ∑ i, b j i M ≫ (f i j').total M =
      famDelta (fun j => (G.X j).toFunctor) j j' M := by
    intro j j' M
    exact congrFun (congrFun (IsIso.inv_hom_id (map f M)) j) j'
  let hb := isSupernatural_of_inverse_source (R := k) ρ
    (fun i j M => (f i j).total M) b ha hab hba
  let g : G ⟶ F := fun j i => (hb j i).toSuperNatTrans
  have hg : ∀ M, map g M = inv (map f M) := by
    intro M
    ext j i
    exact HomogeneousSuperfunctorIso.homogeneous_total (hb j i) M
  refine ⟨g, ?_, ?_⟩
  · apply map_ext
    intro M
    rw [map_comp, map_id, hg]
    exact IsIso.hom_inv_id _
  · apply map_ext
    intro M
    rw [map_comp, map_id, hg]
    exact IsIso.inv_hom_id _

/-- In particular, pointwise inverses suffice for an entrywise even matrix. -/
theorem isIso_of_components {F G : Mat_ (Superfunctor k C D)} (f : F ⟶ G)
    (hf : ∀ i j, f i j ∈ parity (R := k) _ _ 0)
    (h : ∀ M, IsIso (map f M)) : IsIso f :=
  isIso_of_components_target f (fun _ => 0) hf h

end OddMath.QuiverHecke.SwappedAssembly.MatrixEvaluation
