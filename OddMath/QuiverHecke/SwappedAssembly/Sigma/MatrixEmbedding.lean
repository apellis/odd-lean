import OddMath.QuiverHecke.SwappedAssembly.Sigma.AugmentedMatrix

/-! # Padding a family matrix by zero summands

The two-sector central chart retains a zero corner when the corresponding
pure path is absent. This file supplies the explicit matrix isomorphism
which inserts these zero summands; it does not assume an augmented map
invertible.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory Classical
variable {C : Type*} [Category C] [Preadditive C]

/-- Insert a finite family into a larger family, in specified object charts. -/
def matrixEmbeddingHom (M N : Mat_ C) (e : N.ι ↪ M.ι)
    (E : ∀ j, M.X (e j) ≅ N.X j) : M ⟶ N :=
  fun i j => famId M.X i (e j) ≫ (E j).hom

/-- The reverse matrix deletes the inserted zero summands. -/
def matrixEmbeddingInv (M N : Mat_ C) (e : N.ι ↪ M.ι)
    (E : ∀ j, M.X (e j) ≅ N.X j) : N ⟶ M :=
  fun j i => (E j).inv ≫ famId M.X (e j) i

/-- A chart on the present summands, with zero objects at every missing
index, is an isomorphism of family matrices. -/
def matrixEmbeddingIso (M N : Mat_ C) (e : N.ι ↪ M.ι)
    (E : ∀ j, M.X (e j) ≅ N.X j)
    (hzero : ∀ i, (∀ j, e j ≠ i) → Limits.IsZero (M.X i)) : M ≅ N where
  hom := matrixEmbeddingHom M N e E
  inv := matrixEmbeddingInv M N e E
  hom_inv_id := by
    classical
    apply Mat_.hom_ext
    intro i k
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [Mat_.comp_apply]
      dsimp only [matrixEmbeddingHom, matrixEmbeddingInv]
      rw [Finset.sum_eq_single j]
      · simp only [famId_self, Category.id_comp, Iso.hom_inv_id_assoc]
        rfl
      · intro l _ hlj
        rw [famId_of_ne M.X (fun h => hlj (e.injective h).symm)]
        simp only [Limits.zero_comp]
      · simp
    · exact (hzero i (by simpa only [not_exists] using hi)).eq_of_src _ _
  inv_hom_id := by
    classical
    apply Mat_.hom_ext
    intro j k
    rw [Mat_.comp_apply]
    dsimp only [matrixEmbeddingHom, matrixEmbeddingInv]
    rw [Finset.sum_eq_single (e j)]
    · by_cases hjk : j = k
      · subst k
        simp only [famId_self, Category.id_comp, Category.comp_id, Iso.inv_hom_id]
        exact (Mat_.id_apply_self N j).symm
      · rw [famId_of_ne M.X (fun h => hjk (e.injective h))]
        simp only [Limits.comp_zero, Limits.zero_comp]
        exact (Mat_.id_apply_of_ne N j k hjk).symm
    · intro i _ hij
      rw [famId_of_ne M.X hij.symm]
      simp only [Limits.comp_zero, Limits.zero_comp]
    · simp

@[simp] theorem matrixEmbeddingIso_hom_apply (M N : Mat_ C) (e : N.ι ↪ M.ι)
    (E : ∀ j, M.X (e j) ≅ N.X j)
    (hzero : ∀ i, (∀ j, e j ≠ i) → Limits.IsZero (M.X i)) (i j) :
    (matrixEmbeddingIso M N e E hzero).hom i j =
      famId M.X i (e j) ≫ (E j).hom := rfl

@[simp] theorem matrixEmbeddingIso_inv_apply (M N : Mat_ C) (e : N.ι ↪ M.ι)
    (E : ∀ j, M.X (e j) ≅ N.X j)
    (hzero : ∀ i, (∀ j, e j ≠ i) → Limits.IsZero (M.X i)) (j i) :
    (matrixEmbeddingIso M N e E hzero).inv j i =
      (E j).inv ≫ famId M.X (e j) i := rfl

/-- In the inserted coordinates every entry of a map is its specified
source chart, the old entry, and the inverse target chart. -/
def matrixEmbeddingMap {M N M' N' : Mat_ C} (S : M ≅ N) (T : M' ≅ N')
    (f : N ⟶ N') : M ⟶ M' := S.hom ≫ f ≫ T.inv

/-- The literal coordinate square, without any invertibility assumption
on the map being charted. -/
theorem matrixEmbeddingMap_square {M N M' N' : Mat_ C} (S : M ≅ N) (T : M' ≅ N')
    (f : N ⟶ N') : S.hom ≫ f = matrixEmbeddingMap S T f ≫ T.hom := by
  simp [matrixEmbeddingMap, Category.assoc]

end OddMath.QuiverHecke.SwappedAssembly
