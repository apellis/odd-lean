import OddMath.QuiverHecke.SwappedAssembly.Sigma.MatrixEmbedding

/-! # Entries in zero-padded family coordinates

These finite-sum formulas identify the entries of the central augmented
matrix chart with their selected source and target component charts.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory Classical
variable {C : Type*} [Category C] [Preadditive C]

/-- Only the selected source summand contributes to a matrix product. -/
theorem matrixEmbeddingHom_comp_apply (M N K : Mat_ C) (e : N.ι ↪ M.ι)
    (E : ∀ j, M.X (e j) ≅ N.X j) (f : N ⟶ K) (j k) :
    (matrixEmbeddingHom M N e E ≫ f) (e j) k = (E j).hom ≫ f j k := by
  rw [Mat_.comp_apply]
  dsimp only [matrixEmbeddingHom]
  rw [Finset.sum_eq_single j]
  · simp only [famId_self, Category.id_comp]
  · intro l _ hlj
    rw [famId_of_ne M.X (fun h => hlj (e.injective h).symm)]
    simp only [Limits.zero_comp]
  · simp

/-- Only the selected target summand contributes to a matrix product. -/
theorem matrixEmbedding_comp_inv_apply (M N K : Mat_ C) (e : N.ι ↪ M.ι)
    (E : ∀ j, M.X (e j) ≅ N.X j) (f : K ⟶ N) (i j) :
    (f ≫ matrixEmbeddingInv M N e E) i (e j) = f i j ≫ (E j).inv := by
  rw [Mat_.comp_apply]
  dsimp only [matrixEmbeddingInv]
  rw [Finset.sum_eq_single j]
  · simp only [famId_self, Category.comp_id]
  · intro l _ hlj
    rw [famId_of_ne M.X (fun h => hlj (e.injective h))]
    simp only [Limits.comp_zero]
  · simp

/-- A present entry is exactly the selected source chart, the old entry,
and the inverse selected target chart. -/
theorem matrixEmbeddingMap_apply
    (M N M' N' : Mat_ C) (e : N.ι ↪ M.ι) (e' : N'.ι ↪ M'.ι)
    (E : ∀ j, M.X (e j) ≅ N.X j) (E' : ∀ j, M'.X (e' j) ≅ N'.X j)
    (hz : ∀ i, (∀ j, e j ≠ i) → Limits.IsZero (M.X i))
    (hz' : ∀ i, (∀ j, e' j ≠ i) → Limits.IsZero (M'.X i))
    (f : N ⟶ N') (j k) :
    (matrixEmbeddingMap (matrixEmbeddingIso M N e E hz)
      (matrixEmbeddingIso M' N' e' E' hz') f) (e j) (e' k) =
      (E j).hom ≫ f j k ≫ (E' k).inv := by
  unfold matrixEmbeddingMap
  rw [← Category.assoc]
  change ((matrixEmbeddingHom M N e E ≫ f) ≫
    matrixEmbeddingInv M' N' e' E') (e j) (e' k) = _
  rw [matrixEmbedding_comp_inv_apply, matrixEmbeddingHom_comp_apply]
  rw [Category.assoc]

end OddMath.QuiverHecke.SwappedAssembly
