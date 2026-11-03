import OddMath.QuiverHecke.SwappedAssembly.Supernatural.MatrixProductEvaluation
import OddMath.QuiverHecke.CyclotomicAction.GlobalProduct

/-! # Matrix inversion at input, output and represented-word coordinates

Brundan–Ellis (1.13)–(1.14): the central matrix is a matrix of Hom
superfunctors into a product of module categories. Its inverses at each
input object, output block and represented word determine a whole natural
inverse. The forward matrix's prescribed parity forces inverse naturality
at both module layers; no faithfulness of a forgetful action is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.SwappedAssembly.MatrixNestedEvaluation
universe u v w
variable {k : Type u} [CommRing k] {ι : Type u}
  {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C] [Supercategory k C]
  (D : ι → Type u) [∀ a, Category.{u} (D a)] [∀ a, Preadditive (D a)]
  [∀ a, Linear k (D a)] [∀ a, Supercategory k (D a)]

/-- The literal three successive component evaluations of a natural matrix. -/
def component {F G : Mat_ (Superfunctor k C (∀ a, Superfunctor k (D a) (SVec k)))} (f : F ⟶ G)
    (M : C) (a : ι) (N : D a) :=
  MatrixEvaluation.map
    ((MatrixProductEvaluation.evaluation (fun a => Superfunctor k (D a) (SVec k)) a).map
      (MatrixEvaluation.map f M)) N

/-- Target-indexed parity and pointwise inverses give the whole natural inverse. -/
theorem isIso_of_components_target {F G : Mat_ (Superfunctor k C (∀ a, Superfunctor k (D a) (SVec k)))}
    (f : F ⟶ G) (ρ : G.ι → ZMod 2)
    (hf : ∀ i j, f i j ∈ parity (R := k) _ _ (ρ j))
    (h : ∀ M a N, IsIso (component D f M a N)) : IsIso f := by
  apply MatrixEvaluation.isIso_of_components_target f ρ hf
  intro M
  apply MatrixProductEvaluation.isIso_of_components
  intro a
  apply MatrixEvaluation.isIso_of_components_target (C := D a) (D := SVec k) _ (fun j => ρ j)
  · intro i j
    change (f i j).total M a ∈ parity (R := k) _ _ (ρ j)
    rw [HomogeneousSuperfunctorIso.total_eq_app _ (hf i j) M]
    exact (f i j).app_mem (ρ j) M a
  · exact h M a

/-- Source-indexed parity gives the other augmented-matrix orientation. -/
theorem isIso_of_components_source {F G : Mat_ (Superfunctor k C (∀ a, Superfunctor k (D a) (SVec k)))}
    (f : F ⟶ G) (ρ : F.ι → ZMod 2)
    (hf : ∀ i j, f i j ∈ parity (R := k) _ _ (ρ i))
    (h : ∀ M a N, IsIso (component D f M a N)) : IsIso f := by
  apply MatrixEvaluation.isIso_of_components_source f ρ hf
  intro M
  apply MatrixProductEvaluation.isIso_of_components
  intro a
  apply MatrixEvaluation.isIso_of_components_source (C := D a) (D := SVec k) _ (fun i => ρ i)
  · intro i j
    change (f i j).total M a ∈ parity (R := k) _ _ (ρ i)
    rw [HomogeneousSuperfunctorIso.total_eq_app _ (hf i j) M]
    exact (f i j).app_mem (ρ i) M a
  · exact h M a

end OddMath.QuiverHecke.SwappedAssembly.MatrixNestedEvaluation
