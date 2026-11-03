import OddMath.QuiverHecke.SwappedAssembly.Supernatural.MatrixEvaluation
import Categorification.TwoRep.PiLinear

/-! # Finite matrix inversion over arbitrary products

Brundan–Ellis (1.13)–(1.14): invert a finite central matrix after each
output-content projection, then assemble its inverse on the full product.
The set of output blocks need not be finite. This combines with natural
matrix inverse lifting at the input-module and represented-word layers.
-/
noncomputable section
open CategoryTheory
namespace OddMath.QuiverHecke.SwappedAssembly.MatrixProductEvaluation
universe u v
variable {ι : Type v} (C : ι → Type u) [∀ a, Category.{v} (C a)]
  [∀ a, Preadditive (C a)]

/-- Project every matrix entry to the selected output coordinate. -/
def evaluation (a : ι) : Mat_ (∀ a, C a) ⥤ Mat_ (C a) :=
  (Pi.eval C a).mapMat_

/-- All output coordinates jointly detect the given finite matrix. -/
theorem map_ext {F G : Mat_ (∀ a, C a)} {f g : F ⟶ G}
    (h : ∀ a, (evaluation C a).map f = (evaluation C a).map g) : f = g := by
  apply Mat_.hom_ext
  intro i j
  funext a
  exact congrFun (congrFun (h a) i) j

/-- Coordinatewise inverses assemble without finite output support. -/
theorem isIso_of_components {F G : Mat_ (∀ a, C a)} (f : F ⟶ G)
    (h : ∀ a, IsIso ((evaluation C a).map f)) : IsIso f := by
  let inst (a : ι) : IsIso ((evaluation C a).map f) := h a
  let g : G ⟶ F := fun j i a => (inv ((evaluation C a).map f)) j i
  have hg (a : ι) : (evaluation C a).map g = inv ((evaluation C a).map f) := rfl
  refine ⟨g, ?_, ?_⟩
  · apply map_ext C
    intro a
    rw [CategoryTheory.Functor.map_comp, (evaluation C a).map_id, hg]
    exact IsIso.hom_inv_id _
  · apply map_ext C
    intro a
    rw [CategoryTheory.Functor.map_comp, (evaluation C a).map_id, hg]
    exact IsIso.inv_hom_id _

end OddMath.QuiverHecke.SwappedAssembly.MatrixProductEvaluation
