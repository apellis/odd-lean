import OddMath.QuiverHecke.CyclotomicAction.ContentBlocks
import OddMath.QuiverHecke.CyclotomicAction.SuperInduction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Content support of cyclotomic superinduction

The content blocks needed for BE2 §11 are full subcategories of the existing
cyclotomic supermodules. Their objects are modules on which the corresponding
central idempotent acts as the identity. Balanced-tensor induction adds its
colour to the content. This construction still has positive-height indexing.
-/

noncomputable section
open CategoryTheory StringDiagrams
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

/-- A supermodule supported on the specified content block. -/
def ContentSupported (n : ℕ) (β : Multiset I)
    (M : CyclotomicSupermodules D Sc a ha n) : Prop :=
  ∀ m : M.toSVec, M.lact (cyclotomicContentIdempotent D Sc a n β) m = m

/-- The full subcategory retains all even and odd module morphisms. -/
abbrev CyclotomicContentModules (n : ℕ) (β : Multiset I) :=
  ObjectProperty.FullSubcategory (ContentSupported D Sc a ha n β)

/-- On the induction corner, the target content projector equals the right
source projector. Both sides use the actual cyclotomic multiplication. -/
theorem inductionCorner_content (i : I) (n : ℕ) (β : Multiset I)
    (x : (inductionCorner D Sc i a ha n).toSVec) :
    (inductionCorner D Sc i a ha n).lact
        (cyclotomicContentIdempotent D Sc a (n + 1) ({i} + β)) x =
      (inductionCorner D Sc i a ha n).ract
        (cyclotomicContentIdempotent D Sc a n β) x := by
  apply Subtype.ext
  change cyclotomicContentIdempotent D Sc a (n + 1) ({i} + β) * x.1 =
    x.1 * cyclotomicAppend D Sc i a n (cyclotomicContentIdempotent D Sc a n β)
  have he := cyclotomicContentIdempotent_append D Sc i a n β 1
  rw [mul_one] at he
  rw [cyclotomicContentIdempotent_central, ← he]
  rw [cyclotomicContentIdempotent_central D Sc a (n + 1) ({i} + β)
    (cyclotomicAppend D Sc i a n 1), ← mul_assoc, x.2]

/-- Balanced-tensor superinduction carries content `β` to `{i} + β`. -/
theorem contentSupported_induction (i : I) (n : ℕ) (β : Multiset I)
    (M : CyclotomicSupermodules D Sc a ha n) (hM : ContentSupported D Sc a ha n β M) :
    ContentSupported D Sc a ha (n + 1) ({i} + β)
      ((cyclotomicSuperInduction D Sc i a ha n).obj M) := by
  intro z
  change (SuperBimodule.tensor (inductionCorner D Sc i a ha n) M).lact _ z = z
  induction z using SuperBimodule.tensor_induction_on with
  | zero => exact map_zero _
  | add x y hx hy => rw [map_add, hx, hy]
  | btmul x m =>
    rw [SuperBimodule.lact_btmul, inductionCorner_content,
      SuperBimodule.btmul_ract_lact, hM m]

/-- Restriction of the existing induction functor to its content blocks. -/
def cyclotomicContentInduction (i : I) (n : ℕ) (β : Multiset I) :
    CyclotomicContentModules D Sc a ha n β ⥤
      CyclotomicContentModules D Sc a ha (n + 1) ({i} + β) where
  obj M := ⟨(cyclotomicSuperInduction D Sc i a ha n).obj M.obj,
    contentSupported_induction D Sc a ha i n β M.obj M.property⟩
  map f := ⟨(cyclotomicSuperInduction D Sc i a ha n).map f.hom⟩
  map_id M := InducedCategory.hom_ext ((cyclotomicSuperInduction D Sc i a ha n).map_id M.obj)
  map_comp f g := InducedCategory.hom_ext
    ((cyclotomicSuperInduction D Sc i a ha n).map_comp f.hom g.hom)

end OddMath.QuiverHecke
