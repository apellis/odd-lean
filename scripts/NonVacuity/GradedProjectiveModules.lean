import OddMath

/-! # Graded projective modules and the graded Karoubi envelope (BE2 §11, (11.2))

On the datum of `OddMath.QuiverHecke.AlgebraExamples` over `ℚ`: the shifted row module of the
empty word is finitely generated and projective, so it lies in the essential image of the graded
super Karoubi envelope of the quiver Hecke supercategory, and the equivalence of (11.2) applies.
-/

noncomputable section
open CategoryTheory StringDiagrams OddMath.FiniteHomMatrix
open OddMath.QuiverHecke OddMath.QuiverHecke.AlgebraExamples

namespace NonVacuity.GradedProjectiveModules

/-- **BE2 (11.2)**: a shifted row module of `H` is in the image of the Karoubi envelope. -/
example : (gsKarFunctor ℚ (HGr datum scalars symmetrizer homogeneous)).essImage
    (GSMod.shift ((3 : ℤ), (1 : ZMod 2))
      (rowModule (k := ℚ) (obj := fun X : HGr datum scalars symmetrizer homogeneous => X)
        (hObj datum scalars symmetrizer homogeneous []))) :=
  (gsKarFunctor_essImage_iff _).2 ⟨GSMod.fg_rowModule _ _, GSMod.isProjective_rowModule _ _⟩

/-- **BE2 (11.2)**: the equivalence for `H`. -/
example : GSKar ℚ (HGr datum scalars symmetrizer homogeneous) ≌
    (gsKarFunctor ℚ (HGr datum scalars symmetrizer homogeneous)).EssImageSubcategory :=
  gsKarEquivEssImage ℚ _

end NonVacuity.GradedProjectiveModules
